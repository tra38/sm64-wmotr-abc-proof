(** Actual allocator choices. The graph callbacks' effects are NOT assumed
    harmless: this first result follows the saved receiver through them. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area1AllocationSource
  InkCopyCaller InkBackwardExecution InkFloorResetExecution InkBodyResetFrame
  ContactConsumerExecution ObjectContactNecessity SecretContactExecution
  EyerokRank15LiveMovement OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition pac_node := tptr (Tstruct PAS._ObjectNode noattr).
Definition pac_object := tptr (Tstruct PAS._Object noattr).
Definition pac_read id field := Efield
  (Ederef (Etempvar id pac_node) (Tstruct PAS._ObjectNode noattr)) field pac_node.
Definition pac_prefix version := match fn_body (pas_body version PATry) with
| Ssequence (Ssequence first _) _ => first | _ => Sskip end.
Definition pac_choice version := match fn_body (pas_body version PATry) with
| Ssequence (Ssequence _ choice) _ => choice | _ => Sskip end.
Definition pac_tail version := match fn_body (pas_body version PATry) with
| Ssequence _ tail => tail | _ => Sskip end.
Definition pac_graph_calls version := match pac_tail version with
| Ssequence remove (Ssequence add _) => Ssequence remove add | _ => Sskip end.
Definition pac_return := Sreturn (Some (Ecast (Etempvar PAS._nextObj pac_node) pac_object)).

Lemma pac_source_cuts : forall version,
 fn_vars (pas_body version PATry) = [] /\
 fn_params (pas_body version PATry) = [(PAS._destList,pac_node);(PAS._freeList,pac_node)] /\
 fn_body (pas_body version PATry) =
 Ssequence (Ssequence (pac_prefix version) (pac_choice version)) (pac_tail version) /\
 pac_prefix version = Ssequence
   (Ssequence (Sset PAS._t'5 (pac_read PAS._freeList PAS._next))
     (Sset PAS._t'1 (Ecast (Etempvar PAS._t'5 pac_node) pac_node)))
   (Sset PAS._nextObj (Etempvar PAS._t'1 pac_node)) /\
 ibk_normal (pac_prefix version) = true /\
 ifr_keeps_temp PAS._nextObj (pac_choice version) = true /\
 ibk_normal (pac_graph_calls version) = true /\
 ifr_keeps_temp PAS._nextObj (pac_graph_calls version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma pac_node_layout : forall version,
 ibcc_field_ok (Clight.globalenv (selected_clight_target version)) PAS._ObjectNode PAS._next 96 = true /\
 ibcc_field_ok (Clight.globalenv (selected_clight_target version)) PAS._ObjectNode PAS._prev 100 = true.
Proof.
 intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
 PAS._ObjectNode PAS._next 96 = true /\
 ibcc_field_ok (prog_comp_env (selected_clight_target version)) PAS._ObjectNode PAS._prev 100 = true).
 rewrite <- rank15_selected_header_environment_exact.
 destruct version; vm_compute; split; reflexivity.
Qed.

Lemma pac_read_field : forall version e le m id field delta b ofs value answer,
 le ! id = Some (Vptr b ofs) ->
 ibcc_field_ok (Clight.globalenv (selected_clight_target version)) PAS._ObjectNode field delta = true ->
 Mem.load Mint32 m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some value ->
 eval_expr (Clight.globalenv (selected_clight_target version)) e le m (pac_read id field) answer ->
 answer = value.
Proof.
 intros version e le m id field delta b ofs value answer Htemp Hfield Hload Hread.
 unfold pac_read in Hread.
 eapply ibr_field_read_value with (ty := pac_node) (chunk := Mint32); [exact Htemp|exact Hfield|reflexivity|exact Hload|exact Hread].
Qed.

Lemma pac_cast_pointer : forall ge e le m id from to b ofs answer,
 le ! id = Some (Vptr b ofs) ->
 eval_expr ge e le m (Ecast (Etempvar id (tptr from)) (tptr to)) answer ->
 answer = Vptr b ofs.
Proof.
 intros ge e le m id from to b ofs answer Htemp Hread.
 inversion Hread; subst.
 - match goal with Ht : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
     assert (v = Vptr b ofs) by (eapply ocn_temp_value; eauto); subst v end.
   match goal with Hcast : sem_cast _ _ _ _ = Some answer |- _ =>
     cbn in Hcast; congruence end.
 - match goal with Hl : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma pac_prefix_reads_head : forall version le m fb fo ob oo t le' after out,
 le ! PAS._freeList = Some (Vptr fb fo) ->
 Mem.load Mint32 m fb (Ptrofs.unsigned (Ptrofs.add fo (Ptrofs.repr 96))) = Some (Vptr ob oo) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (pac_prefix version) t le' after out ->
 after = m /\ le' ! PAS._nextObj = Some (Vptr ob oo) /\ le' ! PAS._t'1 = Some (Vptr ob oo).
Proof.
 intros version le m fb fo ob oo t le' after out Hfree Hhead Hrun.
 destruct (pac_source_cuts version) as (_ & _ & _ & Hprefix & _).
 rewrite Hprefix in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
 cce_unroll_loop_free_exec.
 match goal with Hr : eval_expr _ _ _ _ (pac_read _ _) ?v |- _ =>
   assert (v = Vptr ob oo) by (eapply pac_read_field; eauto; apply pac_node_layout); subst v end.
 match goal with Hr : eval_expr _ _ _ _ (Ecast _ _) ?v |- _ =>
   assert (v = Vptr ob oo) by (eapply pac_cast_pointer; eauto; apply PTree.gss); subst v end.
 match goal with Hr : eval_expr _ _ _ _ (Etempvar PAS._t'1 _) ?v |- _ =>
   assert (v = Vptr ob oo) by (eapply ocn_temp_value; eauto; apply PTree.gss); subst v end.
 split; [reflexivity|]. split; [apply PTree.gss|rewrite PTree.gso by discriminate; apply PTree.gss].
Qed.

Lemma pac_choice_return_is_zero : forall version le m t le' after value ty,
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (pac_choice version) t le' after (Out_return (Some (value,ty))) -> value = Vint Int.zero /\ ty = tptr tvoid.
Proof.
 intros version le m t le' after value ty Hrun.
 assert (exists guard yes, pac_choice version = Sifthenelse guard yes
    (Sreturn (Some (Ecast (Econst_int Int.zero tint) (tptr tvoid)))) /\ ibk_normal yes = true)
   as (guard & yes & Hshape & Hnormal) by (destruct version; do 2 eexists; split; reflexivity).
 rewrite Hshape in Hrun. inversion Hrun; subst. destruct b.
 - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ yes _ _ _ _ |- _ =>
     pose proof (ibk_normal_outcome _ _ _ _ _ _ _ _ _ Hnormal Hr); discriminate end.
 - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn _) _ _ _ _ |- _ =>
     inversion Hr; subst end.
   split; [eapply cce_cast_zero_value; eauto|reflexivity].
Qed.

Lemma pac_nonnull_node_test : forall ge e le m id b ofs,
 le ! id = Some (Vptr b ofs) ->
 ~ ocn_test_value ge e le m (Ebinop One (Etempvar id pac_node)
   (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint) false.
Proof.
 intros ge e le m id b ofs Hnode [answer [Hexpr Hbool]]. inversion Hexpr; subst.
 - match goal with Htemp : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
     assert (v = Vptr b ofs) by (eapply ocn_temp_value; eauto); subst v end.
   match goal with Hcast : eval_expr _ _ _ _ (Ecast _ _) _ |- _ =>
     apply cce_cast_zero_value in Hcast; subst end.
   match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some answer |- _ =>
     change (option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) Cne
       (Vptr b ofs) (Vint Int.zero)) = Some answer) in Hsem;
     cbn [Val.cmpu_bool] in Hsem;
     repeat match type of Hsem with context [if ?test then _ else _] =>
       destruct test eqn:?; cbn in Hsem; try discriminate end;
     inversion Hsem; subst; discriminate end.
 - match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma pac_nonempty_choice_finishes_normally : forall version le m ob oo t le' after out,
 le ! PAS._t'1 = Some (Vptr ob oo) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (pac_choice version) t le' after out -> out = Out_normal.
Proof.
 intros version le m ob oo t le' after out Hhead Hrun.
 assert (exists yes, pac_choice version = Sifthenelse
   (Ebinop One (Etempvar PAS._t'1 pac_node)
     (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint) yes
   (Sreturn (Some (Ecast (Econst_int Int.zero tint) (tptr tvoid)))) /\ ibk_normal yes = true)
   as (yes & E & Hnormal) by (destruct version; eexists; split; reflexivity).
 rewrite E in Hrun. inversion Hrun; subst. destruct b.
 - eapply ibk_normal_outcome; eauto.
 - exfalso; eapply pac_nonnull_node_test; [exact Hhead|]. unfold ocn_test_value; eauto.
Qed.

Lemma pac_tail_returns_saved_head : forall version le m ob oo t le' after out,
 le ! PAS._nextObj = Some (Vptr ob oo) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (pac_tail version) t le' after out ->
 out = Out_return (Some (Vptr ob oo,pac_object)).
Proof.
 intros version le m ob oo t le' after out Hhead Hrun.
 assert (exists remove add, pac_tail version = Ssequence remove (Ssequence add pac_return) /\
   ibk_normal remove = true /\ ibk_normal add = true /\
   ifr_keeps_temp PAS._nextObj remove = true /\ ifr_keeps_temp PAS._nextObj add = true)
   as (remove & add & Hshape & Hrn & Han & Hrk & Hak)
   by (destruct version; do 2 eexists; repeat split; reflexivity).
 rewrite Hshape in Hrun.
 destruct (ibk_split_sequence _ _ _ _ remove _ _ _ _ _ Hrn Hrun)
   as (ll & mm & tt & ts & Et & Hr & Hrest).
 destruct (ibk_split_sequence _ _ _ _ add _ _ _ _ _ Han Hrest)
   as (ll2 & mm2 & tt2 & ts2 & Et2 & Ha & Hreturn).
 assert (ll2 ! PAS._nextObj = Some (Vptr ob oo)) as Hsaved.
 { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Ha Hak).
   rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hr Hrk). exact Hhead. }
 inversion Hreturn; subst.
 match goal with Hv : eval_expr _ _ _ _ (Ecast _ _) ?v |- _ =>
   assert (v = Vptr ob oo) by (eapply pac_cast_pointer; eauto); subst v end.
 reflexivity.
Qed.

Theorem pac_try_body_result_origin : forall version le m fb fo ob oo t le' after value ty,
 le ! PAS._freeList = Some (Vptr fb fo) ->
 Mem.load Mint32 m fb (Ptrofs.unsigned (Ptrofs.add fo (Ptrofs.repr 96))) = Some (Vptr ob oo) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (fn_body (pas_body version PATry)) t le' after (Out_return (Some (value,ty))) ->
 value = Vptr ob oo /\ ty = pac_object.
Proof.
 intros version le m fb fo ob oo t le' after value ty Hfree Hhead Hrun.
 destruct (pac_source_cuts version) as (_ & _ & Hbody & _ & Hpn & Hkeep & _).
 rewrite Hbody in Hrun. inversion Hrun; subst.
 - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
     destruct (ibk_split_sequence _ _ _ _ (pac_prefix version) _ _ _ _ _ Hpn Hr)
       as (ll & mm & tt & ts & Et & Hp & Hc) end.
   destruct (pac_prefix_reads_head _ _ _ _ _ _ _ _ _ _ _ Hfree Hhead Hp) as [Em [Hl Ht1]].
   match goal with Htail : ClightBigstep.exec_stmt _ _ _ ?ll' _ (pac_tail version) _ _ _ _ |- _ =>
     assert (ll' ! PAS._nextObj = Some (Vptr ob oo)) by
       (rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hc Hkeep); exact Hl);
     pose proof (pac_tail_returns_saved_head _ _ _ _ _ _ _ _ _ H Htail) end.
   split; congruence.
 - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
     destruct (ibk_split_sequence _ _ _ _ (pac_prefix version) _ _ _ _ _ Hpn Hr)
       as (ll & mm & tt & ts & Et & Hp & Hc) end.
   destruct (pac_prefix_reads_head _ _ _ _ _ _ _ _ _ _ _ Hfree Hhead Hp) as [Em [Hl Ht1]].
   pose proof (pac_nonempty_choice_finishes_normally _ _ _ _ _ _ _ _ _ Ht1 Hc). discriminate.
Qed.

Theorem pac_try_call_result_origin : forall version m dest fb fo ob oo t after result,
 Mem.load Mint32 m fb (Ptrofs.unsigned (Ptrofs.add fo (Ptrofs.repr 96))) = Some (Vptr ob oo) ->
 ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
  m (Internal (pas_body version PATry)) [dest;Vptr fb fo] t after result ->
 result = Vptr ob oo.
Proof.
 intros version m dest fb fo ob oo t after result Hhead Hcall.
 destruct (pac_source_cuts version) as (Hvars & Hparams & _).
 inversion Hcall; subst.
 match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
 match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ => rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
 match goal with Hf : Mem.free_list ?m (blocks_of_env _ empty_env) = Some ?last |- _ =>
   change (Some m = Some last) in Hf; inversion Hf; subst end.
 match goal with Hb : bind_parameter_temps _ _ _ = Some ?le |- _ =>
   rewrite Hparams in Hb; cbn [bind_parameter_temps] in Hb; inversion Hb; subst le end.
 assert (fn_return (pas_body version PATry) = pac_object) as Hreturn by (destruct version; reflexivity).
 match goal with Ho : outcome_result_value ?out _ _ _ |- _ =>
   rewrite Hreturn in Ho; destruct out; cbn in Ho; try contradiction;
   match goal with o : option (val * type) |- _ =>
     destruct o as [[value ty]|]; cbn in Ho; try contradiction end end.
 match goal with Ho : _ /\ sem_cast _ _ _ _ = Some _ |- _ => destruct Ho as [_ Hcast] end.
 match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
   destruct (pac_try_body_result_origin _ _ _ _ _ _ _ _ _ _ _ _ ltac:(apply PTree.gss) Hhead Hr)
     as [Evalue Etype]; subst end.
 all: try reflexivity.
 all: match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
   destruct version; cbn in Hcast; inversion Hcast; auto end.
Qed.

(** Distinctness follows from actual unequal flag cells, not from the word
    'child'. Reaching these entry facts still needs free/active ownership. *)
Theorem pac_free_head_flags_exclude_mario : forall version m dest fb fo ob child mario flags t after result,
 Mem.load Mint32 m fb (Ptrofs.unsigned (Ptrofs.add fo (Ptrofs.repr 96))) =
   Some (Vptr ob (Ptrofs.repr (object_slot_offset child))) ->
 Mem.load Mint16signed m ob (object_slot_offset child + object_active_flags_offset) = Some (Vint Int.zero) ->
 Mem.load Mint16signed m ob (object_slot_offset mario + object_active_flags_offset) = Some (Vint flags) ->
 flags <> Int.zero ->
 ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
   m (Internal (pas_body version PATry)) [dest;Vptr fb fo] t after result ->
 child <> mario /\ result = Vptr ob (Ptrofs.repr (object_slot_offset child)).
Proof.
 intros. split; [intro E; subst; congruence|]. eapply pac_try_call_result_origin; eauto.
Qed.
