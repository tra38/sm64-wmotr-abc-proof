(** The initialized particle slot is also the returned slot. This connects
    the same-pool frame to the allocator's actual return, without assuming
    that graph/list maintenance or eviction preserved memory. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop Ctypes
 Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area1SlotExpressions
 Area1SlotWriteCheck Area1AllocationSource Area1AllocationInitialization
 Area1AllocationSlotFrame Area1AllocationChoice Area1AllocationCallback
 InkBackwardExecution InkFloorResetExecution ObjectContactNecessity
 SecretContactExecution ContactConsumerExecution OrdinaryArea1EntryMemory
 SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Fixpoint asr_returns id ty s := match s with
| Sreturn (Some (Etempvar j t)) => Pos.eqb id j && (if type_eq ty t then true else false)
| Sreturn _ => false
| Ssequence a b | Sifthenelse _ a b | Sloop a b => asr_returns id ty a && asr_returns id ty b
| Sswitch _ _ | Slabel _ _ | Sgoto _ => false
| _ => true end.

Lemma asr_return_temp_value : forall ge e le m s t le' after out,
 ocn_exec ge e le m s t le' after out ->
 forall id ty, asr_returns id ty s = true ->
 forall v, out = Out_return v -> exists value, v = Some (value,ty) /\ le' ! id = Some value.
Proof.
 intros ge e le m s t le' after out Hrun.
 induction Hrun; intros keep retty Hshape returned Eout;
  cbn [asr_returns] in Hshape; try discriminate.
 - apply andb_true_iff in Hshape as [Ha Hb]. eapply IHHrun2; eauto.
 - apply andb_true_iff in Hshape as [Ha Hb]. eapply IHHrun; eauto.
 - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; eapply IHHrun; eauto.
 - destruct a; try discriminate. apply andb_true_iff in Hshape as [Hid Htype].
   apply Pos.eqb_eq in Hid; subst i.
   match type of Htype with context [if type_eq ?a ?b then _ else _] =>
     destruct (type_eq a b); try discriminate; subst end.
   inversion Eout; subst. exists v. split; [reflexivity|].
   inversion H; subst; try assumption.
   match goal with Hl : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion Hl end.
 - apply andb_true_iff in Hshape as [Ha Hb].
   match goal with Hexit : out_break_or_return _ _ |- _ => inversion Hexit; subst; try discriminate end.
   eapply IHHrun; eauto.
 - apply andb_true_iff in Hshape as [Ha Hb].
   match goal with Hexit : out_break_or_return _ _ |- _ => inversion Hexit; subst; try discriminate end.
   eapply IHHrun2; eauto.
 - apply andb_true_iff in Hshape as [Ha Hb]. eapply IHHrun3; eauto.
   cbn [asr_returns]; rewrite Ha,Hb; reflexivity.
Qed.

Lemma asr_global_address : forall (ge : genv) e le m id ty fb answer,
 e ! id = None -> Genv.find_symbol ge id = Some fb ->
 eval_expr ge e le m (Eaddrof (Evar id ty) (tptr ty)) answer ->
 answer = Vptr fb Ptrofs.zero.
Proof.
 intros ge e le m id ty fb answer Hlocal Hsymbol Hread.
 inversion Hread; subst.
 - match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl; subst; congruence end.
 - match goal with Hl : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma asr_allocate_prefix_saves_head : forall version le m fb ob oo t le' after out,
 Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PAS._gFreeObjectList = Some fb ->
 Mem.load Mint32 m fb 96 = Some (Vptr ob oo) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (paf_allocate_prefix version) t le' after out ->
 le' ! PAS._obj = Some (Vptr ob oo).
Proof.
 intros version le m fb ob oo t le' after out Hsymbol Hhead Hrun.
 assert (paf_allocate_prefix version = paf_allocate_prefix VersionUS) as E by (destruct version; reflexivity).
 rewrite E in Hrun. cbv [paf_allocate_prefix pas_body PAS.f_allocate_object fn_body] in Hrun.
 unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun. cce_unroll_loop_free_exec.
 all: match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ _ |- _ => inversion Hcall; subst; try contradiction end.
 match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
 destruct (pas_selected_helpers_resolve version PATry) as (fnblock & Hfn & Hfun).
 match goal with Hr : eval_expr ?ge ?e ?le ?m (Evar ?id (Tfunction ?ps ?r ?cc)) ?v |- _ =>
   assert (v = Vptr fnblock Ptrofs.zero) by
     (eapply sce_function_name_value; [apply PTree.gempty|exact Hfn|exact Hr]); subst v end.
 match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
   change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fnblock = Some fd) in Hfind;
   rewrite Hfun in Hfind; inversion Hfind; subst fd end.
 repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
 match goal with Hr : eval_expr _ _ _ _ (Eaddrof _ _) ?v |- _ =>
   assert (v = Vptr fb Ptrofs.zero) by (eapply asr_global_address; eauto; apply PTree.gempty); subst v end.
 match goal with Hcast : sem_cast (Vptr fb _) _ _ _ = Some ?v |- _ =>
   change (Some (Vptr fb Ptrofs.zero) = Some v) in Hcast; inversion Hcast; subst v end.
 match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ ?result |- _ =>
   assert (result = Vptr ob oo) as Ereturn by
     (eapply (pac_try_call_result_origin version m _ fb Ptrofs.zero ob oo); [exact Hhead|exact Hcall]);
   subst result end.
 match goal with Hr : eval_expr _ _ _ _ (Etempvar PAS._t'1 _) ?v |- _ =>
   assert (v = Vptr ob oo) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst v end.
 apply PTree.gss.
Qed.

Lemma asr_nonnull_skips_eviction : forall version le m ob oo t le' after out,
 le ! PAS._obj = Some (Vptr ob oo) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (paf_allocate_choice version) t le' after out ->
 t = E0 /\ le' = le /\ after = m /\ out = Out_normal.
Proof.
 intros version le m ob oo t le' after out Hobj Hrun.
 assert (exists yes, paf_allocate_choice version = Sifthenelse
   (Ebinop Oeq (Etempvar PAS._obj pac_object)
     (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint) yes Sskip)
   as (yes & E) by (destruct version; eexists; reflexivity).
 rewrite E in Hrun. inversion Hrun; subst. destruct b.
 - exfalso.
   match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion Hr; subst end.
   + match goal with Hr : eval_expr _ _ _ _ (Etempvar PAS._obj _) ?v |- _ =>
       assert (v = Vptr ob oo) by (eapply ocn_temp_value; eauto); subst v end.
     match goal with Hr : eval_expr _ _ _ _ (Ecast _ _) _ |- _ => apply cce_cast_zero_value in Hr; subst end.
     match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some ?answer |- _ =>
       change (option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) Ceq
         (Vptr ob oo) (Vint Int.zero)) = Some answer) in Hsem;
       cbn [Val.cmpu_bool] in Hsem;
       repeat match type of Hsem with context [if ?test then _ else _] =>
         destruct test eqn:?; cbn in Hsem; try discriminate end;
       inversion Hsem; subst; discriminate end.
   + match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
 - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion Hr; subst end.
   repeat split; reflexivity.
Qed.

Theorem asr_initializer_frames_and_returns_same_slot : forall version le m ob slot t le' after out,
 (slot < object_pool_capacity)%nat ->
 le ! PAS._obj = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (pai_initializer version) t le' after out ->
 asw_frame ob slot m after /\
 out = Out_return (Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)),pac_object)).
Proof.
 intros version le m ob slot t le' after out Hslot Hobj Hrun.
 destruct (asf_initializer_checked version) as (last & Hcheck & Hfinal).
 assert (ase_context ob (Ptrofs.repr (object_slot_offset slot)) asf_initial_env le) as Hctx.
 { intros id x Hget. cbn [asf_initial_env ase_get] in Hget.
   destruct (Pos.eqb id PAS._obj) eqn:E; try discriminate.
   apply Pos.eqb_eq in E; subst. inversion Hget; subst.
   cbn [ase_denote]. rewrite Ptrofs.add_zero. exact Hobj. }
 destruct (asw_check_sound _ _ ob slot _ Hslot
   ltac:(intros; eapply asf_matrix_reached_frame; eauto)
   _ _ _ _ _ _ _ Hrun 150 asf_initial_env last ASWreturn Hcheck Hctx)
   as (Hframe & Hctx' & [value Eout]).
 split; [exact Hframe|].
 assert (asr_returns PAS._obj pac_object (pai_initializer version) = true) as Hshape
   by (destruct version; reflexivity).
 destruct (asr_return_temp_value _ _ _ _ _ _ _ _ _ Hrun _ _ Hshape _ Eout)
   as (result & Eresult & Hread).
 specialize (Hctx' _ _ Hfinal). cbn [ase_denote] in Hctx'.
 rewrite Ptrofs.add_zero in Hctx'. rewrite Eout,Eresult. f_equal. f_equal. congruence.
Qed.

Theorem asr_nonempty_allocator_body_connection : forall version le m fb ob slot t le' after out,
 (slot < object_pool_capacity)%nat ->
 Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PAS._gFreeObjectList = Some fb ->
 Mem.load Mint32 m fb 96 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (fn_body (pas_body version PAAllocate)) t le' after out ->
 exists init_le init_m pre suffix,
 t = pre ++ suffix /\
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (paf_allocate_prefix version) pre init_le init_m Out_normal /\
 init_le ! PAS._obj = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) /\
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env init_le init_m
   (pai_initializer version) suffix le' after out /\
 asw_frame ob slot init_m after /\
 out = Out_return (Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)),pac_object)).
Proof.
 intros version le m fb ob slot t le' after out Hslot Hfree Hhead Hrun.
 assert (fn_body (pas_body version PAAllocate) = Ssequence (paf_allocate_prefix version)
   (Ssequence (paf_allocate_choice version) (pai_initializer version))) as Hbody
   by (destruct version; reflexivity).
 assert (ibk_normal (paf_allocate_prefix version) = true) as Hnormal by (destruct version; reflexivity).
 rewrite Hbody in Hrun.
 destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
   as (ll & mm & pre & rest & Et & Hprefix & Hrest).
 pose proof (asr_allocate_prefix_saves_head _ _ _ _ _ _ _ _ _ _ Hfree Hhead Hprefix) as Hsaved.
 inversion Hrest; subst.
 - match goal with Hchoice : ClightBigstep.exec_stmt _ _ _ _ _ (paf_allocate_choice _) _ _ _ _ |- _ =>
     destruct (asr_nonnull_skips_eviction _ _ _ _ _ _ _ _ _ Hsaved Hchoice)
       as (-> & Etemps & Emem & _); subst end.
   match goal with Hinit : ClightBigstep.exec_stmt _ _ _ _ _ (pai_initializer _) ?suf _ _ _ |- _ =>
     exists ll,mm,pre,suf;
     pose proof (asr_initializer_frames_and_returns_same_slot _ _ _ _ _ _ _ _ _ Hslot Hsaved Hinit)
       as [Hframe Hreturn] end.
   repeat split; auto.
 - match goal with Hchoice : ClightBigstep.exec_stmt _ _ _ _ _ (paf_allocate_choice _) _ _ _ _ |- _ =>
     destruct (asr_nonnull_skips_eviction _ _ _ _ _ _ _ _ _ Hsaved Hchoice)
       as (_ & _ & _ & Eout); contradiction end.
Qed.

Theorem asr_nonempty_allocate_call_returns_head : forall version m dest fb ob slot t after result,
 (slot < object_pool_capacity)%nat ->
 Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PAS._gFreeObjectList = Some fb ->
 Mem.load Mint32 m fb 96 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
 ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
   m (Internal (pas_body version PAAllocate)) [dest] t after result ->
 result = Vptr ob (Ptrofs.repr (object_slot_offset slot)).
Proof.
 intros version m dest fb ob slot t after result Hslot Hfree Hhead Hcall.
 assert (fn_vars (pas_body version PAAllocate) = []) as Hvars by (destruct version; reflexivity).
 inversion Hcall; subst.
 match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
 match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ => rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
 match goal with Hf : Mem.free_list ?m (blocks_of_env _ empty_env) = Some ?last |- _ =>
   change (Some m = Some last) in Hf; inversion Hf; subst end.
 match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
   destruct (asr_nonempty_allocator_body_connection _ _ _ _ _ _ _ _ _ _ Hslot Hfree Hhead Hr)
     as (il & im & pre & suf & _ & _ & _ & _ & _ & Eout); subst end.
 assert (fn_return (pas_body version PAAllocate) = pac_object) as Hreturn by (destruct version; reflexivity).
 match goal with Ho : outcome_result_value _ _ _ _ |- _ =>
   rewrite Hreturn in Ho; cbn [outcome_result_value] in Ho; destruct Ho as [_ Hcast];
   change (Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) = Some result) in Hcast; congruence end.
Qed.

Theorem asr_nonempty_allocation_excludes_active_mario : forall version m dest fb ob slot mario flags t after result,
 (slot < object_pool_capacity)%nat ->
 Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PAS._gFreeObjectList = Some fb ->
 Mem.load Mint32 m fb 96 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
 Mem.load Mint16signed m ob (object_slot_offset slot + object_active_flags_offset) = Some (Vint Int.zero) ->
 Mem.load Mint16signed m ob (object_slot_offset mario + object_active_flags_offset) = Some (Vint flags) ->
 flags <> Int.zero ->
 ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
   m (Internal (pas_body version PAAllocate)) [dest] t after result ->
 slot <> mario /\ result = Vptr ob (Ptrofs.repr (object_slot_offset slot)).
Proof.
 intros. split; [intro E; subst; congruence|].
 eapply asr_nonempty_allocate_call_returns_head; eauto.
Qed.

Record Area1AllocationSlotCheckedBoundary : Prop := {
 asr_allocator_pieces : Area1PostCopyAllocationCheckedBoundary;
 asr_real_nonempty_return : forall version m dest fb ob slot t after result,
   (slot < object_pool_capacity)%nat ->
   Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PAS._gFreeObjectList = Some fb ->
   Mem.load Mint32 m fb 96 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
   ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
     m (Internal (pas_body version PAAllocate)) [dest] t after result ->
   result = Vptr ob (Ptrofs.repr (object_slot_offset slot));
 asr_real_entry_flags_exclude_mario : forall version m dest fb ob slot mario flags t after result,
   (slot < object_pool_capacity)%nat ->
   Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PAS._gFreeObjectList = Some fb ->
   Mem.load Mint32 m fb 96 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
   Mem.load Mint16signed m ob (object_slot_offset slot + object_active_flags_offset) = Some (Vint Int.zero) ->
   Mem.load Mint16signed m ob (object_slot_offset mario + object_active_flags_offset) = Some (Vint flags) ->
   flags <> Int.zero ->
   ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
     m (Internal (pas_body version PAAllocate)) [dest] t after result ->
   slot <> mario /\ result = Vptr ob (Ptrofs.repr (object_slot_offset slot))
}.
Theorem area1_allocation_slot_checked_boundary_holds : Area1AllocationSlotCheckedBoundary.
Proof.
 constructor.
 - exact area1_postcopy_allocation_checked_boundary_holds.
 - exact asr_nonempty_allocate_call_returns_head.
 - exact asr_nonempty_allocation_excludes_active_mario.
Qed.
