(** Ordinary secret-trigger effects require the actual read-only pair query.
    Initialization from missing triggers is a distinct path, not a touch. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ContactConsumerSource
  ContactConsumerExecution ContactCreditExecution ObjectContactNecessity
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma sce_function_name_value : forall (ge : genv) e le m id args result cc function_block value,
  e ! id = None -> Genv.find_symbol ge id = Some function_block ->
  eval_expr ge e le m (Evar id (Tfunction args result cc)) value ->
  value = Vptr function_block Ptrofs.zero.
Proof.
  intros ge e le m id args result cc function_block value Hlocal Hsymbol Hexpr.
  inversion Hexpr; subst.
  match goal with Hlv : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ =>
    inversion Hlv; subst; try congruence end.
  match goal with Hfind : Genv.find_symbol _ _ = Some ?found |- _ =>
    assert (found = function_block) by congruence; subst found end.
  match goal with Hderef : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hderef; subst; try discriminate; reflexivity end.
Qed.

Definition sce_object_pointer := tptr (Tstruct CCB._Object noattr).
Definition sce_current_read := Evar CCB._gCurrentObject sce_object_pointer.
Definition sce_mario_read := Evar CCB._gMarioObject sce_object_pointer.
Definition sce_current_temp version := match version with
| VersionUS => CCB._t'8 | VersionJP => CCB._t'7 end.
Definition sce_mario_temp version := match version with
| VersionUS => CCB._t'9 | VersionJP => CCB._t'8 end.
Definition sce_query version := Scall (Some CCB._t'2)
  (Evar CCB._obj_check_if_collided_with_object
    (Tfunction [sce_object_pointer; sce_object_pointer] tint cc_default))
  [Etempvar (sce_current_temp version) sce_object_pointer;
   Etempvar (sce_mario_temp version) sce_object_pointer].
Definition sce_prefix version := Ssequence (Sset (sce_current_temp version) sce_current_read)
  (Ssequence (Sset (sce_mario_temp version) sce_mario_read) (sce_query version)).
Definition sce_guard := Ebinop Oeq (Etempvar CCB._t'2 tint)
  (Econst_int Int.one tint) tint.
Definition sce_effects version := match fn_body (ccs_body version CCSecret) with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.

Lemma sce_source_shape : forall version,
  fn_body (ccs_body version CCSecret) =
    Ssequence (sce_prefix version) (Sifthenelse sce_guard (sce_effects version) Sskip).
Proof. intros []; reflexivity. Qed.

Lemma sce_query_calls_selected_body : forall version e le m t le' m' out,
  e ! CCB._obj_check_if_collided_with_object = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (sce_query version) t le' m' out ->
  exists args result,
    eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
      [Etempvar (sce_current_temp version) sce_object_pointer;
       Etempvar (sce_mario_temp version) sce_object_pointer]
      [sce_object_pointer; sce_object_pointer] args /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ccs_body version CCPairSearch)) args E0 m result /\
    t = E0 /\ m' = m /\ out = Out_normal /\ le' = PTree.set CCB._t'2 result le.
Proof.
  intros version e le m t le' m' out Hlocal Hrun.
  destruct (ccs_selected_consumer_resolves version CCPairSearch)
    as (function_block & Hsymbol & Hfunction).
  unfold sce_query in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  match goal with Hexpr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr function_block Ptrofs.zero)
      by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
      function_block = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _
      (Internal (ccs_body _ _)) _ _ _ _ |- _ =>
    pose proof (cce_search_call_preserves_memory _ _ _ _ _ _ _
      (or_introl eq_refl) Hcall) as [Ht Hm]; subst end.
  eauto 9.
Qed.

Definition sce_query_locals version (le : temp_env) current mario :=
  PTree.set (sce_mario_temp version) mario
    (PTree.set (sce_current_temp version) current le).
Definition sce_effect_locals version le current mario :=
  PTree.set CCB._t'2 (Vint Int.one) (sce_query_locals version le current mario).

Lemma sce_object_cast_identity : forall value m cast_value,
  sem_cast value sce_object_pointer sce_object_pointer m = Some cast_value ->
  cast_value = value.
Proof.
  intros value m cast_value Hcast. unfold sce_object_pointer, tptr in Hcast.
  destruct value; cbn in Hcast; try congruence.
  all: destruct Archi.ptr64; congruence.
Qed.

Lemma sce_query_arguments : forall version ge e le m current mario args,
  eval_exprlist ge e (sce_query_locals version le current mario) m
    [Etempvar (sce_current_temp version) sce_object_pointer;
     Etempvar (sce_mario_temp version) sce_object_pointer]
    [sce_object_pointer; sce_object_pointer] args -> args = [current; mario].
Proof.
  intros version ge e le m current mario args Hargs.
  repeat match goal with Hlist : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Hlist; subst; clear Hlist end.
  repeat match goal with Hexpr : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ =>
    inversion Hexpr; subst; clear Hexpr end.
  all: try match goal with Hlv : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ =>
    inversion Hlv end.
  unfold sce_query_locals in *.
  repeat match goal with Hget : (PTree.set _ _ _) ! _ = Some _ |- _ =>
    first [rewrite PTree.gss in Hget |
      rewrite PTree.gso in Hget by (destruct version; discriminate)];
    try (inversion Hget; subst; clear Hget) end.
  repeat match goal with Hcast : sem_cast ?value _ _ _ = Some ?cast |- _ =>
    apply sce_object_cast_identity in Hcast; subst cast end.
  reflexivity.
Qed.

Lemma sce_prefix_has_exact_call : forall version e le m t le' m' out,
  e ! CCB._obj_check_if_collided_with_object = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (sce_prefix version) t le' m' out ->
  exists current mario result,
    eval_expr (Clight.globalenv (selected_clight_target version)) e le m
      sce_current_read current /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (PTree.set (sce_current_temp version) current le) m sce_mario_read mario /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ccs_body version CCPairSearch)) [current; mario] E0 m result /\
    (result = Vint Int.zero \/ result = Vint Int.one) /\
    t = E0 /\ m' = m /\ out = Out_normal /\
    le' = PTree.set CCB._t'2 result (sce_query_locals version le current mario).
Proof.
  intros version e le m t le' m' out Hlocal Hrun.
  unfold sce_prefix, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hquery : ClightBigstep.exec_stmt _ _ _ _ _ (sce_query _) _ _ _ _ |- _ =>
    destruct (sce_query_calls_selected_body _ _ _ _ _ _ _ _ Hlocal Hquery)
      as (args & result & Hargs & Hcall & Ht & Hm & Hout & Hle); subst end.
  all: try contradiction.
  match goal with
  | Hcurrent : eval_expr _ _ _ _ sce_current_read ?current,
    Hmario : eval_expr _ _ _ _ sce_mario_read ?mario |- _ =>
      assert (args = [current; mario]) by (eapply sce_query_arguments; exact Hargs);
      subst args; exists current, mario, result
  end.
  repeat split; try assumption; try reflexivity.
  eapply ccr_pair_call_returns_boolean; exact Hcall.
Qed.

Lemma sce_zero_cannot_pass_guard : forall ge e le m,
  le ! CCB._t'2 = Some (Vint Int.zero) ->
  ~ ocn_test_value ge e le m sce_guard true.
Proof.
  intros ge e le m Hzero [value [Hexpr Hbool]].
  unfold sce_guard in Hexpr. inversion Hexpr; subst.
  - match goal with Htemp : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hconst : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hconst; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some value |- _ =>
      change (Some (Vint Int.zero) = Some value) in Hsem; inversion Hsem; subst end.
    discriminate.
  - match goal with Hlv : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ =>
      inversion Hlv end.
Qed.

(** A failed query has no effects at all. Therefore every completed callback
    with a net memory change or an observable event has this SAME entry read,
    successful pair call, and subsequent effects execution. *)
Theorem sce_secret_effect_requires_successful_entry_query :
  forall version e le m t le' m' out,
  e ! CCB._obj_check_if_collided_with_object = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ccs_body version CCSecret)) t le' m' out ->
  (m' <> m \/ t <> E0) ->
  exists current mario,
    eval_expr (Clight.globalenv (selected_clight_target version)) e le m
      sce_current_read current /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (PTree.set (sce_current_temp version) current le) m sce_mario_read mario /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ccs_body version CCPairSearch)) [current; mario] E0 m (Vint Int.one) /\
    ocn_test_value (Clight.globalenv (selected_clight_target version)) e
      (sce_effect_locals version le current mario) m sce_guard true /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (sce_effect_locals version le current mario) m
      (sce_effects version) t le' m' out.
Proof.
  intros version e le m t le' m' out Hlocal Hrun Hchanged.
  rewrite sce_source_shape in Hrun. inversion Hrun; subst.
  all: match goal with Hprefix : ClightBigstep.exec_stmt _ _ _ _ _ (sce_prefix _) _ _ _ _ |- _ =>
    destruct (sce_prefix_has_exact_call _ _ _ _ _ _ _ _ Hlocal Hprefix)
      as (current & mario & result & Hcurrent & Hmario & Hcall & Hboolean & Ht & Hm & Hout & Hle);
    subst end.
  2: contradiction.
  match goal with Hbranch : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
    inversion Hbranch; subst end.
  destruct b; cbn beta iota in *.
  - assert (result = Vint Int.one) as Hyes.
    { destruct Hboolean as [Hno | Hyes]; [|assumption]. subst result.
      exfalso. eapply sce_zero_cannot_pass_guard; [apply PTree.gss |].
      unfold ocn_test_value; eauto. }
    subst result. exists current, mario.
    unfold sce_effect_locals. repeat split; try assumption.
    unfold ocn_test_value; eauto.
  - match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hskip; subst end. tauto.
Qed.

Definition sce_entry_pair_evidence version le m current mario : Prop :=
  eval_expr (Clight.globalenv (selected_clight_target version)) empty_env le m
    sce_current_read current /\
  eval_expr (Clight.globalenv (selected_clight_target version)) empty_env
    (PTree.set (sce_current_temp version) current le) m sce_mario_read mario /\
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ccs_body version CCPairSearch)) [current; mario] E0 m (Vint Int.one).

(** Function-entry allocation and return freeing are included here. No
    separate harmless outside-call specification is assumed for the query. *)
Theorem sce_secret_call_effect_requires_entry_pair :
  forall version args m t m' result,
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ccs_body version CCSecret)) args t m' result ->
  (m' <> m \/ t <> E0) ->
  exists le current mario, sce_entry_pair_evidence version le m current mario.
Proof.
  intros version args m t m' result Hcall Hchanged.
  assert (fn_vars (ccs_body version CCSecret) = []) as Hvars
    by (destruct version; reflexivity).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _
      (fn_body (ccs_body version CCSecret)) _ _ _ _ |- _ =>
    destruct (sce_secret_effect_requires_successful_entry_query
      version empty_env _ _ _ _ _ _ ltac:(reflexivity) Hbody Hchanged)
      as (current & mario & Hcurrent & Hmario & Hpair & _)
  end.
  unfold sce_entry_pair_evidence. eauto 7.
Qed.

Theorem sce_entry_pair_reads_recorded_mario :
  forall version le m current target offset,
  sce_entry_pair_evidence version le m current (Vptr target offset) ->
  exists il count,
    il ! CCH._obj1 = Some current /\
    il ! CCH._obj2 = Some (Vptr target offset) /\
    eval_expr (Clight.globalenv (selected_clight_target version)) empty_env il m
      cce_pair_count_expression count /\
    eval_expr (Clight.globalenv (selected_clight_target version)) empty_env
      (PTree.set CCH._t'2 count il) m cce_pair_entry_expression (Vptr target offset) /\
    ocn_test_value (Clight.globalenv (selected_clight_target version)) empty_env
      (PTree.set CCH._t'2 count il) m cce_pair_count_guard true.
Proof.
  intros version le m current target offset (_ & _ & Hcall).
  exact (proj2 (proj2 (ccr_pair_call_reads_requested_object _ _ _ _ _ _ _ Hcall))).
Qed.
