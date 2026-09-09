(** A completed loader returning zero did not transfer an animation. This
    covers both a cache hit and the index-rejection branch of the real code. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkLateHelperSource InkLateCallExecution InkAnimationTimerFrame
  ObjectContactNecessity ContactConsumerExecution SecretContactExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition InkAnimationNoTransferNoEffect : Prop :=
  forall version m args t m',
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version ILLoad)) args t m' (Vint Int.zero) ->
  t = E0 /\ m' = m.

Theorem ian_zero_loader_result_has_no_effect : InkAnimationNoTransferNoEffect.
Proof.
  intros version m args t m' Hcall.
  destruct (ill_empty_locals_and_original_argument version ILLoad) as [Hvars _].
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  assert (fn_body (ill_body version ILLoad) = fn_body us_memory.f_load_patchable_table) as Hsource
    by (destruct version; reflexivity).
  assert (fn_return (ill_body version ILLoad) = tint) as Hreturn by (destruct version; reflexivity).
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hsource in Hr; cbv [fn_body us_memory.f_load_patchable_table] in Hr end.
  match goal with Hresult : outcome_result_value _ (fn_return _) _ _ |- _ =>
    rewrite Hreturn in Hresult end.
  cce_unroll_loop_free_exec.
  all: try solve [match goal with
    | Hbad : ?outcome <> Out_normal,
      Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ ?outcome |- _ =>
        inversion Hr; subst; contradiction
    | Hbad : ?outcome <> Out_normal,
      Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ ?outcome |- _ =>
        inversion Hr; subst; contradiction end].
  all: try (split; reflexivity).
  all: repeat match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  all: lazymatch goal with Hr : eval_expr _ _ _ _ (Etempvar us_memory._ret _) ?v |- _ =>
    assert (v = Vint Int.one) by (eapply ocn_temp_value; [exact Hr|
      repeat rewrite PTree.gso by discriminate; apply PTree.gss]); subst v end.
  all: lazymatch goal with Hresult : outcome_result_value _ _ _ _ |- _ =>
    destruct Hresult as [_ Hcast];
    change (Some (Vint Int.one) = Some (Vint Int.zero)) in Hcast; discriminate end.
Qed.

(** This is the actual callsite in set_mario_animation, including the returned
    temporary. No assumption about the requested transfer destination is used. *)
Corollary ian_zero_animation_load_call_has_no_effect :
  forall version le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    iaf_load_call t le' m' out ->
  le' ! IBM._t'1 = Some (Vint Int.zero) -> t = E0 /\ m' = m.
Proof.
  intros version le m t le' m' out Hrun Hzero.
  unfold iaf_load_call in Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (ill_selected_helpers_resolve version ILLoad) as (fb & Hsymbol & Hfunction).
  lazymatch goal with Hr : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (eapply (sce_function_name_value _ empty_env le m _ _ _ _ fb vf);
        [reflexivity|exact Hsymbol|exact Hr]); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  cbn [set_opttemp] in Hzero. rewrite PTree.gss in Hzero. inversion Hzero; subst.
  eapply ian_zero_loader_result_has_no_effect; eassumption.
Qed.
