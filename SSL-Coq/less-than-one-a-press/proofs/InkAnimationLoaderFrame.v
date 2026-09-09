(** The real animation loader's own bookkeeping is separate from MarioState.
    The transfer effect is explicit: it is not supplied by the name dma_read. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkLateHelperSource InkLateWriteFrame InkLateCallExecution
  InkAnimationDestination InkLandingHistoryGate InkCopyCaller InkControllerEdge
  ContactConsumerExecution EyerokRank15LiveMovement ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition ial_transfer_type := Tfunction [tptr tuchar; tptr tuchar; tptr tuchar] tvoid cc_default.
Definition ial_bookkeeping lhs := match iad_write_root lhs with
| Some id => Pos.eqb id us_memory._list | None => false end.
Definition ial_transfer fn (_ : list expr) := ilh_named us_memory._dma_read ial_transfer_type fn.
Definition ial_transfer_call := Scall None
  (Evar us_memory._dma_read ial_transfer_type)
  [Etempvar us_memory._t'3 (tptr tvoid); Etempvar us_memory._addr (tptr tuchar);
   Ebinop Oadd (Etempvar us_memory._addr (tptr tuchar))
     (Etempvar us_memory._size tint) (tptr tuchar)].

Theorem ial_real_loader_shape : forall version,
  ilw_shape [us_memory._list] ial_bookkeeping ial_transfer
    (fn_body (ill_body version ILLoad)) = true.
Proof. intros []; vm_compute; reflexivity. Qed.

Definition InkAnimationTransferTimerEffect version mb mo : Prop :=
  forall le m ab ao t le' m' out,
  le ! us_memory._t'3 = Some (Vptr ab ao) -> ab <> mb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    ial_transfer_call t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.

Definition InkAnimationLoaderCheckedFrame : Prop := forall version mb mo,
  InkAnimationTransferTimerEffect version mb mo ->
  forall m lb lo ab ao args t m' result, lb <> mb -> ab <> mb ->
  Mem.load Mint32 m lb (Ptrofs.unsigned (Ptrofs.add lo (Ptrofs.repr 8))) = Some (Vptr ab ao) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version ILLoad)) (Vptr lb lo :: args) t m' result ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.

Theorem ial_actual_loader_preserves_timer : InkAnimationLoaderCheckedFrame.
Proof.
  intros version mb mo Htransfer m lb lo ab ao args t m' result Hother HbufferOther Hbuffer Hcall.
  destruct (ilh_actual_helper_entry version ILLoad m lb lo args t m' result Hcall)
    as (entry_le & final_le & out & Hlist & Hbody).
  assert (ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    us_memory._DmaHandlerList us_memory._bufTarget 8 = true) as Hfield.
  { change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
      us_memory._DmaHandlerList us_memory._bufTarget 8 = true).
    rewrite <- rank15_selected_header_environment_exact. destruct version; vm_compute; reflexivity. }
  assert (fn_body (ill_body version ILLoad) = fn_body us_memory.f_load_patchable_table) as Hsource
    by (destruct version; reflexivity).
  rewrite Hsource in Hbody.
  cbv [fn_body us_memory.f_load_patchable_table] in Hbody.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hbody.
  cce_unroll_loop_free_exec.
  all: try solve [match goal with
    | Hbad : ?outcome <> Out_normal,
      Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ ?outcome |- _ =>
        inversion Hr; subst; contradiction
    | Hbad : ?outcome <> Out_normal,
      Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ ?outcome |- _ =>
        inversion Hr; subst; contradiction end].
  all: try reflexivity.
  lazymatch goal with Hr : eval_expr _ _ ?temps _ (Efield _ us_memory._bufTarget _) ?value |- _ =>
    assert (temps ! us_memory._list = Some (Vptr lb lo)) as HoriginalList
      by (repeat rewrite PTree.gso by discriminate; exact Hlist);
    assert (value = Vptr ab ao) by (eapply ice_field_read with (ty := tptr tvoid);
      [exact HoriginalList|exact Hfield|reflexivity|exact Hbuffer|exact Hr]); subst value end.
  lazymatch goal with Hr : ClightBigstep.exec_stmt _ _ _ ?temps ?memory (Scall _ _ _) ?tr ?temps' ?memory' ?outcome |- _ =>
    assert (ilh_timer_load memory' mb mo = ilh_timer_load memory mb mo) as HtransferFrame
      by (eapply (Htransfer temps memory ab ao tr temps' memory' outcome);
        [apply PTree.gss|exact HbufferOther|exact Hr]);
    inversion Hr; subst; clear Hr end.
  lazymatch goal with Hr : ClightBigstep.exec_stmt _ _ _ ?temps ?memory (Sassign ?lhs ?rhs) ?tr ?temps' ?memory' ?outcome |- _ =>
    assert (temps ! us_memory._list = Some (Vptr lb lo)) as HwriteList
      by (cbn [set_opttemp]; repeat rewrite PTree.gso by discriminate; exact Hlist);
    pose proof (iad_other_block_assignment _ _ temps memory lhs rhs us_memory._list lb lo mb mo
      tr temps' memory' outcome eq_refl HwriteList Hother Hr) as HwriteFrame end.
  congruence.
Qed.
