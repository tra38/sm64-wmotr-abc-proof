(** The actual last landing write: read depth, read timer, evaluate, store. *)
From Coq Require Import Bool Lia List Reals ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkLandingArithmetic InkBackwardExecution InkCopyCaller InkQuicksandSource
  InkQuicksandExpressions InkFloorResetExecution ContactConsumerExecution
  ObjectContactNecessity EyerokRank15LiveMovement JPBinary32DepthWrites SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma imb_control_fields : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IMB._MarioState IMB._actionTimer 26 = true /\
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IMB._MarioState IMB._input 2 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IMB._MarioState IMB._actionTimer 26 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IMB._MarioState IMB._input 2 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; split; reflexivity.
Qed.

Lemma imb_ushort_field_read : forall version e le m mb mo field offset value answer,
  le ! IMB._m = Some (Vptr mb mo) ->
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IMB._MarioState field offset = true ->
  Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr offset))) = Some value ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (Efield ibcc_state field tushort) answer -> answer = value.
Proof.
  intros version e le m mb mo field offset value answer Hm Hfield Hload Hread.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_state v -> v = Vptr mb mo) as Hbase by
    (intros; eapply ibcc_deref_struct; eauto).
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibcc_field_location _ _ _ _ ibcc_state IMB._MarioState field
      tushort _ _ _ _ _ _ eq_refl Hbase Hfield Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr offset))) =
      Some answer) in Hr; congruence end.
Qed.

Lemma imb_depth_location : forall version e le m mb mo b ofs bf,
  le ! IMB._m = Some (Vptr mb mo) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m iq_depth b ofs bf ->
  b = mb /\ ofs = Ptrofs.add mo (Ptrofs.repr 192) /\ bf = Full.
Proof.
  intros version e le m mb mo b ofs bf Hm Hl.
  eapply ibcc_field_location with (base := ibcc_state) (tag := IMB._MarioState)
    (field := IMB._quicksandDepth) (ty := tfloat) (delta := 192);
    [reflexivity| |exact (proj1 (iq_selected_fields version))|exact Hl].
  intros. eapply ibcc_deref_struct; eauto.
Qed.

Lemma imb_landing_expression_value : forall ge e le m depth timer answer,
  le ! IMB._t'3 = Some (Vsingle depth) -> le ! IMB._t'4 = Some (Vint timer) ->
  eval_expr ge e le m (Ebinop Oadd (Etempvar IMB._t'3 tfloat) imb_landing_delta tfloat) answer ->
  answer = Vsingle (Float32.add depth (imb_depth_delta timer)).
Proof.
  intros ge e le m depth timer answer Hd Htimer Hread.
  unfold imb_landing_delta in Hread.
  repeat match goal with
  | Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion Hr; subst; clear Hr
  end.
  all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end].
  all: repeat match goal with
  | Hr : eval_expr _ _ _ _ (Etempvar IMB._t'3 _) ?v |- _ =>
      assert (v = Vsingle depth) by (eapply ocn_temp_value; eauto); subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Etempvar IMB._t'4 _) ?v |- _ =>
      assert (v = Vint timer) by (eapply ocn_temp_value; eauto); subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hr; subst
  | Hr : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ => inversion Hr; subst; clear Hr
  end.
  all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion Hbad end].
  all: repeat match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    progress (cbn in Hsem; inversion Hsem; subst; clear Hsem) end.
  reflexivity.
Qed.

Theorem imb_landing_stage_exact_store :
  forall version e le m mb mo depth timer t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26))) = Some (Vint timer) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (imb_landing_write version) t le' m' out ->
  Mem.store Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192)))
    (Vsingle (Float32.add depth (imb_depth_delta timer))) = Some m' /\
  t = E0 /\ out = Out_normal.
Proof.
  intros version e le m mb mo depth timer t le' m' out Hm Hd Htimer Hrun.
  destruct (imb_source_cuts version) as (_ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ iq_depth ?v |- _ =>
    pose proof (iq_depth_read _ _ _ _ _ _ _ _ Hm Hd Hr) as Hvalue; subst v end.
  all: match goal with Hr : eval_expr _ _ ?temps _ imb_timer ?v |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as HmNow
      by (rewrite PTree.gso by discriminate; exact Hm);
    assert (v = Vint timer) by (eapply imb_ushort_field_read;
      [exact HmNow|exact (proj1 (imb_control_fields version))|exact Htimer|exact Hr]); subst v end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  lazymatch goal with Hl : eval_lvalue _ _ ?temps _ iq_depth _ _ _ |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as HmStore
      by (repeat rewrite PTree.gso by discriminate; exact Hm);
    destruct (imb_depth_location _ _ _ _ _ _ _ _ _ HmStore Hl) as (-> & -> & ->) end.
  lazymatch goal with Hr : eval_expr ?ge ?env ?temps ?memory (Ebinop Oadd _ _ _) ?v |- _ =>
    assert (v = Vsingle (Float32.add depth (imb_depth_delta timer))) as Hexpression by
      (eapply (imb_landing_expression_value ge env temps memory depth timer);
        [rewrite PTree.gso by discriminate; apply PTree.gss|apply PTree.gss|exact Hr]);
    inversion Hexpression; subst end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  split; [assumption|]. split; reflexivity.
Qed.

Definition InkFirstNegativeLandingCut : Prop :=
  forall version e le m mb mo depth timer t le' m' out after,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26))) = Some (Vint timer) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (imb_landing_write version) t le' m' out ->
  Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) ->
  JPBinary32FiniteNonnegative depth -> is_finite 24 128 after = true ->
  (B2R 24 128 after < 0)%R -> 4 <= Int.unsigned timer.

Theorem imb_actual_first_negative_landing_needs_late_timer : InkFirstNegativeLandingCut.
Proof.
  unfold InkFirstNegativeLandingCut.
  intros version e le m mb mo depth timer t le' m' out after Hm Hd Htimer Hrun Hafter Hnonnegative Hfinite Hnegative.
  destruct (imb_landing_stage_exact_store _ _ _ _ _ _ _ _ _ _ _ _ Hm Hd Htimer Hrun) as [Hstore _].
  rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore) in Hafter. inversion Hafter; subst.
  eapply imb_first_negative_landing_needs_timer_at_least_four; eauto.
Qed.
