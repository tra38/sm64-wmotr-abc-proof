(** The real crouch-slide long-jump guard reads the A-pressed bit from memory.
    Controller-to-input provenance and all other action entries remain separate. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkLandingExecution InkBackwardExecution InkCopyCaller ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma imb_a_test_value : forall ge e le m flags answer,
  le ! IMB._t'13 = Some (Vint flags) ->
  eval_expr ge e le m (Ebinop Oand (Etempvar IMB._t'13 tushort)
    (Econst_int (Int.repr 2) tint) tint) answer ->
  answer = Vint (Int.and flags (Int.repr 2)).
Proof.
  intros ge e le m flags answer Hflags Hread. inversion Hread; subst.
  - match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vint flags) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hr; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some answer |- _ =>
      cbn in Hsem; inversion Hsem; reflexivity end.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Definition InkCrouchGuardNoA : Prop :=
  forall version e le m mb mo flags t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 2))) = Some (Vint flags) ->
  Int.and flags (Int.repr 2) = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (imb_crouch_a_guard version) t le' m' out ->
  t = E0 /\ m' = m /\ out = Out_normal.

Theorem imb_actual_crouch_a_guard_skips_without_pressed_bit : InkCrouchGuardNoA.
Proof.
  unfold InkCrouchGuardNoA.
  intros version e le m mb mo flags t le' m' out Hm Hload Hclear Hrun.
  destruct (imb_source_cuts version) as (_ & _ & _ & _ & Hshape).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IMB._t'13 imb_input) _ _ _ _ _ eq_refl Hrun)
    as (guard_le & guard_m & pre & rest & Htrace & Hread & Hbranch).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ imb_input ?v |- _ =>
    assert (v = Vint flags) by (eapply imb_ushort_field_read;
      [exact Hm|exact (proj2 (imb_control_fields version))|exact Hload|exact Hr]); subst v end.
  inversion Hbranch; subst.
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Ebinop Oand _ _ _) ?v |- _ =>
    assert (v = Vint (Int.and flags (Int.repr 2))) as Hvalue by
      (eapply (imb_a_test_value ge env temps memory flags); [apply PTree.gss|exact Hr]);
    subst v end.
  match goal with Hb : bool_val (Vint (Int.and _ _)) _ _ = Some ?choice |- _ =>
    rewrite Hclear in Hb; change (Some false = Some choice) in Hb; inversion Hb; subst end.
  match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
    inversion Hskip; subst end.
  repeat split; reflexivity.
Qed.

Corollary imb_actual_long_jump_guard_return_requires_pressed_bit :
  forall version e le m mb mo flags t le' m' answer,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 2))) = Some (Vint flags) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (imb_crouch_a_guard version) t le' m' (Out_return answer) ->
  Int.and flags (Int.repr 2) <> Int.zero.
Proof.
  intros version e le m mb mo flags t le' m' answer Hm Hload Hrun Hclear.
  destruct (imb_actual_crouch_a_guard_skips_without_pressed_bit _ _ _ _ _ _ _ _ _ _ _
    Hm Hload Hclear Hrun) as (_ & _ & Hout). discriminate.
Qed.
