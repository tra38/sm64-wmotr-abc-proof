(** Exhaust the actual post-ground switch, including wall contact. This does
    not assume that the preceding movement call preserved the landing timer. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkMovingBackwardSource InkLandingContinuationSource InkLandingDispatch
  InkLateHelperSource InkLateCallExecution InkAnimationTimerFrame InkAnimationLoaderFrame
  InkLandingHistoryGate ObjectContactNecessity ContactConsumerExecution Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iof_wall_animation := Scall None
  (Evar IBM._set_mario_animation (Tfunction [ill_mario_pointer; tint] tshort cc_default))
  [Etempvar IMB._m ill_mario_pointer; Econst_int (Int.repr 108) tint].

Lemma iof_wall_case : forall version,
  seq_of_labeled_statement (select_switch 2 (ilc_cases version)) =
    Ssequence (Ssequence iof_wall_animation Sbreak) Sskip.
Proof. intros []; reflexivity. Qed.

Lemma iof_other_case : forall version n, n <> 0 -> n <> 2 ->
  seq_of_labeled_statement (select_switch n (ilc_cases version)) = Sskip.
Proof.
  intros [] n Hzero Htwo;
    cbv [ilc_cases ilc_dispatch ilc_after_ground imb_body ibk_head
      rank12b_drop_sequences fn_body IMB.f_common_landing_action
      jp_mario_actions_moving.f_common_landing_action
      select_switch select_switch_case select_switch_default seq_of_labeled_statement];
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    congruence.
Qed.

Definition InkLandingDispatchOutcomeCut : Prop :=
  forall version le m mb mo step t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  le ! IMB._stepResult = Some (Vint step) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilc_dispatch version) t le' m' out ->
  (Int.unsigned step = 0 /\ ilh_timer_load m' mb mo = Some (Vint Int.zero)) \/
  (Int.unsigned step = 2 /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      iof_wall_animation t le' m' Out_normal) \/
  (Int.unsigned step <> 0 /\ Int.unsigned step <> 2 /\ m' = m).

Theorem iof_actual_dispatch_has_only_three_outcomes : InkLandingDispatchOutcomeCut.
Proof.
  intros version le m mb mo step t le' m' out Hm Hstep Hrun.
  destruct (Z.eq_dec (Int.unsigned step) 0) as [Hzero|Hzero].
  - left. split; [exact Hzero|].
    assert (step = Int.zero) by (rewrite <- (Int.repr_unsigned step), Hzero; reflexivity).
    subst step. eapply (ilc_left_ground_dispatch_resets_timer version empty_env le m mb mo);
      [reflexivity|exact Hm|exact Hstep|exact Hrun].
  - destruct (ilc_source_cuts version) as (_ & _ & _ & _ & _ & _ & Hshape & _).
    rewrite Hshape in Hrun. inversion Hrun; subst.
    match goal with Hr : eval_expr _ _ _ _ (Etempvar IMB._stepResult _) ?v |- _ =>
      assert (v = Vint step) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hswitch : sem_switch_arg _ _ = Some ?n |- _ =>
      change (Some (Int.unsigned step) = Some n) in Hswitch; inversion Hswitch; subst end.
    destruct (Z.eq_dec (Int.unsigned step) 2) as [Htwo|Htwo].
    + right. left. split; [exact Htwo|].
      match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
        (seq_of_labeled_statement (select_switch _ _)) _ _ _ _ |- _ =>
        rewrite Htwo, iof_wall_case in Hr end.
      cce_unroll_loop_free_exec.
      all: try solve [match goal with
        Hr : ClightBigstep.exec_stmt _ _ _ _ _ iof_wall_animation _ _ _ ?bad,
        Hbad : ?bad <> Out_normal |- _ => inversion Hr; subst; contradiction end].
      all: lazymatch goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ iof_wall_animation _ _ _ _ |- _ =>
        rewrite ?E0_right; exact Hr end.
    + right. right. repeat split; try assumption.
      match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
        (seq_of_labeled_statement (select_switch _ _)) _ _ _ _ |- _ =>
        rewrite (iof_other_case version _ Hzero Htwo) in Hr; inversion Hr; reflexivity end.
Qed.

Lemma iof_wall_animation_preserves_timer : forall version le m mb mo ob oo lb lo ab ao t le' m',
  le ! IMB._m = Some (Vptr mb mo) ->
  InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao ->
  InkAnimationTransferTimerEffect version mb mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    iof_wall_animation t le' m' Out_normal ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version le m mb mo ob oo lb lo ab ao t le' m' Hm Hdest Htransfer Hrun.
  unfold iof_wall_animation in Hrun.
  destruct (ilh_actual_named_call version ILAnimation empty_env le m None _
    [ill_mario_pointer; tint] tshort t le' m' Out_normal eq_refl Hrun)
    as (values & result & Hargs & Hcall).
  destruct (ilh_actual_mario_arguments _ _ _ _ _ _ _ mb mo Hm Hargs) as [rest ->].
  eapply iaf_actual_animation_preserves_timer; [exact Htransfer|exact Hdest|exact Hcall].
Qed.

Definition InkLandingDispatchCheckedFrame : Prop :=
  forall version le m mb mo step ob oo lb lo ab ao t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  le ! IMB._stepResult = Some (Vint step) ->
  (Int.unsigned step = 2 -> InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao) ->
  InkAnimationTransferTimerEffect version mb mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilc_dispatch version) t le' m' out ->
  ilh_timer_load m' mb mo =
    if Z.eq_dec (Int.unsigned step) 0 then Some (Vint Int.zero) else ilh_timer_load m mb mo.

Theorem iof_all_dispatch_outcomes_reset_or_preserve_timer : InkLandingDispatchCheckedFrame.
Proof.
  intros version le m mb mo step ob oo lb lo ab ao t le' m' out Hm Hstep Hdest Htransfer Hrun.
  destruct (iof_actual_dispatch_has_only_three_outcomes version le m mb mo step t le' m' out
    Hm Hstep Hrun) as [(Hzero & Hreset)|[(Htwo & Hwall)|(Hzero & Htwo & ->)]].
  - destruct (Z.eq_dec (Int.unsigned step) 0); congruence.
  - destruct (Z.eq_dec (Int.unsigned step) 0); [lia|].
    eapply iof_wall_animation_preserves_timer;
      [exact Hm|exact (Hdest Htwo)|exact Htransfer|exact Hwall].
  - destruct (Z.eq_dec (Int.unsigned step) 0); congruence.
Qed.
