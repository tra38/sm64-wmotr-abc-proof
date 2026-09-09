(** A continuous, actually executed cancellation suffix: the duration gate,
    both remaining input tests and the return.  The later landing helper
    calls are deliberately NOT framed by this theorem. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkLandingHistorySource
  InkLandingHistoryGate InkLandingHistoryReturn InkControllerBackward
  InkMovingBackwardSource InkLandingExecution InkBackwardSource InkCopyCaller
  InkBackwardExecution InkFloorResetExecution InkMarioInputFlag
  ObjectContactNecessity SelectedClightTarget ZeroAQuicksandEntryBoundary.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ilh_input_guard id mask yes := Ssequence (Sset id imb_input)
  (Sifthenelse (Ebinop Oand (Etempvar id tushort) (Econst_int mask tint) tint) yes Sskip).

Lemma ilh_input_guard_skips_clear_mask :
  forall version e le m mb mo id mask yes flags t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> imf_input_load m mb mo = Some (Vint flags) ->
  Int.and flags mask = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_input_guard id mask yes) t le' m' out ->
  t = E0 /\ m' = m /\ out = Out_normal /\ le' = PTree.set id (Vint flags) le.
Proof.
  intros version e le m mb mo id mask yes flags t le' m' out Hm Hload Hclear Hrun.
  unfold ilh_input_guard in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset id imb_input) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hbranch).
  inversion Hread; subst.
  match goal with H : eval_expr _ _ _ _ imb_input ?v |- _ =>
    assert (v = Vint flags) by (eapply imb_ushort_field_read;
      [exact Hm|exact (proj2 (imb_control_fields version))|exact Hload|exact H]); subst v end.
  inversion Hbranch; subst.
  match goal with H : eval_expr ?ge ?env ?temps ?memory (Ebinop Oand _ _ _) ?v |- _ =>
    assert (v = Vint (Int.and flags mask)) by
      (eapply (imf_and_constant_value ge env temps memory id mask flags); [apply PTree.gss|exact H]); subst v end.
  match goal with H : bool_val (Vint (Int.and flags mask)) _ _ = Some ?choice |- _ =>
    rewrite Hclear in H; change (Some false = Some choice) in H; inversion H; subst end.
  match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H; subst end.
  repeat split; reflexivity.
Qed.

Lemma ilh_split_clear_input_guard : forall version e le m mb mo id mask yes flags rest t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> imf_input_load m mb mo = Some (Vint flags) ->
  Int.and flags mask = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Ssequence (ilh_input_guard id mask yes) rest) t le' m' out ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e
    (PTree.set id (Vint flags) le) m rest t le' m' out.
Proof.
  intros version e le m mb mo id mask yes flags rest t le' m' out Hm Hload Hclear Hrun.
  inversion Hrun; subst.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (ilh_input_guard _ _ _) _ _ _ _ |- _ =>
      destruct (ilh_input_guard_skips_clear_mask _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hload Hclear H)
        as (-> & -> & _ & ->) end. assumption.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (ilh_input_guard _ _ _) _ _ _ _ |- _ =>
      destruct (ilh_input_guard_skips_clear_mask _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hload Hclear H)
        as (_ & _ & Hout & _) end. contradiction.
Qed.

Theorem ilh_remaining_clear_input_checks_preserve_memory :
  forall version e le m mb mo flags t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> imf_input_load m mb mo = Some (Vint flags) ->
  Int.and flags (Int.repr 2) = Int.zero -> Int.and flags (Int.repr 4) = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_after_gate version) t le' m' out ->
  t = E0 /\ m' = m /\ out = Out_return (Some (Vint Int.zero, tint)) /\
    le' ! IMB._m = Some (Vptr mb mo).
Proof.
  intros version e le m mb mo flags t le' m' out Hm Hload HnoA Hground Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & _ & _ & _ & _ & Htail & Ha & Hoff & _).
  rewrite Htail, Ha, Hoff in Hrun.
  change (ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Ssequence (ilh_input_guard IMB._t'11 (Int.repr 2) (ilh_a_yes version))
      (Ssequence (ilh_input_guard IMB._t'9 (Int.repr 4) (ilh_off_yes version))
        (Sreturn (Some (Econst_int Int.zero tint))))) t le' m' out) in Hrun.
  pose proof (ilh_split_clear_input_guard _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hload HnoA Hrun) as Hrest.
  pose proof (ilh_split_clear_input_guard version e (PTree.set IMB._t'11 (Vint flags) le) m
    mb mo IMB._t'9 (Int.repr 4) (ilh_off_yes version) flags
    (Sreturn (Some (Econst_int Int.zero tint))) t le' m' out
    ltac:(rewrite PTree.gso by discriminate; exact Hm) Hload Hground Hrest) as Hreturn.
  inversion Hreturn; subst.
  match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
  repeat split; try reflexivity. repeat rewrite PTree.gso by discriminate. exact Hm.
Qed.

Lemma ilh_gate_normal_or_nonzero_return : forall version e le m t le' m' out,
  e ! IMB._set_mario_action = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_gate version) t le' m' out ->
  out = Out_normal \/ out = Out_return (Some (Vint Int.one, tuint)).
Proof.
  intros version e le m t le' m' out Hlocal Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & _ & Hgate & _ & Hguard & _).
  rewrite Hgate in Hrun.
  assert (ibk_normal (ilh_increment version) = true) as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suf & Htrace & Hincrement & Hduration).
  rewrite Hguard in Hduration.
  destruct (ibk_split_sequence _ _ _ _ (Sset IMB._t'13 ilh_frames) _ _ _ _ _ eq_refl Hduration)
    as (guard_le & guard_m & read_t & branch_t & Htrace2 & Hread & Hbranch).
  inversion Hbranch; subst. destruct b.
  - right. eapply ilh_duration_rejection_returns_one; eauto.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H; subst end.
    left. reflexivity.
Qed.

Definition InkLandingCancellationTailCut : Prop :=
  forall version e le m mb mo db dofs before frames flags t le' m',
  e ! IMB._set_mario_action = None -> imf_room mo ->
  le ! IMB._m = Some (Vptr mb mo) -> le ! IMB._landingAction = Some (Vptr db dofs) ->
  mb <> db -> ilh_timer_load m mb mo = Some (Vint before) ->
  Mem.load Mint16signed m db (Ptrofs.unsigned dofs) = Some (Vint frames) ->
  imf_input_load m mb mo = Some (Vint flags) ->
  Int.and flags (Int.repr 2) = Int.zero -> Int.and flags (Int.repr 4) = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_gate_tail version) t le' m' (Out_return (Some (Vint Int.zero, tint))) ->
  Mem.store Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26)))
    (Vint (ilh_next_timer before)) = Some m' /\
  ilh_timer_load m' mb mo = Some (Vint (ilh_next_timer before)) /\
  Int.unsigned (ilh_next_timer before) < Int.signed frames /\
  imf_input_load m' mb mo = Some (Vint flags) /\
  le' ! IMB._m = Some (Vptr mb mo) /\ t = E0.

Theorem ilh_actual_gate_to_zero_return_keeps_bounded_timer : InkLandingCancellationTailCut.
Proof.
  unfold InkLandingCancellationTailCut.
  intros version e le m mb mo db dofs before frames flags t le' m'
    Hlocal Hroom Hm Hdescriptor Hseparate Htimer Hframes Hflags HnoA Hground Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & Hshape & _). rewrite Hshape in Hrun.
  inversion Hrun; subst.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (ilh_gate version) _ ?middle ?memory _ |- _ =>
      destruct (ilh_actual_duration_gate_bounds_its_stored_timer _ _ _ _ _ _ _ _ _ _ _ _ _
        Hm Hdescriptor Hseparate Htimer Hframes H)
        as (Hstore & Hstored & Hbound & HmNow & HdescriptorNow & Hpre);
      assert (imf_input_load memory mb mo = Some (Vint flags)) as HflagsNow by
        (rewrite <- Hflags; unfold imf_input_load; eapply Mem.load_store_other; [exact Hstore|];
         right; left; cbn [size_chunk]; rewrite !imf_address by (auto; lia); lia)
    end.
    match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (ilh_after_gate version) _ _ _ _ |- _ =>
      destruct (ilh_remaining_clear_input_checks_preserve_memory _ _ _ _ _ _ _ _ _ _ _
        HmNow HflagsNow HnoA Hground H) as (Hsuf & Hmemory & _ & HmFinal) end.
    subst. repeat split; assumption || reflexivity.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (ilh_gate version) _ _ _ _ |- _ =>
      destruct (ilh_gate_normal_or_nonzero_return _ _ _ _ _ _ _ _ Hlocal H) as [Hnormal|Hone]
    end; contradiction || discriminate.
Qed.

Corollary ilh_stock_cancel_suffix_returns_timer_below_duration :
  forall kind version e le m mb mo db dofs before flags t le' m',
  e ! IMB._set_mario_action = None -> imf_room mo ->
  le ! IMB._m = Some (Vptr mb mo) -> le ! IMB._landingAction = Some (Vptr db dofs) ->
  mb <> db -> ilh_timer_load m mb mo = Some (Vint before) ->
  Mem.load Mint16signed m db (Ptrofs.unsigned dofs) = Some (Vint (Int.repr (stock_landing_frames kind))) ->
  imf_input_load m mb mo = Some (Vint flags) ->
  Int.and flags (Int.repr 2) = Int.zero -> Int.and flags (Int.repr 4) = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_gate_tail version) t le' m' (Out_return (Some (Vint Int.zero, tint))) ->
  ilh_timer_load m' mb mo = Some (Vint (ilh_next_timer before)) /\
    Int.unsigned (ilh_next_timer before) < stock_landing_frames kind.
Proof.
  intros kind version e le m mb mo db dofs before flags t le' m' Hlocal Hroom Hm Hd Hsep Htimer Hframes Hflags Ha Hoff Hrun.
  destruct (ilh_actual_gate_to_zero_return_keeps_bounded_timer _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hlocal Hroom Hm Hd Hsep Htimer Hframes Hflags Ha Hoff Hrun) as (_ & Hload & Hbound & _).
  split; [exact Hload|]. destruct kind; exact Hbound.
Qed.

Definition InkLandingHistoryCheckedBoundary : Prop :=
  InkControllerCheckedBoundary /\
  (forall version, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IMB._common_landing_cancels = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ilh_cancel_body version))) /\
  InkActualLandingDurationGate /\ InkLandingCancellationTailCut.

Theorem ilh_landing_history_checked : InkLandingHistoryCheckedBoundary.
Proof.
  split; [exact icb_controller_backward_checked|].
  split; [exact ilh_selected_cancels_resolves|].
  split; [exact ilh_actual_duration_gate_bounds_its_stored_timer|].
  exact ilh_actual_gate_to_zero_return_keeps_bounded_timer.
Qed.
