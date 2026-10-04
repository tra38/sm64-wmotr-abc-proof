(** The new direct-exclusion boundary consumes completed selected-program
    calls. It rules out a split at the ordinary copy's return, without imposing
    synchronization on all earlier or later gameplay. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes
  Rank1CaptureGeometry Rank1ObjectUpdateSchedule Rank1PlatformQueryCompletion
  InkRawCopyCompletion InkRawCopySource Area1Rank18CopyRead
  InkCopyCaller InkPlatformDeparture InkPlatformSource SelectedClightTarget
  EntryMemory OrdinaryArea1EntryMemory.
Import ListNotations.
Local Open Scope Z_scope.

Definition Rank1CopyReturnCannotSplit : Prop :=
  forall version m cb gb mb ob slot height t after result state_height raw_height,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge IRC._gCurrentObject = Some cb ->
  Genv.find_symbol ge IRC._gMarioObject = Some gb ->
  Genv.find_symbol ge IRC._gMarioStates = Some mb ->
  Genv.find_symbol ge IRC._gObjectPool = Some ob ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 m gb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (rank18_copy_body version)) [] t after result ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle state_height) ->
  Mem.load Mfloat32 after ob (object_slot_offset slot + 164) = Some (Vsingle raw_height) ->
  state_height = raw_height.

Theorem r1d_completed_copy_cannot_leave_a_vertical_split : Rank1CopyReturnCannotSplit.
Proof.
  unfold Rank1CopyReturnCannotSplit.
  intros version m cb gb mb ob slot height t after result state_height raw_height.
  cbn zeta. intros Hslot Hcs Hgs Hms Hps Hcurrent Hmario Hheight Hcopy Hstate Hraw.
  destruct (ircc_completed_copy_has_matching_state_and_collision_height _ _ _ _ _ _ _ _ _ _ _
    Hslot Hcs Hgs Hms Hps Hcurrent Hmario Hheight Hcopy) as [Hr [Hs _]].
  assert (state_height = height) by congruence.
  assert (raw_height = height) by congruence. congruence.
Qed.

(** This is a proved necessary replacement, not an assumption that no later
    writer exists. The actual Area-2 caller and the interval remain open. *)
Definition Rank1EffectiveApplyNeedsReplacement : Prop :=
  forall version pb cleared next t after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IPD._gMarioPlatform = Some pb ->
  Mem.load Mptr cleared pb 0 = Some (Vint Int.zero) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    next (Internal (ipd_body version IPDApply)) [] t after result ->
  after <> next ->
  Mem.load Mptr next pb 0 <> Mem.load Mptr cleared pb 0.

Theorem r1d_effective_apply_after_clearing_requires_replacement :
  Rank1EffectiveApplyNeedsReplacement.
Proof.
  intros version pb cleared next t after result Hsymbol Hclear Hcall Heffect Hsame.
  rewrite Hclear in Hsame.
  destruct (ipd_null_platform_call_cannot_depart _ _ _ _ _ _ Hsymbol Hsame Hcall) as [_ Hidentity].
  contradiction.
Qed.

Definition Rank1DirectExecutionBoundary : Prop :=
  Rank1CaptureGeometryBoundary /\ Rank1CompletedObjectUpdateQuery /\
  Rank1LowQueryCallClearing /\ InkRawCopyCompletion /\ Rank1CopyReturnCannotSplit /\
  Rank1EffectiveApplyNeedsReplacement.

Theorem r1d_direct_execution_checked : Rank1DirectExecutionBoundary.
Proof.
  split; [exact r1cg_capture_geometry_checked|].
  split; [exact r1s_actual_completed_call_must_query|].
  split; [exact r1qc_completed_low_query_call_clears_both|].
  split; [exact ircc_completed_copy_has_matching_state_and_collision_height|].
  split; [exact r1d_completed_copy_cannot_leave_a_vertical_split|].
  exact r1d_effective_apply_after_clearing_requires_replacement.
Qed.
