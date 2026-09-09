(** Integration of the two independent backward searches. Their actual
    execution cuts are proved separately; this does not assert that a clean
    run connects the floor, controller and landing checkpoints. *)
From LessThanOneAPress.Proofs Require Import
  InkControllerRemembered InkFloorHistoryBackward InkLandingHistory
  InkActionTimerReset InkLandingTimerFrontier InkLandingLateClosure
  InkAnimationStorageSetup InkAnimationNoTransfer InkLandingOutcomeFrames
  InkLandingQuietSound InkLandingBoundedClosure.

Definition InkBackwardHistoryCheckedBoundary : Prop :=
  InkLandingHistoryCheckedBoundary /\
  InkFloorHistoryCheckedBoundary /\ InkControllerRememberedCut /\
  InkCompletedActionTimerReset /\ InkCompletedLandingTimerFrontier /\
  InkLateLandingNegativeClosure /\ InkAnimationSetupInstallsBuffer /\
  InkAnimationListInitialization /\ InkAnimationNoTransferNoEffect /\
  InkRepeatedLandingSoundNoEffect /\ InkLandingDispatchOutcomeCut /\
  InkLandingDispatchCheckedFrame /\ InkAllGroundOutcomeTimerBound /\
  InkBoundedLateLandingNegativeClosure.

Theorem ibh_backward_histories_checked : InkBackwardHistoryCheckedBoundary.
Proof.
  split; [exact ilh_landing_history_checked|].
  split; [exact ifh_floor_history_boundary_checked|].
  split; [exact icr_actual_edge_then_remember|].
  split; [exact iar_completed_set_action_resets_original_timer|].
  split; [exact ilf_completed_landing_has_same_run_timer_frontier|].
  split; [exact ilt_checked_late_calls_exclude_first_negative_final_depth|].
  split; [exact ias_completed_setup_installs_original_buffer|].
  split; [exact ias_initialization_installs_separate_descriptor|].
  split; [exact ian_zero_loader_result_has_no_effect|].
  split; [exact iqs_repeated_landing_sound_has_no_request|].
  split; [exact iof_actual_dispatch_has_only_three_outcomes|].
  split; [exact iof_all_dispatch_outcomes_reset_or_preserve_timer|].
  split; [exact ilb_all_ground_outcomes_keep_a_small_timer|].
  exact ilb_small_timer_excludes_first_negative_final_depth.
Qed.
