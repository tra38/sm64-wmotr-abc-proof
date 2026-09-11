(** Integration of the two independent backward searches. Their actual
    execution cuts are proved separately; this does not assert that a clean
    run connects the floor, controller and landing checkpoints. *)
From LessThanOneAPress.Proofs Require Import
  InkControllerRemembered InkFloorHistoryBackward InkLandingHistory
  InkActionTimerReset InkLandingTimerFrontier InkLandingLateClosure
  InkAnimationStorageSetup InkAnimationNoTransfer InkLandingOutcomeFrames
  InkLandingQuietSound InkLandingBoundedClosure InkCrouchSlideHistory InkActionPassHistory
  InkActionVisibilityFrame InkBodyResetHistory InkStarDialogFrame InkStarDialogCall
  InkScheduledSharedHistory InkPreparationConstruction InkAcceptedInitialStorage
  InkInputSharedConstruction InkInitialControllerGuard InkInputGeometryHistory InkPostDialogGroundReset
  InkRetryCompletion InkRetryQuery InkVerticalRetryGeometry InkRetryCallCompletion.

Definition InkBackwardHistoryCheckedBoundary : Prop :=
  InkLandingHistoryCheckedBoundary /\
  InkFloorHistoryCheckedBoundary /\ InkControllerRememberedCut /\
  InkCompletedActionTimerReset /\ InkCompletedLandingTimerFrontier /\
  InkLateLandingNegativeClosure /\ InkAnimationSetupInstallsBuffer /\
  InkAnimationListInitialization /\ InkAnimationNoTransferNoEffect /\
  InkRepeatedLandingSoundNoEffect /\ InkLandingDispatchOutcomeCut /\
  InkLandingDispatchCheckedFrame /\ InkAllGroundOutcomeTimerBound /\
  InkBoundedLateLandingNegativeClosure /\ InkCrouchWindowNoA /\ InkCrouchSlideEntryCut /\
  InkActionPassPreparationHistory /\ InkActionStartFirstWrite /\ InkSharedActionPrefixConstruction /\
  InkMilestoneCheckFrame /\ InkMilestoneNamedCallFrame /\ InkNativeSharedHistoryExtension /\
  InkConstructedNativePreparation /\ InkAcceptedInitialActionConstruction /\
  InkAcceptedInitialInputConstruction /\ InkInitialControllerGuardConstruction /\
  InkInitialInputGeometryHistory /\ InkPostDialogGroundResetBoundary /\
  InkRetryCompletedPosition /\ InkRetrySameRunFloorCall /\ InkVerticalRetryGeometryBoundary /\
  InkPrimaryQueryPositionFrame /\ InkRetryCompletedQueryPosition.

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
  split; [exact ilb_small_timer_excludes_first_negative_final_depth|].
  split; [exact ich_actual_timer_window_cannot_create_a|].
  split; [exact ich_actual_crouch_entry_reaches_suffix_without_a|].
  split; [exact iap_actual_pass_builds_shared_preparation_run|].
  split; [exact iav_constructed_start_excludes_first_flag_store_seed|].
  split; [exact ibr_accepted_call_extends_through_body_reset|].
  split; [exact isd_milestone_check_preserves_shared_readings|].
  split; [exact isd_named_call_preserves_shared_readings|].
  split; [exact ish_native_prefix_and_reset_extend_one_history|].
  split; [exact ipc_native_preparation_is_constructed|].
  split; [exact ini_accepted_action_prefix_constructed|].
  split; [exact iih_accepted_initial_action_reaches_buttons|].
  split; [exact icg_initial_history_passes_real_a_guard|].
  split; [exact iig_initial_history_connects_buttons_joystick_geometry|].
  split; [exact ipg_post_dialog_ground_reset_checked|].
  split; [exact irc_taken_retry_completes_before_second_query|].
  split; [exact irq_retry_connects_display_to_real_floor_call|].
  split; [exact ivr_vertical_retry_geometry_checked|].
  split; [exact ircq_first_query_preserves_actual_position|].
  exact ircq_retry_finishes_at_the_copied_display.
Qed.
