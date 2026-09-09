(** Integration of the two independent backward searches. Their actual
    execution cuts are proved separately; this does not assert that a clean
    run connects the floor, controller and landing checkpoints. *)
From LessThanOneAPress.Proofs Require Import
  InkControllerRemembered InkFloorHistoryBackward InkLandingHistory
  InkActionTimerReset InkLandingTimerFrontier InkLandingLateClosure.

Definition InkBackwardHistoryCheckedBoundary : Prop :=
  InkLandingHistoryCheckedBoundary /\
  InkFloorHistoryCheckedBoundary /\ InkControllerRememberedCut /\
  InkCompletedActionTimerReset /\ InkCompletedLandingTimerFrontier /\
  InkLateLandingNegativeClosure.

Theorem ibh_backward_histories_checked : InkBackwardHistoryCheckedBoundary.
Proof.
  split; [exact ilh_landing_history_checked|].
  split; [exact ifh_floor_history_boundary_checked|].
  split; [exact icr_actual_edge_then_remember|].
  split; [exact iar_completed_set_action_resets_original_timer|].
  split; [exact ilf_completed_landing_has_same_run_timer_frontier|].
  exact ilt_checked_late_calls_exclude_first_negative_final_depth.
Qed.
