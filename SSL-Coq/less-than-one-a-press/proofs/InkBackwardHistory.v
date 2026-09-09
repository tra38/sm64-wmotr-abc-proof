(** Integration of the two independent backward searches. Their actual
    execution cuts are proved separately; this does not assert that a clean
    run connects the floor, controller and landing checkpoints. *)
From LessThanOneAPress.Proofs Require Import
  InkControllerRemembered InkFloorHistoryBackward InkLandingHistory.

Definition InkBackwardHistoryCheckedBoundary : Prop :=
  InkLandingHistoryCheckedBoundary /\
  InkFloorHistoryCheckedBoundary /\ InkControllerRememberedCut.

Theorem ibh_backward_histories_checked : InkBackwardHistoryCheckedBoundary.
Proof.
  split; [exact ilh_landing_history_checked|].
  split; [exact ifh_floor_history_boundary_checked|].
  exact icr_actual_edge_then_remember.
Qed.
