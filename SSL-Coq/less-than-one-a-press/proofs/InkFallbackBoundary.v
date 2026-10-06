(** Fallback/contact integration.  The generated-source chronology, the
    completed real retry's position/contact effects and a reached pending
    warp guard are distinct claims.  Their conjunction does not construct a
    whole collision-to-warp history or a floor/owner/Ink outcome. *)
From LessThanOneAPress.Proofs Require Import
  InkFallbackSourceOrder InkFallbackContact InkFailedRetryGuard.

Definition InkFallbackCheckedBoundary : Prop :=
  InkFallbackSourceOrderExecutionBoundary /\ InkFallbackContactBoundary /\
  InkPendingWarpActualCallFrame.

Theorem ifb_fallback_contact_and_pending_guard_checked : InkFallbackCheckedBoundary.
Proof.
  split; [exact ifso_source_order_and_null_floor_execution_checked|].
  split; [exact ifct_fallback_contact_boundary_checked|].
  exact ifg_pending_operation_blocks_actual_trigger_call.
Qed.
