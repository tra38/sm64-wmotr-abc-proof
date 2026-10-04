(** Four source-linked producer cuts. These claims intentionally retain
    their different scopes. They neither construct a useful Ink pose nor
    assert that every gameplay history belongs to one of the cuts. *)
From LessThanOneAPress.Proofs Require Import InkFloorProducerEffect
  InkPlatformProducerHeight InkBounceProducerEffect InkQuicksandProducerSize.

Definition InkConcreteProducerCheckedBoundary : Prop :=
  InkFloorProducerCheckedBoundary /\ InkPlatformNonrotationHeightBoundary /\
  InkBounceHeightCheckpoint /\ InkBounceBoundedProducerCheckpoint /\
  InkBounceFreshContactNoDownwardCheckpoint /\
  InkQuicksandProducerSizeBoundary.

Theorem icpb_concrete_producer_boundary_checked : InkConcreteProducerCheckedBoundary.
Proof.
  split; [exact ifp_floor_producer_boundary_checked|].
  split; [exact iph_platform_nonrotation_height_checked|].
  split; [exact ibp_completed_bounce_reaches_height_checkpoint|].
  split; [exact ibp_completed_bounded_bounce_is_insufficient_at_snap|].
  split; [exact ibp_fresh_contact_bounce_cannot_snap_below_collision|].
  exact iqps_quicksand_producer_size_checked.
Qed.
