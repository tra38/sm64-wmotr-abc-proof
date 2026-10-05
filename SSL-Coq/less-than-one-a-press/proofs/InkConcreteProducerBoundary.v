(** Four source-linked producer cuts. These claims intentionally retain
    their different scopes. They neither construct a useful Ink pose nor
    assert that every gameplay history belongs to one of the cuts. *)
From LessThanOneAPress.Proofs Require Import InkFloorProducerEffect
  InkPlatformProducerHeight InkBounceProducerEffect InkQuicksandProducerSize
  InkStoppedFloorQuery InkGroundReturnFrame InkStoppedCrawlAlignment
  InkFloorAlignmentTailFrame.

(** These are adjacent actual cuts, not an asserted producer classification.
    In particular the matrix helper and the origin of the cached floor are
    still exposed, rather than hidden inside a coverage premise. *)
Definition InkStoppedFloorProducerCheckedBoundary : Prop :=
  InkStoppedFloorQueryBoundary /\ InkGroundReturnedPositionFrame /\
  InkStoppedCrawlReturnedGap /\ InkStoppedCrawlGroundReturnConnection /\
  InkStoppedCrawlActualResultAlignment /\ InkAlignmentTailFrameBoundary.

Theorem icpb_stopped_floor_producer_checked : InkStoppedFloorProducerCheckedBoundary.
Proof.
  split; [exact isfq_stopped_floor_query_checked|].
  split; [exact igr_ground_return_position_checked|].
  split; [exact isca_stopped_crawl_returned_gap_checked|].
  split; [exact isca_actual_ground_call_connects_return_to_switch|].
  split; [exact isca_real_ground_result_two_reaches_alignment|].
  exact ifat_alignment_tail_frame_boundary_checked.
Qed.

Definition InkConcreteProducerCheckedBoundary : Prop :=
  InkFloorProducerCheckedBoundary /\ InkPlatformNonrotationHeightBoundary /\
  InkBounceHeightCheckpoint /\ InkBounceBoundedProducerCheckpoint /\
  InkBounceFreshContactNoDownwardCheckpoint /\
  InkQuicksandProducerSizeBoundary /\ InkStoppedFloorProducerCheckedBoundary.

Theorem icpb_concrete_producer_boundary_checked : InkConcreteProducerCheckedBoundary.
Proof.
  split; [exact ifp_floor_producer_boundary_checked|].
  split; [exact iph_platform_nonrotation_height_checked|].
  split; [exact ibp_completed_bounce_reaches_height_checkpoint|].
  split; [exact ibp_completed_bounded_bounce_is_insufficient_at_snap|].
  split; [exact ibp_fresh_contact_bounce_cannot_snap_below_collision|].
  split; [exact iqps_quicksand_producer_size_checked|].
  exact icpb_stopped_floor_producer_checked.
Qed.
