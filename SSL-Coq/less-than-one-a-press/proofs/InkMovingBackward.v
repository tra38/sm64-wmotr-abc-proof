(** Checked backward cuts, not a claim that their live histories are linked. *)
From compcert Require Import AST Clight Ctypes Globalenvs.
From LessThanOneAPress.Proofs Require Import GameTypes InkQuicksandBackward
  InkMovingBackwardSource InkFloorAlignmentBackward InkGroundBackwardSource
  InkGroundDisplayBackward InkGroundCallBackward InkNegativeDepthBackward
  SelectedClightTarget.

Definition InkMovingCheckedBoundary : Prop :=
  InkQuicksandCheckedBoundary /\
  (forall version kind, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (imb_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Ctypes.Internal (imb_body version kind))) /\
  InkFloorAlignmentHeightCut /\
  (forall version, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      us_mario_step._perform_ground_step = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Ctypes.Internal (igb_body version))) /\
  InkGroundCallRefreshCut /\ InkGroundRefreshHeightCut /\ InkNegativeDepthCheckedBoundary.

Theorem imb_moving_backward_checked : InkMovingCheckedBoundary.
Proof.
  split; [exact iq_quicksand_boundary_checked|].
  split; [exact imb_selected_bodies_resolve|].
  split; [exact imb_alignment_copies_entry_floor_and_preserves_object|].
  split; [exact igb_selected_body_resolves|].
  split; [exact igb_completed_ground_call_reaches_display_refresh|].
  split; [exact igb_refresh_reads_current_movement_height|].
  exact imb_negative_depth_backward_checked.
Qed.
