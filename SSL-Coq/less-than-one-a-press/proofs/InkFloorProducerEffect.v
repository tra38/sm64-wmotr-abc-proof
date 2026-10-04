(** The accepted grounded quarter stores one height in both movement and
    cached floorHeight. An immediate align_with_floor snap therefore cannot
    create a new height split, even if the Object positions already disagree.

    This is a connection between actual generated executions. It deliberately
    stops before the matrix-building tail and does not cover early quarter
    returns or the caller's intervening helpers. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank10AGroundAlignment
  OrdinaryArea1EntryMemory InkCopyCompletion InkPostDialogGroundReset
  InkGroundBackwardSource
  InkFloorHistorySource InkFloorHistoryQuery InkBackwardExecution InkCopyCaller
  InkFloorResetExecution InkFloorResetSource InkMovingBackwardSource
  InkFloorAlignmentBackward ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Local Open Scope Z_scope.

Definition InkAcceptedFloorHeightPair : Prop :=
  forall version e le m mb floor t le' after out,
  e ! IFH._vec3f_set = None -> e ! IFH._atan2s = None ->
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  Mem.valid_block m mb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_accept version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle floor) /\
  Mem.load Mfloat32 after mb 112 = Some (Vsingle floor).

(** Neither the vector setter nor the wall-angle helper is abstracted by a
    memory-frame premise: their complete selected-body effects are reused. *)
Theorem ifp_accepted_quarter_installs_one_height : InkAcceptedFloorHeightPair.
Proof.
  unfold InkAcceptedFloorHeightPair.
  intros version e le m mb floor t le' after out Hset Hangle Hm Hfloor Hvalid Hrun.
  split.
  - eapply rank10g_accept_completes_y; eauto.
  - assert (ifh_accept version = Ssequence (ifh_accept_move version)
      (Ssequence (ifh_accept_floor version)
        (Ssequence (ifh_accept_height version) (ifh_accept_after version)))) as Hshape
      by (destruct version; reflexivity).
    rewrite Hshape in Hrun.
    destruct (ibk_split_sequence _ _ _ _ (ifh_accept_move version) _ _ _ _ _
      ltac:(destruct version; reflexivity) Hrun)
      as (ml & mm & mt & rt & Ht & Hmove & Hrest).
    assert (ml ! IFH._m = Some (Vptr mb Ptrofs.zero) /\
      ml ! IFH._floorHeight = Some (Vsingle floor)) as [Hm1 Hf1].
    { split; (erewrite ifr_execution_keeps_temp;
        [eassumption|exact Hmove|destruct version; reflexivity]). }
    destruct (ibk_split_sequence _ _ _ _ (ifh_accept_floor version) _ _ _ _ _
      ltac:(destruct version; reflexivity) Hrest)
      as (fl & fm & ft & ht & Hft & Hfp & Hrest2).
    assert (fl ! IFH._m = Some (Vptr mb Ptrofs.zero) /\
      fl ! IFH._floorHeight = Some (Vsingle floor)) as [Hm2 Hf2].
    { split; (erewrite ifr_execution_keeps_temp;
        [eassumption|exact Hfp|destruct version; reflexivity]). }
    destruct (ibk_split_sequence _ _ _ _ (ifh_accept_height version) _ _ _ _ _
      ltac:(destruct version; reflexivity) Hrest2)
      as (hl & hm & ht' & at' & Hht & Hheight & Hafter).
    assert (ifh_accept_height version = Sassign ifr_floor_read
      (Etempvar IFH._floorHeight tfloat)) as Hh by (destruct version; reflexivity).
    rewrite Hh in Hheight.
    destruct (ifh_floor_result_store _ _ _ _ _ _ _ _ _ _ _ Hm2 Hf2 Hheight)
      as (f & Heq & Hstore & Hload & Hframe & _).
    inversion Heq; subst f.
    rewrite (rank10g_post_frame _ (rank10g_post_classified version)
      _ _ _ _ _ _ _ _ Hangle Hafter).
    exact Hload.
Qed.

Definition InkAcceptedFloorAlignmentNoNewGap : Prop :=
  forall version e le before mb ob floor tq quarter_le aligned quarter_out
      ta after result,
  let ge := Clight.globalenv (selected_clight_target version) in
  e ! IFH._vec3f_set = None -> e ! IFH._atan2s = None ->
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  Mem.valid_block before mb ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  ocn_exec ge e le before (ifh_accept version) tq quarter_le aligned quarter_out ->
  ClightBigstep.Clight2.eval_funcall ge aligned (Internal (imb_body version IMBAlign))
    [Vptr mb Ptrofs.zero] ta after result ->
  exists snap_le snap_m final_le out,
    Mem.load Mfloat32 aligned mb 64 = Some (Vsingle floor) /\
    Mem.load Mfloat32 aligned mb 112 = Some (Vsingle floor) /\
    Mem.store Mfloat32 aligned mb 64 (Vsingle floor) = Some snap_m /\
    Mem.load Mfloat32 snap_m mb 64 = Mem.load Mfloat32 aligned mb 64 /\
    (forall chunk offset,
      Mem.load chunk snap_m ob offset = Mem.load chunk aligned ob offset) /\
    snap_le ! IMB._m = Some (Vptr mb Ptrofs.zero) /\
    ocn_exec ge empty_env snap_le snap_m (imb_align_tail version)
      ta final_le after out.

(** No numerical gap or position agreement is assumed. At the snap the
    movement height is unchanged and every Object-pool load is unchanged,
    so any display/collision disagreement there was already present. *)
Theorem ifp_accepted_floor_then_alignment_cannot_create_a_gap :
  InkAcceptedFloorAlignmentNoNewGap.
Proof.
  unfold InkAcceptedFloorAlignmentNoNewGap.
  intros version e le before mb ob floor tq quarter_le aligned quarter_out
    ta after result Hset Hangle Hm Hfloor Hvalid Hstate Hpool Hquarter Hcall.
  destruct (ifp_accepted_quarter_installs_one_height version e le before mb floor
    tq quarter_le aligned quarter_out Hset Hangle Hm Hfloor Hvalid Hquarter)
    as [Hy Hcached].
  destruct (imb_alignment_copies_entry_floor_and_preserves_object version aligned
    mb ob floor ta after result Hstate Hpool Hcached Hcall)
    as (snap_le & snap_m & final_le & out & Hstore & Hsnap & Hobject & HmSnap & Htail).
  exists snap_le, snap_m, final_le, out.
  repeat apply conj; try assumption. rewrite Hsnap, Hy. reflexivity.
Qed.

(** The actual ground refresh is in front of align_with_floor at its stock
    call sites. This composition accounts for its complete display copy;
    the enclosing loop and intervening animation/speed calls stay separate. *)
Definition InkAcceptedRefreshAlignmentNoDisplayGap : Prop :=
  forall version e le before mb ob slot floor tq quarter_le aligned quarter_out
      refresh_le tc refreshed_le refreshed refresh_out ta after result,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  e ! IFH._vec3f_set = None -> e ! IFH._atan2s = None ->
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  Mem.valid_block before mb ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  ocn_exec ge e le before (ifh_accept version) tq quarter_le aligned quarter_out ->
  Mem.valid_block aligned ob ->
  e ! IFR._vec3f_copy = None ->
  refresh_le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 aligned mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec ge e refresh_le aligned (igb_refresh version)
    tc refreshed_le refreshed refresh_out ->
  ClightBigstep.Clight2.eval_funcall ge refreshed (Internal (imb_body version IMBAlign))
    [Vptr mb Ptrofs.zero] ta after result ->
  exists snap_le snap_m final_le out,
    Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle floor) /\
    Mem.load Mfloat32 snap_m ob (object_slot_offset slot + 36) = Some (Vsingle floor) /\
    Mem.load Mfloat32 snap_m ob (object_slot_offset slot + 164) =
      Mem.load Mfloat32 refreshed ob (object_slot_offset slot + 164) /\
    ocn_exec ge empty_env snap_le snap_m (imb_align_tail version)
      ta final_le after out.

Theorem ifp_accepted_refresh_then_alignment_has_zero_display_gap :
  InkAcceptedRefreshAlignmentNoDisplayGap.
Proof.
  unfold InkAcceptedRefreshAlignmentNoDisplayGap.
  intros version e le before mb ob slot floor tq quarter_le aligned quarter_out
    refresh_le tc refreshed_le refreshed refresh_out ta after result
    Hslot Hset Hangle Hm Hfloor Hvalid Hstate Hpool Hquarter
    HobjectValid Hcopy HrefreshM Hobject Hrefresh Hcall.
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool) as Hseparate.
  destruct (ifp_accepted_quarter_installs_one_height version e le before mb floor
    tq quarter_le aligned quarter_out Hset Hangle Hm Hfloor Hvalid Hquarter)
    as [Hy Hcached].
  destruct (ipg_ground_refresh_completes_without_old_display version e refresh_le
    aligned mb ob slot floor tc refreshed_le refreshed refresh_out
    Hslot Hseparate HobjectValid Hcopy HrefreshM Hobject Hy Hrefresh)
    as [Hdisplay Hframe].
  assert (Mem.valid_block aligned mb) as HstateValid
    by (eapply ibcc_loaded_block_valid; exact Hy).
  assert (Mem.load Mfloat32 refreshed mb 112 = Some (Vsingle floor)) as HcachedNow.
  { rewrite Hframe; [exact Hcached|exact HstateValid|left; exact Hseparate]. }
  destruct (imb_alignment_copies_entry_floor_and_preserves_object version refreshed
    mb ob floor ta after result Hstate Hpool HcachedNow Hcall)
    as (snap_le & snap_m & final_le & out & Hstore & Hsnap & HobjectFrame & HmSnap & Htail).
  exists snap_le, snap_m, final_le, out.
  split; [exact Hsnap|]. split.
  - rewrite HobjectFrame. exact Hdisplay.
  - split; [apply HobjectFrame|exact Htail].
Qed.

Definition InkFloorProducerCheckedBoundary : Prop :=
  InkAcceptedFloorHeightPair /\ InkAcceptedFloorAlignmentNoNewGap /\
  InkAcceptedRefreshAlignmentNoDisplayGap.

Theorem ifp_floor_producer_boundary_checked : InkFloorProducerCheckedBoundary.
Proof.
  split; [exact ifp_accepted_quarter_installs_one_height|].
  split; [exact ifp_accepted_floor_then_alignment_cannot_create_a_gap|
    exact ifp_accepted_refresh_then_alignment_has_zero_display_gap].
Qed.
