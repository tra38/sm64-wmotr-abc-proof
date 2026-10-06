(** A taken graphical fallback transfers all three displayed coordinates to
    MarioState while preserving the existing raw/contact records.  The real
    completed second find_floor and the floorHeight store are included.  This
    preserves the cache present at the copy cut; it does not identify that
    cache with the earlier collision detection or prove a later warp accepts.
    No live floor result, miss/top coverage or clean producer is supplied. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkCopyCompletion InkRetryCompletion
  InkRetryQuery InkRetryCallCompletion InkFloorCallEffects InkFloorListEffects
  InkFloorHistorySource InkFloorHistoryQuery InkRawCopyStores
  InkVerticalRetryGeometry InkQuicksandProducerSize EyerokRank15LiveMovement
  OrdinaryArea1EntryMemory ObjectContactNecessity ContactConsumerExecution Area2Rank12BContact
  UpperElevatorQueryResolution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

(** Named cache destinations in the actual selected composite environment. *)
Theorem ifct_selected_contact_fields : forall version,
  let ce := genv_cenv (Clight.globalenv (selected_clight_target version)) in
  ibcc_field_ok ce IBM._Object IBM._collidedObjInteractTypes 112 = true /\
  ibcc_field_ok ce IBM._Object IBM._numCollidedObjs 118 = true /\
  ibcc_field_ok ce IBM._Object IBM._collidedObjs 120 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._collidedObjInteractTypes 164 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._interactObj 120 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._usedObj 128 = true.
Proof.
  intro version. cbn zeta.
  change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._Object IBM._collidedObjInteractTypes 112 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._Object IBM._numCollidedObjs 118 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._Object IBM._collidedObjs 120 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IBM._collidedObjInteractTypes 164 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IBM._interactObj 120 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IBM._usedObj 128 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Definition ifct_state_contact_offset ofs := In ofs [120;128;164].

Lemma ifct_symbol_separate_from_floor_globals : forall version id b,
  In id [us_object_list_processor._gMarioStates; us_object_list_processor._gObjectPool] ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) id = Some b ->
  forall other, In other ifc_globals ->
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) other <> Some b.
Proof.
  intros version id b Hid Hsymbol other Hother Hsame.
  assert (id <> other) as Hids by
    (destruct Hid as [<-|[<-|[]]];
     destruct Hother as [<-|[<-|[<-|[]]]]; discriminate).
  assert (b <> b) as Hcontra by (eapply Genv.global_addresses_distinct; eauto).
  exact (Hcontra eq_refl).
Qed.

(** The floor callee has actual limited writes.  Ordinary symbol separation
    derives the pool/contact frame; no narrow callee frame is assumed. *)
Theorem ifct_completed_floor_preserves_raw_and_contact :
  forall version m mb ob x y z t after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block m mb -> Mem.valid_block m ob ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ueqr_native_body version UEQRFindFloor))
    [x;y;z;Vptr mb (Ptrofs.repr 104)] t after result ->
  t = E0 /\
  (forall chunk ofs, Mem.load chunk after ob ofs = Mem.load chunk m ob ofs) /\
  (forall ofs, ifct_state_contact_offset ofs ->
    Mem.load Mint32 after mb ofs = Mem.load Mint32 m mb ofs).
Proof.
  intros version m mb ob x y z t after result Hstate Hpool Hmb Hob Hcall.
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool) as Hsep.
  assert (forall chunk ofs,
    t = E0 /\ Mem.load chunk after ob ofs = Mem.load chunk m ob ofs) as Hobject.
  { intros chunk ofs. eapply ifc_completed_floor_preserves_other_cells; eauto.
    - eapply (ifct_symbol_separate_from_floor_globals version
        us_object_list_processor._gObjectPool ob); [cbn; tauto|exact Hpool].
    - left; congruence. }
  split; [exact (proj1 (Hobject Mint32 0))|]. split.
  - intros; exact (proj2 (Hobject _ _)).
  - intros ofs Hoffset.
    assert (forall id, In id ifc_globals ->
      Genv.find_symbol (Clight.globalenv (selected_clight_target version)) id <> Some mb)
      as Hglobals by (eapply (ifct_symbol_separate_from_floor_globals version
        us_object_list_processor._gMarioStates mb); [cbn; tauto|exact Hstate]).
    assert (ifl_disjoint mb (Ptrofs.unsigned (Ptrofs.repr 104)) 4 Mint32 mb ofs)
      as Houtside by (right; right; change (108 <= ofs);
        destruct Hoffset as [<-|[<-|[<-|[]]]]; lia).
    exact (proj2 (ifc_completed_floor_preserves_other_cells
      version m x y z mb (Ptrofs.repr 104) t after result Mint32 mb ofs
      Hmb Hglobals Houtside Hcall)).
Qed.

Definition InkTakenFallbackContactTransfer : Prop :=
  forall version e le m mb ob slot values t le' after out,
  e ! IBM._vec3f_copy = None -> e ! IBM._find_floor = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  (slot < object_pool_capacity)%nat ->
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  (forall axis, Mem.load Mfloat32 m ob
    (object_slot_offset slot + 32 + 4 * icp_number axis) = Some (Vsingle (values axis))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' after out ->
  exists copied query_m copy_trace result floor,
    t = copy_trace /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ibk_copy_body version))
      [Vptr mb (Ptrofs.repr 60);Vptr ob (Ptrofs.repr (object_slot_offset slot + 32))]
      copy_trace copied result /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      copied (Internal (ueqr_native_body version UEQRFindFloor))
      [Vsingle (values ICPX);Vsingle (values ICPY);Vsingle (values ICPZ);
       Vptr mb (Ptrofs.repr 104)] E0 query_m (Vsingle floor) /\
    Mem.store Mfloat32 query_m mb 112 (Vsingle floor) = Some after /\
    (forall axis,
      Mem.load Mfloat32 copied mb (60 + 4 * icp_number axis) = Some (Vsingle (values axis)) /\
      Mem.load Mfloat32 after mb (60 + 4 * icp_number axis) = Some (Vsingle (values axis))) /\
    (forall chunk ofs,
      Mem.load chunk copied ob ofs = Mem.load chunk m ob ofs /\
      Mem.load chunk after ob ofs = Mem.load chunk m ob ofs) /\
    (forall ofs, ifct_state_contact_offset ofs ->
      Mem.load Mint32 copied mb ofs = Mem.load Mint32 m mb ofs /\
      Mem.load Mint32 after mb ofs = Mem.load Mint32 m mb ofs) /\ out = Out_normal.

Theorem ifct_taken_fallback_transfers_display_and_preserves_contact :
  InkTakenFallbackContactTransfer.
Proof.
  intros version e le m mb ob slot values t le' after out
    HcopyName HfloorName Hstate Hpool Hslot Hm Hobject Hvalues Hretry.
  destruct (irc_taken_retry_completes_before_second_query version e le m mb ob slot
    values t le' after out HcopyName Hstate Hpool Hslot Hm Hobject Hvalues Hretry)
    as (copied & copy_trace & query_trace & result & Htrace & Hcopy & Hposition & HcopyFrame & Hquery).
  destruct (irq_second_floor_call_uses_completed_position version e
    (PTree.set IBM._t'45 (Vptr ob (Ptrofs.repr (object_slot_offset slot))) le)
    copied mb values query_trace le' after out HfloorName
    ltac:(rewrite PTree.gso by discriminate; exact Hm) Hposition Hquery)
    as (floor & query_m & Hfloor & Hstore & Hy & Hout).
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool) as Hsep.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ (Hvalues ICPX)) as Hob.
  assert (Mem.valid_block copied ob) as HobCopy.
  { apply (ibcc_loaded_block_valid _ _ _ _ _
      (eq_trans (HcopyFrame Mfloat32 ob
        (object_slot_offset slot + 32 + 4 * icp_number ICPX) Hob
        (or_introl (not_eq_sym Hsep))) (Hvalues ICPX))). }
  destruct (ifct_completed_floor_preserves_raw_and_contact version copied mb ob
    (Vsingle (values ICPX)) (Vsingle (values ICPY)) (Vsingle (values ICPZ))
    query_trace query_m (Vsingle floor) Hstate Hpool
    (ibcc_loaded_block_valid _ _ _ _ _ (Hposition ICPX)) HobCopy Hfloor)
    as (Hzero & HpoolFloor & HcacheFloor).
  destruct (ifc_floor_call_preserves_mario_position version copied mb
    (Vsingle (values ICPX)) (Vsingle (values ICPY)) (Vsingle (values ICPZ))
    query_trace query_m (Vsingle floor) Hstate
    (ibcc_loaded_block_valid _ _ _ _ _ (Hposition ICPX)) Hfloor)
    as (_ & HstateFloor).
  subst query_trace. rewrite app_nil_r in Htrace.
  exists copied, query_m, copy_trace, result, floor.
  repeat apply conj; try assumption.
  - intros axis. split; [exact (Hposition axis)|].
    erewrite Mem.load_store_other; [|exact Hstore|right; left;
      destruct axis; cbn [icp_number size_chunk]; lia].
    rewrite HstateFloor by (destruct axis; cbn [icp_number]; lia).
    exact (Hposition axis).
  - intros chunk ofs.
    assert (Mem.load chunk copied ob ofs = Mem.load chunk m ob ofs) as Hcopied
      by (apply HcopyFrame; [exact Hob|left; congruence]).
    split; [exact Hcopied|].
    erewrite Mem.load_store_other; [|exact Hstore|left; congruence].
    rewrite HpoolFloor. exact Hcopied.
  - intros ofs Hoffset.
    assert (Mem.load Mint32 copied mb ofs = Mem.load Mint32 m mb ofs) as Hcopied.
    { apply HcopyFrame; [eapply ibcc_loaded_block_valid; exact Hobject|].
      right; right. destruct Hoffset as [<-|[<-|[<-|[]]]]; lia. }
    split; [exact Hcopied|].
    erewrite Mem.load_store_other; [|exact Hstore|right; right;
      destruct Hoffset as [<-|[<-|[<-|[]]]]; cbn [size_chunk]; lia].
    rewrite HcacheFloor by exact Hoffset. exact Hcopied.
Qed.

(** This names the actual preserved raw XYZ, cache type/count and all four
    cache pointers.  Equality is to the cache AT THE COPY CUT, not a claim
    that no earlier geometry/wall helper changed the detection cache. *)
Theorem ifct_taken_fallback_keeps_named_object_contact :
  forall version e le m mb ob slot values t le' after out,
  e ! IBM._vec3f_copy = None -> e ! IBM._find_floor = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gObjectPool = Some ob ->
  (slot < object_pool_capacity)%nat -> le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  (forall axis, Mem.load Mfloat32 m ob
    (object_slot_offset slot + 32 + 4 * icp_number axis) = Some (Vsingle (values axis))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' after out ->
  (forall axis, Mem.load Mfloat32 after ob (object_slot_offset slot + 160 + 4 * icp_number axis) =
    Mem.load Mfloat32 m ob (object_slot_offset slot + 160 + 4 * icp_number axis)) /\
  Mem.load Mint32 after ob (object_slot_offset slot + 112) =
    Mem.load Mint32 m ob (object_slot_offset slot + 112) /\
  Mem.load Mint16signed after ob (object_slot_offset slot + 118) =
    Mem.load Mint16signed m ob (object_slot_offset slot + 118) /\
  (forall index, (index < 4)%nat ->
    Mem.load Mint32 after ob (object_slot_offset slot + 120 + 4 * Z.of_nat index) =
    Mem.load Mint32 m ob (object_slot_offset slot + 120 + 4 * Z.of_nat index)).
Proof.
  intros version e le m mb ob slot values t le' after out
    Hcopy Hfloor Hstate Hpool Hslot Hm Hobject Hvalues Hretry.
  destruct (ifct_taken_fallback_transfers_display_and_preserves_contact version e le m mb ob slot
    values t le' after out Hcopy Hfloor Hstate Hpool Hslot Hm Hobject Hvalues Hretry)
    as (copied & query_m & copy_trace & result & height & _ & _ & _ & _ & _ & Hframe & _).
  repeat split; intros; apply (proj2 (Hframe _ _)).
Qed.

(** The first floor query has the same contact frame, independently of a
    successful or failed result.  Earlier wall/support corrections are not
    included in this query segment. *)
Theorem ifct_primary_query_preserves_contact :
  forall version e le m mb ob y t le' after out,
  e ! IBM._find_floor = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block m ob -> le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_geometry_query version) t le' after out ->
  t = E0 /\ out = Out_normal /\
  (forall chunk ofs, Mem.load chunk after ob ofs = Mem.load chunk m ob ofs) /\
  (forall ofs, ifct_state_contact_offset ofs ->
    Mem.load Mint32 after mb ofs = Mem.load Mint32 m mb ofs).
Proof.
  intros version e le m mb ob y t le' after out
    Hname Hstate Hpool Hob Hm Hy Hquery.
  destruct (ifh_primary_floor_query_uses_movement_y_and_stores_result
    version e le m mb y t le' after out Hname Hm Hy Hquery)
    as (x & z & floor & query_m & Hcall & Hstore & _ & _ & Hout).
  destruct (ifct_completed_floor_preserves_raw_and_contact version m mb ob
    (Vsingle x) (Vsingle y) (Vsingle z) t query_m (Vsingle floor)
    Hstate Hpool (ibcc_loaded_block_valid _ _ _ _ _ Hy) Hob Hcall)
    as (Ht & Hobject & Hcache).
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool) as Hsep.
  split; [exact Ht|]. split; [exact Hout|]. split.
  - intros chunk ofs. erewrite Mem.load_store_other; [apply Hobject|exact Hstore|left; congruence].
  - intros ofs Hoffset. erewrite Mem.load_store_other; [apply Hcache; exact Hoffset|exact Hstore|].
    right; right. destruct Hoffset as [<-|[<-|[<-|[]]]]; cbn [size_chunk]; lia.
Qed.

(** The signed-16 query conversion is LOCAL.  It is three Sset operations,
    not a write of truncated coordinates back to MarioState. *)
Definition ifct_floor_coordinate_casts version := ocn_prepend
  (firstn 3 (ocn_prefix_items 3 (rank12b_drop_sequences 2
    (fn_body (ueqr_native_body version UEQRFindFloor))))) Sskip.

Theorem ifct_floor_coordinate_casts_are_local : forall version,
  ifct_floor_coordinate_casts version =
  Ssequence (Sset IFL._x (Ecast (Ecast (Etempvar IFL._xPos tfloat) tshort) tshort))
    (Ssequence (Sset IFL._y (Ecast (Ecast (Etempvar IFL._yPos tfloat) tshort) tshort))
      (Ssequence (Sset IFL._z (Ecast (Ecast (Etempvar IFL._zPos tfloat) tshort) tshort)) Sskip)).
Proof. intros []; reflexivity. Qed.

Theorem ifct_completed_local_casts_do_not_write_position :
  forall version ge e le m t le' after out,
  ocn_exec ge e le m (ifct_floor_coordinate_casts version) t le' after out ->
  t = E0 /\ after = m /\ out = Out_normal.
Proof.
  intros version ge e le m t le' after out Hrun.
  rewrite ifct_floor_coordinate_casts_are_local in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec. all: try contradiction.
  repeat split; reflexivity.
Qed.

(** Control consequences are conditional on ACTUALLY TAKING the fallback.
    Incoming State Y is unrestricted: Original and Hybrid therefore inherit
    their displayed high Y, while Variant would lose its high State Y if it
    took this low-display retry.  A successful first query bypasses this
    branch; deciding that result needs the separate live-list geometry proof. *)
Theorem ifct_original_hybrid_taken_retry_uses_high_display :
  forall version e le m mb ob slot values t le' after out,
  e ! IBM._vec3f_copy = None -> e ! IBM._find_floor = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gObjectPool = Some ob ->
  (slot < object_pool_capacity)%nat -> le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  (forall axis, Mem.load Mfloat32 m ob
    (object_slot_offset slot + 32 + 4 * icp_number axis) = Some (Vsingle (values axis))) ->
  values ICPY = ivr_contact_height ->
  Mem.load Mfloat32 m ob (object_slot_offset slot + 164) = Some (Vsingle iqps_low_height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle ivr_contact_height) /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 164) = Some (Vsingle iqps_low_height) /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 36) = Some (Vsingle ivr_contact_height).
Proof.
  intros version e le m mb ob slot values t le' after out
    Hcopy Hfloor Hstate Hpool Hslot Hm Hobject Hvalues Hheight Hraw Hretry.
  destruct (ifct_taken_fallback_transfers_display_and_preserves_contact version e le m mb ob slot
    values t le' after out Hcopy Hfloor Hstate Hpool Hslot Hm Hobject Hvalues Hretry)
    as (copied & query_m & copy_trace & result & height & _ & _ & _ & _ & Hposition & Hframe & _).
  split; [exact (eq_trans (proj2 (Hposition ICPY)) (f_equal (fun h => Some (Vsingle h)) Hheight))|].
  split; [rewrite (proj2 (Hframe Mfloat32 (object_slot_offset slot + 164))); exact Hraw|].
  rewrite (proj2 (Hframe Mfloat32 (object_slot_offset slot + 36))).
  replace (object_slot_offset slot + 36) with
    (object_slot_offset slot + 32 + 4 * icp_number ICPY) by (cbn [icp_number]; lia).
  rewrite <- Hheight. exact (Hvalues ICPY).
Qed.

Theorem ifct_variant_taken_retry_uses_low_display :
  forall version e le m mb ob slot values t le' after out,
  e ! IBM._vec3f_copy = None -> e ! IBM._find_floor = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gObjectPool = Some ob ->
  (slot < object_pool_capacity)%nat -> le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  (forall axis, Mem.load Mfloat32 m ob
    (object_slot_offset slot + 32 + 4 * icp_number axis) = Some (Vsingle (values axis))) ->
  values ICPY = iqps_low_height ->
  Mem.load Mfloat32 m ob (object_slot_offset slot + 164) = Some (Vsingle iqps_low_height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle iqps_low_height) /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 164) = Some (Vsingle iqps_low_height) /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 36) = Some (Vsingle iqps_low_height).
Proof.
  intros version e le m mb ob slot values t le' after out
    Hcopy Hfloor Hstate Hpool Hslot Hm Hobject Hvalues Hheight Hraw Hretry.
  destruct (ifct_taken_fallback_transfers_display_and_preserves_contact version e le m mb ob slot
    values t le' after out Hcopy Hfloor Hstate Hpool Hslot Hm Hobject Hvalues Hretry)
    as (copied & query_m & copy_trace & result & height & _ & _ & _ & _ & Hposition & Hframe & _).
  split; [exact (eq_trans (proj2 (Hposition ICPY)) (f_equal (fun h => Some (Vsingle h)) Hheight))|].
  split; [rewrite (proj2 (Hframe Mfloat32 (object_slot_offset slot + 164))); exact Hraw|].
  rewrite (proj2 (Hframe Mfloat32 (object_slot_offset slot + 36))).
  replace (object_slot_offset slot + 36) with
    (object_slot_offset slot + 32 + 4 * icp_number ICPY) by (cbn [icp_number]; lia).
  rewrite <- Hheight. exact (Hvalues ICPY).
Qed.

Definition InkFallbackContactBoundary : Prop := InkTakenFallbackContactTransfer.
Theorem ifct_fallback_contact_boundary_checked : InkFallbackContactBoundary.
Proof. exact ifct_taken_fallback_transfers_display_and_preserves_contact. Qed.
