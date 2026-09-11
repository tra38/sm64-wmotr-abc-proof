(** Join the completed retry copy to the proved effects of its actual
    second floor call and floorHeight store. The final MarioState position
    is now derived, not left behind an unknown callee-memory effect.
    A found floor, its owner, and a clean producer remain unproved. *)
From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Ctypes Events Floats
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkCopyCaller InkCopyCompletion InkRetryCompletion InkRetryQuery
  InkFloorCallEffects InkFloorHistorySource InkFloorHistoryQuery
  OrdinaryArea1EntryMemory ObjectContactNecessity
  UpperElevatorQueryResolution SelectedClightTarget.
Import ListNotations.
Local Open Scope Z_scope.

(** The first lookup cannot manufacture the actual-position side of the
    mismatch either. Wall corrections precede this statement and remain a
    separate predecessor obligation. *)
Definition InkPrimaryQueryPositionFrame : Prop :=
  forall version e le m mb y t le' m' out,
  e ! IBM._find_floor = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_geometry_query version) t le' m' out ->
  t = E0 /\ out = Out_normal /\ forall axis,
    Mem.load Mfloat32 m' mb (60 + 4 * icp_number axis) =
      Mem.load Mfloat32 m mb (60 + 4 * icp_number axis).

Theorem ircq_first_query_preserves_actual_position : InkPrimaryQueryPositionFrame.
Proof.
  intros version e le m mb y t le' m' out Hlocal Hsymbol Hm Hy Hrun.
  destruct (ifh_primary_floor_query_uses_movement_y_and_stores_result
    version e le m mb y t le' m' out Hlocal Hm Hy Hrun)
    as (x & z & floor & query_m & Hcall & Hstore & _ & _ & Hout).
  destruct (ifc_floor_call_preserves_mario_position version m mb
    (Vsingle x) (Vsingle y) (Vsingle z) t query_m (Vsingle floor)
    Hsymbol (ibcc_loaded_block_valid _ _ _ _ _ Hy) Hcall) as (Ht & Hframe).
  split; [exact Ht|]. split; [exact Hout|]. intros axis.
  erewrite Mem.load_store_other; [|exact Hstore|
    right; left; destruct axis; cbn [icp_number size_chunk]; lia].
  apply Hframe. destruct axis; cbn [icp_number]; lia.
Qed.

Definition InkRetryCompletedQueryPosition : Prop :=
  forall version e le m mb ob slot values t le' m' out,
  e ! IBM._vec3f_copy = None -> e ! IBM._find_floor = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  (slot < object_pool_capacity)%nat ->
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  (forall axis, Mem.load Mfloat32 m ob (object_slot_offset slot + 32 + 4 * icp_number axis) =
    Some (Vsingle (values axis))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' m' out ->
  exists copied query_m copy_trace result floor,
    t = copy_trace /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ibk_copy_body version))
      [Vptr mb (Ptrofs.repr 60); Vptr ob (Ptrofs.repr (object_slot_offset slot + 32))]
      copy_trace copied result /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      copied (Internal (ueqr_native_body version UEQRFindFloor))
      [Vsingle (values ICPX); Vsingle (values ICPY); Vsingle (values ICPZ);
       Vptr mb (Ptrofs.repr 104)] E0 query_m (Vsingle floor) /\
    Mem.store Mfloat32 query_m mb 112 (Vsingle floor) = Some m' /\
    (forall axis, Mem.load Mfloat32 m' mb (60 + 4 * icp_number axis) =
      Some (Vsingle (values axis))) /\ out = Out_normal.

Theorem ircq_retry_finishes_at_the_copied_display : InkRetryCompletedQueryPosition.
Proof.
  intros version e le m mb ob slot values t le' m' out
    HcopyLocal HfloorLocal Hmsym Hosym Hslot Hm Hobj Hvalues Hretry.
  destruct (irq_retry_connects_display_to_real_floor_call version e le m mb ob slot values
    t le' m' out HcopyLocal HfloorLocal Hmsym Hosym Hslot Hm Hobj Hvalues Hretry)
    as (copied & query_m & copy_trace & query_trace & result & floor &
      Htrace & Hcopy & Hposition & Hfloor & Hstore & _ & Hout).
  destruct (ifc_floor_call_preserves_mario_position version copied mb
    (Vsingle (values ICPX)) (Vsingle (values ICPY)) (Vsingle (values ICPZ))
    query_trace query_m (Vsingle floor) Hmsym
    (ibcc_loaded_block_valid _ _ _ _ _ (Hposition ICPX)) Hfloor)
    as (Hquiet & Hframe).
  subst query_trace. rewrite app_nil_r in Htrace.
  exists copied, query_m, copy_trace, result, floor.
  repeat apply conj; try assumption.
  intros axis.
  erewrite Mem.load_store_other; [|exact Hstore|
    right; left; destruct axis; cbn [icp_number size_chunk]; lia].
  rewrite Hframe by (destruct axis; cbn [icp_number]; lia).
  exact (Hposition axis).
Qed.
