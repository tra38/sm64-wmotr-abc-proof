(** Conditional post-dialog reset, in the generated US/JP program.

    A completed ordinary ground call reaches the real display copy whatever
    happened in its quarter-step loop.  The complete copy forgets the old
    display, not merely at its Y store but also at its return.  If the later
    sink sees that reset height and the same movement height, nonnegative
    depth cannot recreate an upward gap.  The intervening read equalities
    are explicit obligations, not a claim that all gameplay paths preserve
    them.  In particular input geometry and platform displacement happen
    before ground movement; this result does not exclude their transport.
*)
From Coq Require Import List Reals ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Generated Require Import us_mario_actions_cutscene jp_mario_actions_cutscene.
From LessThanOneAPress.Proofs Require Import GameTypes InkCopyCompletion
  InkBackwardSource InkBackwardExecution InkCopyCaller InkGroundBackwardSource
  InkGroundDisplayBackward InkGroundCallBackward InkFloorResetSource
  InkQuicksandSource InkQuicksandStores InkQuicksandExecution InkQuicksandArithmetic
  OrdinaryArea1EntryMemory ObjectContactNecessity Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ipg_dialog_body version := match version with
| VersionUS => us_mario_actions_cutscene.f_act_reading_automatic_dialog
| VersionJP => jp_mario_actions_cutscene.f_act_reading_automatic_dialog end.
Definition ipg_dialog_prefix version := map
  (fun n => ibk_head (rank12b_drop_sequences n (fn_body (ipg_dialog_body version))))
  [0%nat; 1%nat; 2%nat; 3%nat].

Lemma ipg_dialog_return_source : forall version,
  fn_body (ipg_dialog_body version) = ocn_prepend (ipg_dialog_prefix version) rank12b_return_zero /\
  forallb ibk_normal (ipg_dialog_prefix version) = true /\
  fn_return (ipg_dialog_body version) = tint.
Proof. intros []; repeat split; reflexivity. Qed.

Definition InkAutomaticDialogReturnsFalse : Prop :=
  forall version ge m args t m' result,
  ClightBigstep.Clight2.eval_funcall ge m (Internal (ipg_dialog_body version)) args t m' result ->
  result = Vint Int.zero.

Theorem ipg_completed_dialog_returns_false : InkAutomaticDialogReturnsFalse.
Proof.
  unfold InkAutomaticDialogReturnsFalse.
  intros version ge m args t m' result Hcall.
  destruct (ipg_dialog_return_source version) as (Hshape & Hnormal & Htype).
  inversion Hcall; subst.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hshape in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (last_le & last_m & prefix & suffix & Htrace & Hprefix & Hreturn) end.
  pose proof (ocn_return_zero_outcome _ _ _ _ _ _ _ _ Hreturn) as Hout. subst.
  match goal with Hr : outcome_result_value _ _ _ _ |- _ =>
    rewrite Htype in Hr; inversion Hr; subst; try discriminate end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; reflexivity end.
Qed.

Definition InkGroundRefreshCompleted : Prop :=
  forall version e le m mb ob slot height t le' m' out,
  (slot < object_pool_capacity)%nat -> mb <> ob -> Mem.valid_block m ob ->
  e ! IFR._vec3f_copy = None -> le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (igb_refresh version) t le' m' out ->
  Mem.load Mfloat32 m' ob (object_slot_offset slot + 36) = Some (Vsingle height) /\
  (forall chunk b ofs, Mem.valid_block m b -> icp_outside_display ob slot chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs).

Theorem ipg_ground_refresh_completes_without_old_display : InkGroundRefreshCompleted.
Proof.
  unfold InkGroundRefreshCompleted.
  intros version e le m mb ob slot height t le' m' out Hslot Hsep Hvalid Hlocal Hm Hobj Hheight Hrun.
  destruct (igb_refresh_calls_selected_copy version e le m mb Ptrofs.zero ob
    (Ptrofs.repr (object_slot_offset slot)) t le' m' out Hlocal Hm Hobj Hrun)
    as (result & Hcall).
  eapply icp_completed_copy_forgets_old_display; eauto.
Qed.

(** Derive the completed copy checkpoint from ONE whole ground-step call.
    The quarter-step prefix is retained verbatim; neither its displacement
    nor its velocity is bounded or replaced with a sampled trajectory. *)
Definition InkGroundCompletedCopyCheckpoint : Prop :=
  forall version m mb t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (igb_body version))
    [Vptr mb Ptrofs.zero] t m' result ->
  exists e entry_le entry_m cut_le cut_m copy_le copy_m last_le last_m pre copy_t suffix out,
    t = pre ++ (copy_t ++ suffix) /\
    function_entry2 ge (igb_body version) [Vptr mb Ptrofs.zero] m e entry_le entry_m /\
    ocn_exec ge e entry_le entry_m (igb_prefix version) pre cut_le cut_m Out_normal /\
    ocn_exec ge e cut_le cut_m (igb_refresh version) copy_t copy_le copy_m Out_normal /\
    ocn_exec ge e copy_le copy_m (igb_tail version) suffix last_le last_m out /\
    outcome_result_value out (fn_return (igb_body version)) result last_m /\
    Mem.free_list last_m (blocks_of_env ge e) = Some m' /\
    (forall ob slot height, (slot < object_pool_capacity)%nat -> mb <> ob ->
      Mem.valid_block cut_m ob ->
      Mem.load Mint32 cut_m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
      Mem.load Mfloat32 cut_m mb 64 = Some (Vsingle height) ->
      Mem.load Mfloat32 copy_m ob (object_slot_offset slot + 36) = Some (Vsingle height)).

Theorem ipg_whole_ground_call_has_completed_copy_checkpoint : InkGroundCompletedCopyCheckpoint.
Proof.
  unfold InkGroundCompletedCopyCheckpoint.
  intros version m mb t m' result Hcall.
  destruct (igb_completed_ground_call_reaches_display_refresh version m mb Ptrofs.zero t m' result Hcall)
    as (e & entry_le & entry_m & cut_le & cut_m & copy_le & copy_m & last_le & last_m &
      pre & copy_t & suffix & out & Htrace & Hentry & Hprefix & Hm & Hlocal & Hcopy &
      Htail & Hresult & Hfree & Hcut).
  exists e, entry_le, entry_m, cut_le, cut_m, copy_le, copy_m, last_le, last_m,
    pre, copy_t, suffix, out.
  repeat match goal with |- _ /\ _ => split; [assumption|] end.
  intros ob slot height Hslot Hsep Hvalid Hobj Hheight.
  eapply (proj1 (ipg_ground_refresh_completes_without_old_display version e cut_le cut_m
    mb ob slot height copy_t copy_le copy_m Out_normal Hslot Hsep Hvalid Hlocal Hm Hobj Hheight Hcopy)).
Qed.

(** No bound on the incoming display or velocity occurs here.  The two
    read-continuity premises concern only the interval AFTER the completed
    refresh.  They must not be applied across the earlier missing-floor
    recovery, which can change movement height by copying the display. *)
Definition InkResetThenSinkNoUpwardGap : Prop :=
  forall version e le before mb ob slot height copy_t copy_le copied copy_out
    sink_start matrix depth sink_t after result,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block before ob -> e ! IFR._vec3f_copy = None ->
  le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 before mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 before mb 64 = Some (Vsingle height) ->
  ocn_exec ge e le before (igb_refresh version) copy_t copy_le copied copy_out ->
  Mem.load Mfloat32 sink_start ob (object_slot_offset slot + 36) =
    Mem.load Mfloat32 copied ob (object_slot_offset slot + 36) ->
  Mem.load Mfloat32 sink_start mb 64 = Mem.load Mfloat32 before mb 64 ->
  Mem.load Mint32 sink_start mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 sink_start ob (object_slot_offset slot + 80) = Some (iq_optional_pointer matrix) ->
  Mem.load Mfloat32 sink_start mb 192 = Some (Vsingle depth) ->
  iq_matrix_storage_separate mb ob slot matrix ->
  ClightBigstep.Clight2.eval_funcall ge sink_start (Internal (iq_body version))
    [Vptr mb Ptrofs.zero] sink_t after result ->
  is_finite 24 128 height = true -> is_finite 24 128 depth = true ->
  is_finite 24 128 (Float32.sub height depth) = true -> (0 <= B2R 24 128 depth)%R ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle height) /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 36) =
    Some (Vsingle (Float32.sub height depth)) /\
  (B2R 24 128 (Float32.sub height depth) <= B2R 24 128 height)%R.

Theorem ipg_reset_then_sink_cannot_retain_an_upward_gap : InkResetThenSinkNoUpwardGap.
Proof.
  unfold InkResetThenSinkNoUpwardGap.
  intros version e le before mb ob slot height copy_t copy_le copied copy_out
    sink_start matrix depth sink_t after result Hslot Hms Hop Hvalid Hlocal Hm Hobj Hheight
    Hcopy HdisplayInterval HmovementInterval HsinkObject Hmatrix Hdepth HmatrixSep Hsink
    Hfinite HdepthFinite HresultFinite Hnonnegative.
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hms Hop) as Hsep.
  destruct (ipg_ground_refresh_completes_without_old_display _ _ _ _ _ _ _ _ _ _ _ _
    Hslot Hsep Hvalid Hlocal Hm Hobj Hheight Hcopy) as [Hcopied HcopyFrame].
  assert (Mem.load Mfloat32 sink_start ob (object_slot_offset slot + 36) = Some (Vsingle height))
    as HsinkHeight by congruence.
  destruct (iq_completed_sink_has_exact_effect version sink_start mb ob slot matrix height depth
    sink_t after result Hslot Hms Hop HsinkObject Hmatrix Hdepth HsinkHeight HmatrixSep Hsink)
    as [Hfinal Hframe].
  split.
  - rewrite Hframe; [congruence|left; reflexivity|left; exact Hsep].
  - split; [exact Hfinal|]. eapply iq_nonnegative_subtraction_cannot_raise; eauto.
Qed.

Definition InkPostDialogGroundResetBoundary : Prop :=
  InkAutomaticDialogReturnsFalse /\ InkGroundCallRefreshCut /\ InkCopyCompletedEffect /\
  InkGroundRefreshCompleted /\ InkGroundCompletedCopyCheckpoint /\ InkResetThenSinkNoUpwardGap.

Theorem ipg_post_dialog_ground_reset_checked : InkPostDialogGroundResetBoundary.
Proof.
  split; [exact ipg_completed_dialog_returns_false|].
  split; [exact igb_completed_ground_call_reaches_display_refresh|].
  split; [exact icp_completed_copy_forgets_old_display|].
  split; [exact ipg_ground_refresh_completes_without_old_display|].
  split; [exact ipg_whole_ground_call_has_completed_copy_checkpoint|].
  exact ipg_reset_then_sink_cannot_retain_an_upward_gap.
Qed.
