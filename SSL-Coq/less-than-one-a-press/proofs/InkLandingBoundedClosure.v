(** Extend the zero-timer result to every timer below four, and every ground
    result. Repeated sounds need no audio effect; first requests still do. *)
From Coq Require Import Bool Lia List Reals ZArith.
From compcert Require Import AST Clight ClightBigstep Ctypes Events Floats
  Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkMovingBackwardSource InkLandingOutcomeFrames InkLandingDispatch
  InkLandingContinuationSource InkLandingPostStep InkLandingHistoryGate
  InkAnimationTimerFrame InkAnimationLoaderFrame InkLandingSoundFrame InkLandingQuietSound
  InkLandingLateClosure InkFloorResetExecution InkMarioInputFlag
  ObjectContactNecessity JPBinary32DepthWrites SelectedClightTarget.
Import ListNotations.
Local Open Scope Z_scope.

Definition InkAllGroundOutcomeTimerBound : Prop :=
  forall version le m mb mo step timer ob oo lb lo ab ao t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> le ! IMB._stepResult = Some (Vint step) ->
  imf_room mo -> ilh_timer_load m mb mo = Some (Vint timer) -> Int.unsigned timer < 4 ->
  (Int.unsigned step = 2 -> InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao) ->
  InkAnimationTransferTimerEffect version mb mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Ssequence (ilc_dispatch version) (ilc_dust version)) t le' m' out ->
  exists next, ilh_timer_load m' mb mo = Some (Vint next) /\ Int.unsigned next < 4.

Theorem ilb_all_ground_outcomes_keep_a_small_timer : InkAllGroundOutcomeTimerBound.
Proof.
  intros version le m mb mo step timer ob oo lb lo ab ao t le' m' out
    Hm Hstep Hroom Htimer Hsmall Hdest Htransfer Hrun.
  destruct (ilc_split_dispatch _ _ _ _ _ _ _ _ _ _ Hrun)
    as (dust_le & dust_m & dispatch_t & dust_t & Htrace & Hdispatch & Hdust).
  pose proof (iof_all_dispatch_outcomes_reset_or_preserve_timer version le m mb mo step
    ob oo lb lo ab ao _ _ _ _ Hm Hstep Hdest Htransfer Hdispatch) as Hafter.
  destruct (ilc_dispatch_keeps_arguments _ _ _ _ _ _ _ _ _ Hdispatch) as [Hkeep _].
  assert (dust_le ! IMB._m = Some (Vptr mb mo)) as HdM by congruence.
  pose proof (ilp_dust_update_preserves_timer version empty_env dust_le dust_m mb mo
    _ _ _ _ HdM Hroom Hdust) as Hframe.
  destruct (Z.eq_dec (Int.unsigned step) 0).
  - exists Int.zero. split; [congruence|rewrite Int.unsigned_zero; lia].
  - exists timer. split; congruence.
Qed.

Definition ilb_sound_entry version mb mo sound_m : Prop :=
  InkAudioRequestTimerEffect version mb mo \/
  exists flags,
    Mem.load Mint32 sound_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 4))) =
      Some (Vint flags) /\ Int.and flags (Int.repr 65536) <> Int.zero.

Lemma ilb_actual_sound_timer_frame : forall version le m mb mo t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) -> imf_room mo -> ilb_sound_entry version mb mo m ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilc_sound version) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version le m mb mo t le' m' out Hm Hroom [Haudio|[flags [Hflags Hset]]] Hrun.
  - eapply ilt_actual_sound_call_frame; [exact Hm|exact Hroom|exact Haudio|exact Hrun].
  - destruct (iqs_actual_landing_call_has_no_request version le m mb mo flags t le' m' out
      Hm Hflags Hset Hrun) as [_ ->]. reflexivity.
Qed.

Definition InkBoundedLateLandingNegativeClosure : Prop :=
  forall version mb mo ob oo lb lo ab ao timer animation_le animation_m
    sound_le sound_m depth_le depth_m final_le final_m animation_t sound_t depth_t out depth after,
  animation_le ! IBM._m = Some (Vptr mb mo) -> imf_room mo ->
  ilh_timer_load animation_m mb mo = Some (Vint timer) -> Int.unsigned timer < 4 ->
  InkAnimationEntryDestinations animation_m mb mo ob oo lb lo ab ao ->
  InkAnimationTransferTimerEffect version mb mo -> ilb_sound_entry version mb mo sound_m ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env animation_le animation_m
    (ilc_animation version) animation_t sound_le sound_m Out_normal ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env sound_le sound_m
    (ilc_sound version) sound_t depth_le depth_m Out_normal ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env depth_le depth_m
    (ilc_after_sound version) depth_t final_le final_m out ->
  Mem.load Mfloat32 depth_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  Mem.load Mfloat32 final_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) ->
  JPBinary32FiniteNonnegative depth -> is_finite 24 128 after = true ->
  (B2R 24 128 after < 0)%R -> False.

Theorem ilb_small_timer_excludes_first_negative_final_depth : InkBoundedLateLandingNegativeClosure.
Proof.
  intros version mb mo ob oo lb lo ab ao timer animation_le animation_m sound_le sound_m
    depth_le depth_m final_le final_m animation_t sound_t depth_t out depth after
    Hm Hroom Htimer Hsmall Hdest Htransfer HsoundEntry Hanimation Hsound Hfinal
    Hdepth Hafter Hnonnegative Hfinite Hnegative.
  destruct (ilt_actual_call_shapes version) as (aa & sa & _ & _ & _ & _ & Hak & Hsk).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hanimation Hak) as HsoundM.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hsound Hsk) as HdepthM.
  assert (sound_le ! IBM._m = Some (Vptr mb mo)) as HsM by congruence.
  assert (depth_le ! IBM._m = Some (Vptr mb mo)) as HdM by congruence.
  pose proof (ilt_actual_animation_call_frame version animation_le animation_m mb mo ob oo lb lo ab ao
    _ _ _ _ Hm Hdest Htransfer Hanimation) as HaFrame.
  pose proof (ilb_actual_sound_timer_frame version sound_le sound_m mb mo _ _ _ _
    HsM Hroom HsoundEntry Hsound) as HsFrame.
  assert (ilh_timer_load depth_m mb mo = Some (Vint timer)) as HlateTimer by congruence.
  pose proof (ilp_actual_post_sound_negative_needs_late_timer version empty_env depth_le depth_m
    mb mo depth timer _ _ _ _ after HdM Hdepth HlateTimer Hfinal Hafter Hnonnegative Hfinite Hnegative)
    as Hlate. lia.
Qed.
