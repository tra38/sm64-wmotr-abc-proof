(** Connect the real animation and sound frames to the same later landing
    interval. This closes that calculation under explicit ordinary-storage
    and runtime effects, not the whole no-A negative-depth history. *)
From Coq Require Import Bool Lia List Reals ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes Events Floats
  Globalenvs Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkMovingBackwardSource InkLateHelperSource InkLateCallExecution InkAnimationTimerFrame
  InkAnimationLoaderFrame InkLandingSoundFrame InkLandingContinuationSource
  InkLandingHistoryGate InkLandingPostStep InkFloorResetExecution InkMarioInputFlag
  ObjectContactNecessity JPBinary32DepthWrites SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Lemma ilt_actual_call_shapes : forall version, exists animation_args sound_args,
  ilc_animation version = Scall None (Evar (ill_ident ILAnimation)
    (Tfunction [ill_mario_pointer; tint] tshort cc_default)) animation_args /\
  ilh_mario_head animation_args = true /\
  ilc_sound version = Scall None (Evar (ill_ident ILSoundOnce)
    (Tfunction [ill_mario_pointer; tuint] tvoid cc_default)) sound_args /\
  ilh_mario_head sound_args = true /\
  ifr_keeps_temp IBM._m (ilc_animation version) = true /\
  ifr_keeps_temp IBM._m (ilc_sound version) = true.
Proof. intros []; do 2 eexists; repeat split; reflexivity. Qed.

Lemma ilt_actual_animation_call_frame : forall version le m mb mo ob oo lb lo ab ao t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) ->
  InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao ->
  InkAnimationTransferTimerEffect version mb mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilc_animation version) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version le m mb mo ob oo lb lo ab ao t le' m' out Hm Hdest Htransfer Hrun.
  destruct (ilt_actual_call_shapes version) as (aa & sa & Hshape & Hhead & _).
  rewrite Hshape in Hrun.
  destruct (ilh_actual_named_call version ILAnimation empty_env le m None aa
    [ill_mario_pointer; tint] tshort t le' m' out eq_refl Hrun)
    as (values & result & Hargs & Hcall).
  destruct (ilh_mario_head_exact aa Hhead) as [rest ->].
  destruct (ilh_actual_mario_arguments _ _ _ _ _ _ _ mb mo Hm Hargs) as [other ->].
  eapply iaf_actual_animation_preserves_timer; [exact Htransfer|exact Hdest|exact Hcall].
Qed.

Lemma ilt_actual_sound_call_frame : forall version le m mb mo t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) -> imf_room mo ->
  InkAudioRequestTimerEffect version mb mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilc_sound version) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version le m mb mo t le' m' out Hm Hroom Haudio Hrun.
  destruct (ilt_actual_call_shapes version) as (aa & sa & _ & _ & Hshape & Hhead & _).
  rewrite Hshape in Hrun.
  destruct (ilh_actual_named_call version ILSoundOnce empty_env le m None sa
    [ill_mario_pointer; tuint] tvoid t le' m' out eq_refl Hrun)
    as (values & result & Hargs & Hcall).
  destruct (ilh_mario_head_exact sa Hhead) as [rest ->].
  destruct (ilh_actual_mario_arguments _ _ _ _ _ _ _ mb mo Hm Hargs) as [other ->].
  exact (ils_landing_sound_chain_preserves_timer version mb mo Hroom Haudio _ _ _ _ _ Hcall).
Qed.

Definition InkLateLandingNegativeClosure : Prop :=
  forall version mb mo ob oo lb lo ab ao animation_le animation_m
    sound_le sound_m depth_le depth_m final_le final_m animation_t sound_t depth_t out depth after,
  animation_le ! IBM._m = Some (Vptr mb mo) -> imf_room mo ->
  ilh_timer_load animation_m mb mo = Some (Vint Int.zero) ->
  InkAnimationEntryDestinations animation_m mb mo ob oo lb lo ab ao ->
  InkAnimationTransferTimerEffect version mb mo -> InkAudioRequestTimerEffect version mb mo ->
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

Theorem ilt_checked_late_calls_exclude_first_negative_final_depth : InkLateLandingNegativeClosure.
Proof.
  intros version mb mo ob oo lb lo ab ao animation_le animation_m sound_le sound_m
    depth_le depth_m final_le final_m animation_t sound_t depth_t out depth after
    Hm Hroom Hzero Hdest Htransfer Haudio Hanimation Hsound Hfinal Hdepth Hafter Hnonnegative Hfinite Hnegative.
  destruct (ilt_actual_call_shapes version) as (aa & sa & _ & _ & _ & _ & Hak & Hsk).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hanimation Hak) as HsoundM.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hsound Hsk) as HdepthM.
  assert (sound_le ! IBM._m = Some (Vptr mb mo)) as HsM by congruence.
  assert (depth_le ! IBM._m = Some (Vptr mb mo)) as HdM by congruence.
  pose proof (ilt_actual_animation_call_frame version animation_le animation_m mb mo ob oo lb lo ab ao
    _ _ _ _ Hm Hdest Htransfer Hanimation) as HaFrame.
  pose proof (ilt_actual_sound_call_frame version sound_le sound_m mb mo _ _ _ _
    HsM Hroom Haudio Hsound) as HsFrame.
  assert (ilh_timer_load depth_m mb mo = Some (Vint Int.zero)) as Htimer by congruence.
  pose proof (ilp_actual_post_sound_negative_needs_late_timer version empty_env depth_le depth_m
    mb mo depth Int.zero _ _ _ _ after HdM Hdepth Htimer Hfinal Hafter Hnonnegative Hfinite Hnegative)
    as Hlate.
  rewrite Int.unsigned_zero in Hlate. lia.
Qed.
