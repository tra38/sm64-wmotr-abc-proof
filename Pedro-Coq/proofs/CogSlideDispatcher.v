From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Ctypes Events Floats Globalenvs
  Integers Memory Values.
From Pedro.Generated Require Import us_mario us_mario_step us_audio_external.
From Pedro.Proofs Require Import GameTypes TTCCogExecution SlideKickDustExecution
  SoundRequestExecution SlideKickAnimationExecution CogActionExecution
  CogReflectionExecution CogSlideExecution CogMovingDispatcher.
Import ListNotations.
Open Scope Z_scope.

(** The full dispatcher consumes the two-helper slide theorem. Its cancellation
    and quicksand callees are executed, not retained as execution premises.
    Movement-helper, entry-image, allocation and next-frame gaps remain. *)
Definition cog_slide_dispatch_claim version : Prop :=
  forall ge before middle m0 m3 m4 mario object area floor speed flags sine yaw sin_value cos_value
    animation animation_end sliding ground reflection action sound speed_code floor_code moving_code
    list target frame loop_end table source base entries entry_offset size cache_code
    queue count index cancel_code quicksand_code slide_code (caller : slide_caller_layout ge),
    cog_dispatch_layout ge caller ->
    cog_dispatch_bindings version CogSlideCase ge cancel_code quicksand_code slide_code ->
    cog_dispatch_entry before mario floor CogSlideCase ->
    cog_quicksand_stores before middle m0 mario ->
    slide_bindings version ge animation animation_end sliding ground reflection action sound ->
    slide_animation_layout ge caller -> animation_cache_layout ge ->
    sound_request_layout ge -> cog_action_layout ge caller -> cog_reflection_layout ge caller ->
    Genv.find_symbol ge us_mario._load_patchable_table = Some cache_code ->
    Genv.find_funct_ptr ge cache_code = Some (Internal (animation_cache_function version)) ->
    Genv.find_symbol ge us_mario._gSineTable = Some sine ->
    Genv.find_symbol ge us_mario_step._mario_set_forward_vel = Some speed_code ->
    Genv.find_funct_ptr ge speed_code = Some (Internal (cog_speed_function version)) ->
    Genv.find_symbol ge us_mario._mario_get_floor_class = Some floor_code ->
    Genv.find_funct_ptr ge floor_code = Some (Internal (cog_floor_class_function version)) ->
    Genv.find_symbol ge us_mario._set_mario_action_moving = Some moving_code ->
    Genv.find_funct_ptr ge moving_code = Some (Internal (cog_moving_transition_function version)) ->
    Genv.find_symbol ge us_audio_external._sSoundRequests = Some queue ->
    Genv.find_symbol ge us_audio_external._sSoundRequestCount = Some count ->
    mario <> sine -> mario <> queue -> mario <> count ->
    area <> mario -> area <> queue -> area <> count ->
    floor <> mario -> floor <> queue -> floor <> count ->
    slide_animation_state_image m0 mario object list target frame loop_end ->
    slide_animation_cache_image m0 list table source base entries entry_offset size ->
    cog_slide_two_helper_path version ge m0 m3 m4 mario ->
    cog_slide_entry_image m4 mario object area floor speed flags ->
    cog_speed_image m4 mario sine yaw sin_value cos_value ->
    sound_request_memory_image m4 queue count index ->
    Mem.valid_access m4 Mint32 queue (sound_slot_offset (cog_next_sound_index index)) Writable ->
    Mem.valid_access m4 Mptr queue (sound_slot_offset (cog_next_sound_index index) + 4) Writable ->
    exists after,
      eval_funcall function_entry2 ge before (Internal (cog_dispatch_function version))
        [Vptr mario Ptrofs.zero] E0 after (Vint Int.zero) /\
      Mem.load Mint32 after mario 8 = Some (Vint (Int.repr 3)) /\
      Mem.load Mint16unsigned after mario 2 = Some (Vint (Int.repr 4)) /\
      Mem.load Mint32 after mario 12 = Some (Vint (Int.repr 132194)) /\
      slide_anchor after mario = slide_anchor before mario.

Theorem generated_cog_slide_complete_dispatch_us_jp :
  forall version, cog_slide_dispatch_claim version.
Proof.
  intros version ge before middle m0 m3 m4 mario object area floor speed flags
    sine yaw sin_value cos_value animation animation_end sliding ground reflection action
    sound speed_code floor_code moving_code list target frame loop_end table source base
    entries entry_offset size cache_code queue count index cancel_code quicksand_code
    slide_code caller Hdispatch Hdispatch_bindings Hentry Hquick
    Hbindings Hanimation_layout Hcache_layout Hsound_layout Haction_layout Hreflection_layout
    Hcache_symbol Hcache_code Hsine Hspeed_symbol Hspeed_code Hfloor_symbol Hfloor_code
    Hmoving_symbol Hmoving_code Hqueue Hcount Hmsine Hmqueue Hmcount Ha_m Ha_q Ha_c Hf_m Hf_q Hf_c
    Hanimation_image Hcache_image Htwo Himage Hspeed_image Hsound_image Hnext_bits Hnext_pos.
  destruct (generated_cog_slide_with_two_helpers_us_jp version ge m0 m3 m4 mario object
    area floor speed flags sine yaw sin_value cos_value animation animation_end sliding
    ground reflection action sound speed_code floor_code moving_code list target frame
    loop_end table source base entries entry_offset size cache_code queue count index caller
    Hbindings Hanimation_layout Hcache_layout Hsound_layout Haction_layout Hreflection_layout
    Hcache_symbol Hcache_code Hsine Hspeed_symbol Hspeed_code Hfloor_symbol Hfloor_code
    Hmoving_symbol Hmoving_code Hqueue Hcount Hmsine Hmqueue Hmcount Ha_m Ha_q Ha_c Hf_m Hf_q Hf_c
    Hanimation_image Hcache_image Htwo Himage Hspeed_image Hsound_image Hnext_bits Hnext_pos)
    as (m5 & m6 & m7 & m8 & after & Hcall & Hparticles & Hinput & Haction & Hanchors & Htail).
  exists after. split.
  - eapply generated_cog_complete_moving_dispatcher_us_jp with
      (case := CogSlideCase) (middle := middle) (ready := m0);
      try eassumption.
  - repeat apply conj; try assumption.
    pose proof (f_equal (fun states => List.last states []) Hanchors) as Hlast.
    cbn [map repeat List.last] in Hlast. rewrite Hlast.
    eapply cog_quicksand_preserves_anchor. exact Hquick.
Qed.
