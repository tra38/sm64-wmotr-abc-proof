(** One completed landing invocation, with the actual left-ground continuation.
    A first negative final depth needs a later timer change in one of the two
    named calls. Their real effects are retained, not replaced by safe frames. *)
From Coq Require Import Classical_Prop Lia List Reals ZArith.
From compcert Require Import AST Clight ClightBigstep Ctypes Events Floats
  Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InkActionTimerReset
  InkLandingContinuationSource InkLandingDispatch InkLandingPostStep
  InkLandingHistoryGate InkMovingBackwardSource InkBackwardExecution
  InkFloorResetExecution InkMarioInputFlag ObjectContactNecessity
  JPBinary32DepthWrites SelectedClightTarget.
Import ListNotations.
Local Open Scope Z_scope.

Definition ilf_late_interval version e mb mo ground_le ground_m t final_le final_m out : Prop :=
  let ge := Clight.globalenv (selected_clight_target version) in
  exists dispatch_le dispatch_m animation_le animation_m sound_le sound_m depth_le depth_m
    dispatch_t dust_t animation_t sound_t depth_t,
    t = dispatch_t ++ (dust_t ++ (animation_t ++ (sound_t ++ depth_t))) /\
    ocn_exec ge e ground_le ground_m (ilc_dispatch version)
      dispatch_t dispatch_le dispatch_m Out_normal /\
    ocn_exec ge e dispatch_le dispatch_m (ilc_dust version)
      dust_t animation_le animation_m Out_normal /\
    ocn_exec ge e animation_le animation_m (ilc_animation version)
      animation_t sound_le sound_m Out_normal /\
    ocn_exec ge e sound_le sound_m (ilc_sound version)
      sound_t depth_le depth_m Out_normal /\
    ocn_exec ge e depth_le depth_m (ilc_after_sound version)
      depth_t final_le final_m out /\
    animation_le ! IMB._m = Some (Vptr mb mo) /\
    sound_le ! IMB._m = Some (Vptr mb mo) /\
    depth_le ! IMB._m = Some (Vptr mb mo) /\
    ilh_timer_load animation_m mb mo = Some (Vint Int.zero) /\
    (forall depth timer after,
      Mem.load Mfloat32 depth_m mb
        (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
      ilh_timer_load depth_m mb mo = Some (Vint timer) ->
      Mem.load Mfloat32 final_m mb
        (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) ->
      JPBinary32FiniteNonnegative depth -> is_finite 24 128 after = true ->
      (B2R 24 128 after < 0)%R ->
      4 <= Int.unsigned timer /\
      (ilh_timer_load sound_m mb mo <> ilh_timer_load animation_m mb mo \/
       ilh_timer_load depth_m mb mo <> ilh_timer_load sound_m mb mo)).

Definition InkLeftGroundTimerFrontier : Prop :=
  forall version e le m mb mo t le' m' out,
  e ! IMB._set_mario_action = None -> le ! IMB._m = Some (Vptr mb mo) ->
  le ! IMB._stepResult = Some (Vint Int.zero) -> imf_room mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilc_after_ground version) t le' m' out ->
  ilf_late_interval version e mb mo le m t le' m' out.

Theorem ilf_actual_left_ground_isolates_two_later_calls : InkLeftGroundTimerFrontier.
Proof.
  unfold InkLeftGroundTimerFrontier.
  intros version e le m mb mo t le' m' out Hlocal Hm Hground Hroom Hrun.
  destruct (ilc_source_cuts version)
    as (_ & _ & _ & _ & _ & HafterGround & _ & HafterDispatch & _).
  rewrite HafterGround in Hrun.
  destruct (ilc_split_dispatch _ _ _ _ _ _ _ _ _ _ Hrun)
    as (dispatch_le & dispatch_m & dispatch_t & tail_t & Htrace & Hdispatch & Htail).
  pose proof (ilc_left_ground_dispatch_resets_timer version e le m mb mo
    _ _ _ _ Hlocal Hm Hground Hdispatch) as Hreset.
  destruct (ilc_dispatch_keeps_arguments _ _ _ _ _ _ _ _ _ Hdispatch)
    as [HdispatchM _].
  assert (dispatch_le ! IMB._m = Some (Vptr mb mo)) as HdM by congruence.
  assert (ibk_normal (ilc_dust version) = true /\
    ibk_normal (ilc_animation version) = true /\
    ibk_normal (ilc_sound version) = true) as (Hdn & Han & Hsn)
    by (destruct version; repeat split; reflexivity).
  assert (ifr_keeps_temp IMB._m (ilc_dust version) = true /\
    ifr_keeps_temp IMB._m (ilc_animation version) = true /\
    ifr_keeps_temp IMB._m (ilc_sound version) = true) as (Hdk & Hak & Hsk)
    by (destruct version; repeat split; reflexivity).
  rewrite HafterDispatch in Htail.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hdn Htail)
    as (animation_le & animation_m & dust_t & calls_t & Hdtrace & Hdust & Hcalls).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Han Hcalls)
    as (sound_le & sound_m & animation_t & last_t & Hatrace & Hanimation & Hlast).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hsn Hlast)
    as (depth_le & depth_m & sound_t & depth_t & Hstrace & Hsound & HdepthRun).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hdust Hdk) as HaM.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hanimation Hak) as HsM.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hsound Hsk) as HdepthM.
  assert (animation_le ! IMB._m = Some (Vptr mb mo)) as HanimationM by congruence.
  assert (sound_le ! IMB._m = Some (Vptr mb mo)) as HsoundM by congruence.
  assert (depth_le ! IMB._m = Some (Vptr mb mo)) as HdepthArgument by congruence.
  pose proof (ilp_dust_update_preserves_timer version e dispatch_le dispatch_m mb mo
    _ _ _ _ HdM Hroom Hdust) as HdustFrame.
  assert (ilh_timer_load animation_m mb mo = Some (Vint Int.zero)) as Hzero
    by congruence.
  unfold ilf_late_interval.
  exists dispatch_le, dispatch_m, animation_le, animation_m, sound_le, sound_m,
    depth_le, depth_m, dispatch_t, dust_t, animation_t, sound_t, depth_t.
  repeat apply conj; try assumption; try congruence.
  intros depth timer after Hdepth Htimer Hafter Hnonnegative Hfinite Hnegative.
  pose proof (ilp_actual_post_sound_negative_needs_late_timer version e depth_le depth_m
    mb mo depth timer _ _ _ _ after HdepthArgument Hdepth Htimer HdepthRun
    Hafter Hnonnegative Hfinite Hnegative) as Hlate.
  split; [exact Hlate|].
  destruct (classic (ilh_timer_load sound_m mb mo = ilh_timer_load animation_m mb mo))
    as [HanimationFrame|HanimationChange].
  - right. intro HsoundFrame.
    rewrite HsoundFrame, HanimationFrame, Hzero in Htimer.
    inversion Htimer; subst. rewrite Int.unsigned_zero in Hlate. lia.
  - left. exact HanimationChange.
Qed.

(** The branch condition is on the checkpoint reached by this same invocation.
    No endpoint is imported from a separate execution. *)
Definition InkCompletedLandingTimerFrontier : Prop :=
  forall version m mb mo animation airAction t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (imb_body version IMBLanding))
    [Vptr mb mo; animation; airAction] t m' result ->
  exists entry_le ground_le ground_m final_le prefix suffix out,
    t = prefix ++ suffix /\
    function_entry2 ge (imb_body version IMBLanding)
      [Vptr mb mo; animation; airAction] m empty_env entry_le m /\
    ocn_exec ge empty_env entry_le m (ocn_prepend (ilc_prefix version) Sskip)
      prefix ground_le ground_m Out_normal /\
    ground_le ! IMB._m = Some (Vptr mb mo) /\
    ocn_exec ge empty_env ground_le ground_m (ilc_after_ground version)
      suffix final_le m' out /\
    outcome_result_value out (fn_return (imb_body version IMBLanding)) result m' /\
    (ground_le ! IMB._stepResult = Some (Vint Int.zero) -> imf_room mo ->
      ilf_late_interval version empty_env mb mo ground_le ground_m suffix final_le m' out).

Theorem ilf_completed_landing_has_same_run_timer_frontier : InkCompletedLandingTimerFrontier.
Proof.
  unfold InkCompletedLandingTimerFrontier.
  intros version m mb mo animation airAction t m' result Hcall.
  destruct (ilc_completed_landing_call_reaches_ground_result version m mb mo
    animation airAction t m' result Hcall)
    as (entry_le & ground_le & ground_m & final_le & prefix & suffix & out &
      Htrace & Hentry & Hprefix & Hm & Hsuffix & Hreturn).
  exists entry_le, ground_le, ground_m, final_le, prefix, suffix, out.
  repeat apply conj; try assumption.
  intros Hground Hroom.
  eapply ilf_actual_left_ground_isolates_two_later_calls;
    [reflexivity|exact Hm|exact Hground|exact Hroom|exact Hsuffix].
Qed.
