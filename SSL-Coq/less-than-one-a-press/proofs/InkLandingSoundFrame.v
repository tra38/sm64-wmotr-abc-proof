(** The complete selected landing-sound chain. Only the final audio request
    needs an outside effect; the three Mario helpers are executed, not framed
    by name. The outside effect below is an explicit premise, not a theorem. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkLateHelperSource InkLateWriteFrame InkLateCallExecution InkMarioInputFlag
  InkLandingHistoryGate ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Inductive InkSoundHelper := ISParticles | ISAction | ISOnce.
Definition ils_helper kind := match kind with
| ISParticles => ILSoundParticles | ISAction => ILSoundAction | ISOnce => ILSoundOnce end.
Definition ils_lower_ok kind fn args := match kind with
| ISParticles => ilh_named IBM._play_sound ill_sound_type fn
| ISAction => ilh_named (ill_ident ILSoundParticles) ill_mario_sound_type fn && ilh_mario_head args
| ISOnce => ilh_named (ill_ident ILSoundAction) ill_mario_sound_type fn && ilh_mario_head args end.

Theorem ils_actual_sound_shapes : forall version kind,
  ilw_shape [IBM._m] ilw_sound_write (ils_lower_ok kind)
    (fn_body (ill_body version (ils_helper kind))) = true.
Proof. intros [] []; vm_compute; reflexivity. Qed.

Definition InkHelperTimerEffect version kind mb mo : Prop :=
  forall m args t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version kind)) (Vptr mb mo :: args) t m' result ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.

Definition InkAudioRequestTimerEffect version mb mo : Prop :=
  forall le m opt args t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Scall opt (Evar IBM._play_sound ill_sound_type) args) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.

Lemma ils_helper_from_lower_calls : forall version kind mb mo,
  imf_room mo ->
  (forall le m opt fn args t le' m' out,
    le ! IBM._m = Some (Vptr mb mo) -> ils_lower_ok kind fn args = true ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (Scall opt fn args) t le' m' out ->
    ilh_timer_load m' mb mo = ilh_timer_load m mb mo) ->
  InkHelperTimerEffect version (ils_helper kind) mb mo.
Proof.
  intros version kind mb mo Hroom Hlower m args t m' result Hcall.
  destruct (ilh_actual_helper_entry version (ils_helper kind) m mb mo args t m' result Hcall)
    as (entry_le & final_le & out & Hm & Hbody).
  assert (entry_le ! IBM._m = Some (Vptr mb mo)) as Hargument
    by (destruct kind; exact Hm).
  unshelve eapply (proj1 (ilw_checked_body_frame
    (Clight.globalenv (selected_clight_target version)) empty_env [IBM._m]
    (fun _ => Some (Vptr mb mo)) ilw_sound_write (ils_lower_ok kind) mb mo
    _ _ entry_le m _ t final_le m' out Hbody (ils_actual_sound_shapes version kind) _)).
  - intros le0 mem lhs rhs tr le1 mem1 outcome Hrefs Hallowed Hrun.
    exact (ilw_sound_write_frame version empty_env le0 mem mb mo lhs rhs tr le1 mem1 outcome
      (Hrefs IBM._m (or_introl eq_refl)) Hroom Hallowed Hrun).
  - intros le0 mem opt fn actual_args tr le1 mem1 outcome Hrefs Hallowed Hrun.
    exact (Hlower le0 mem opt fn actual_args tr le1 mem1 outcome
      (Hrefs IBM._m (or_introl eq_refl)) Hallowed Hrun).
  - intros id [Heq|Hbad]; [subst; exact Hargument|contradiction].
Qed.

Lemma ils_named_mario_helper_frame : forall version kind mb mo,
  InkHelperTimerEffect version kind mb mo ->
  forall le m opt fn args t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) ->
  ilh_named (ill_ident kind) ill_mario_sound_type fn = true -> ilh_mario_head args = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Scall opt fn args) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version kind mb mo Heffect le m opt fn args t le' m' out Hm Hname Hhead Hrun.
  apply ilh_named_exact in Hname. subst fn.
  destruct (ilh_mario_head_exact args Hhead) as [rest ->].
  destruct (ilh_actual_named_call version kind empty_env le m opt _
    [ill_mario_pointer; tuint; tuint] tvoid t le' m' out eq_refl Hrun)
    as (values & result & Hargs & Hcall).
  destruct (ilh_actual_mario_arguments _ _ _ _ _ _ _ mb mo Hm Hargs) as [other ->].
  eapply Heffect; exact Hcall.
Qed.

Theorem ils_particles_preserve_timer : forall version mb mo,
  imf_room mo -> InkAudioRequestTimerEffect version mb mo ->
  InkHelperTimerEffect version ILSoundParticles mb mo.
Proof.
  intros version mb mo Hroom Haudio.
  change (InkHelperTimerEffect version (ils_helper ISParticles) mb mo).
  apply ils_helper_from_lower_calls; [exact Hroom|].
  intros le m opt fn args t le' m' out Hm Hname Hrun.
  apply ilh_named_exact in Hname. subst fn. eapply Haudio; exact Hrun.
Qed.
Theorem ils_action_sound_preserves_timer : forall version mb mo,
  imf_room mo -> InkAudioRequestTimerEffect version mb mo ->
  InkHelperTimerEffect version ILSoundAction mb mo.
Proof.
  intros version mb mo Hroom Haudio.
  change (InkHelperTimerEffect version (ils_helper ISAction) mb mo).
  apply ils_helper_from_lower_calls; [exact Hroom|].
  intros le m opt fn args t le' m' out Hm Hshape Hrun.
  apply andb_true_iff in Hshape as [Hname Hhead].
  eapply ils_named_mario_helper_frame;
    [exact (ils_particles_preserve_timer version mb mo Hroom Haudio)
    |exact Hm|exact Hname|exact Hhead|exact Hrun].
Qed.

Definition InkLandingSoundCheckedFrame : Prop := forall version mb mo,
  imf_room mo -> InkAudioRequestTimerEffect version mb mo ->
  InkHelperTimerEffect version ILSoundOnce mb mo.
Theorem ils_landing_sound_chain_preserves_timer : InkLandingSoundCheckedFrame.
Proof.
  intros version mb mo Hroom Haudio.
  change (InkHelperTimerEffect version (ils_helper ISOnce) mb mo).
  apply ils_helper_from_lower_calls; [exact Hroom|].
  intros le m opt fn args t le' m' out Hm Hshape Hrun.
  apply andb_true_iff in Hshape as [Hname Hhead].
  eapply ils_named_mario_helper_frame;
    [exact (ils_action_sound_preserves_timer version mb mo Hroom Haudio)
    |exact Hm|exact Hname|exact Hhead|exact Hrun].
Qed.
