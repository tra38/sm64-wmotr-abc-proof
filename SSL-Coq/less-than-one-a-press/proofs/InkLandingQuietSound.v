(** A repeated landing sound does not reach the abstract audio request.
    This is a branch-specific execution result, not an audio effect premise. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkLateHelperSource InkLateCallExecution InkLateWriteFrame
  InkControllerEdge InkCopyCaller InkFloorResetExecution InkLandingContinuationSource
  InkLandingLateClosure ObjectContactNecessity ContactConsumerExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition iqs_guard := Eunop Onotbool
  (Ebinop Oand (Etempvar IBM._t'1 tuint) (Econst_int (Int.repr 65536) tint) tuint) tint.

Lemma iqs_set_flag_disables_guard : forall ge e le m flags answer,
  le ! IBM._t'1 = Some (Vint flags) ->
  Int.and flags (Int.repr 65536) <> Int.zero ->
  eval_expr ge e le m iqs_guard answer -> answer = Vint Int.zero.
Proof.
  intros ge e le m flags answer Hflag Hset Hr.
  unfold iqs_guard in Hr. inversion Hr; subst.
  2: match goal with Hbad : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion Hbad end.
  match goal with Hbin : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hbin; subst; clear Hbin end.
  2: match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
  match goal with Htemp : eval_expr _ _ _ _ (Etempvar IBM._t'1 _) ?v |- _ =>
    assert (v = Vint flags) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hconst : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hconst; subst end.
  lazymatch goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some ?value |- _ =>
    change (Some (Vint (Int.and flags (Int.repr 65536))) = Some value) in Hsem;
    inversion Hsem; subst end.
  pose proof (Int.eq_false _ _ Hset) as Hneq.
  lazymatch goal with Hsem : sem_unary_operation _ _ _ _ = Some _ |- _ =>
    change (Some (Val.of_bool (negb (negb (Int.eq (Int.and flags (Int.repr 65536)) Int.zero)))) = Some answer) in Hsem;
    rewrite Hneq in Hsem; inversion Hsem; reflexivity end.
Qed.

Lemma iqs_action_source : forall version, exists active,
  fn_body (ill_body version ILSoundAction) =
    Ssequence (Sset IBM._t'1 ilw_flags) (Sifthenelse iqs_guard active Sskip).
Proof. intros []; eexists; reflexivity. Qed.

Lemma iqs_action_sound_already_played : forall version m mb mo flags args t m' result,
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 4))) = Some (Vint flags) ->
  Int.and flags (Int.repr 65536) <> Int.zero ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version ILSoundAction)) (Vptr mb mo :: args) t m' result ->
  t = E0 /\ m' = m.
Proof.
  intros version m mb mo flags args t m' result Hflags Hset Hcall.
  destruct (ilh_actual_helper_entry version ILSoundAction m mb mo args t m' result Hcall)
    as (entry_le & final_le & out & Hm & Hbody).
  destruct (iqs_action_source version) as [active Hsource]. rewrite Hsource in Hbody.
  destruct (ibk_split_sequence _ _ _ _ (Sset IBM._t'1 ilw_flags) _ _ _ _ _ eq_refl Hbody)
    as (guard_le & guard_m & pre & suf & Htrace & Hread & Hbranch).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ ilw_flags ?v |- _ =>
    assert (v = Vint flags) by (eapply ice_field_read with (ty := tuint);
      [exact Hm|exact (ilw_flags_field version)|reflexivity|exact Hflags|exact Hr]); subst v end.
  inversion Hbranch; subst.
  match goal with Hr : eval_expr _ _ _ _ iqs_guard ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply iqs_set_flag_disables_guard;
      [apply PTree.gss|exact Hset|exact Hr]); subst v end.
  match goal with Hb : bool_val (Vint Int.zero) _ _ = Some ?choice |- _ =>
    change (Some false = Some choice) in Hb; inversion Hb; subst end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
    inversion Hr; subst end.
  split; reflexivity.
Qed.

Definition InkRepeatedLandingSoundNoEffect : Prop :=
  forall version m mb mo flags args t m' result,
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 4))) = Some (Vint flags) ->
  Int.and flags (Int.repr 65536) <> Int.zero ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version ILSoundOnce)) (Vptr mb mo :: args) t m' result ->
  t = E0 /\ m' = m.

Theorem iqs_repeated_landing_sound_has_no_request : InkRepeatedLandingSoundNoEffect.
Proof.
  intros version m mb mo flags args t m' result Hflags Hset Hcall.
  destruct (ilh_actual_helper_entry version ILSoundOnce m mb mo args t m' result Hcall)
    as (entry_le & final_le & out & Hm & Hbody).
  assert (exists prefix actual_args,
    fn_body (ill_body version ILSoundOnce) = Ssequence prefix
      (Scall None (Evar (ill_ident ILSoundAction) ill_mario_sound_type) actual_args) /\
    ibk_normal prefix = true /\ cce_readonly_keep IBM._m prefix = true /\
    ilh_mario_head actual_args = true) as (prefix & actual_args & Hsource & Hnormal & Hreadonly & Hhead)
    by (destruct version; do 2 eexists; repeat split; reflexivity).
  rewrite Hsource in Hbody.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hbody)
    as (call_le & call_m & pre & suf & Htrace & Hprefix & Hlower).
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hprefix Hreadonly) as (-> & -> & Hkeep).
  destruct (ilh_actual_named_call version ILSoundAction empty_env call_le _ None actual_args
    [ill_mario_pointer; tuint; tuint] tvoid suf final_le m' out eq_refl Hlower)
    as (values & answer & Hargs & Haction).
  destruct (ilh_mario_head_exact actual_args Hhead) as [rest ->].
  assert (call_le ! IBM._m = Some (Vptr mb mo)) as HcallM by (rewrite Hkeep; exact Hm).
  destruct (ilh_actual_mario_arguments _ _ _ _ _ _ _ mb mo HcallM Hargs) as [other ->].
  destruct (iqs_action_sound_already_played version _ mb mo flags other _ _ _ Hflags Hset Haction)
    as [-> ->]. split; [exact Htrace|reflexivity].
Qed.

Corollary iqs_actual_landing_call_has_no_request : forall version le m mb mo flags t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 4))) = Some (Vint flags) ->
  Int.and flags (Int.repr 65536) <> Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilc_sound version) t le' m' out -> t = E0 /\ m' = m.
Proof.
  intros version le m mb mo flags t le' m' out Hm Hflags Hset Hrun.
  destruct (ilt_actual_call_shapes version) as (aa & sa & _ & _ & Hshape & Hhead & _).
  rewrite Hshape in Hrun.
  destruct (ilh_actual_named_call version ILSoundOnce empty_env le m None sa
    [ill_mario_pointer; tuint] tvoid t le' m' out eq_refl Hrun)
    as (values & result & Hargs & Hcall).
  destruct (ilh_mario_head_exact sa Hhead) as [rest ->].
  destruct (ilh_actual_mario_arguments _ _ _ _ _ _ _ mb mo Hm Hargs) as [other ->].
  eapply iqs_repeated_landing_sound_has_no_request; [exact Hflags|exact Hset|exact Hcall].
Qed.
