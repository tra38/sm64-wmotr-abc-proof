(** The ordinary scalar update and floor tests after landing dispatch cannot
    supply a late timer. Animation and sound effects are not assumed away. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InkLandingContinuationSource
  InkLandingHistoryGate InkLandingExecution InkMovingBackwardSource
  InkBackwardSource InkBackwardExecution InkCopyCaller InkFloorResetExecution
  InkControllerEdge InkMarioInputFlag InkQuicksandSource
  ObjectContactNecessity ContactConsumerExecution EyerokRank15LiveMovement
  JPBinary32DepthWrites SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma ilp_particle_field : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IMB._MarioState IMB._particleFlags 8 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IMB._MarioState IMB._particleFlags 8 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Lemma ilp_particle_store_preserves_timer : forall version e le m mb mo rhs t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> imf_room mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign ilc_dust_field rhs) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version e le m mb mo rhs t le' m' out Hm Hroom Hrun.
  inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue ?ge ?env ?temps ?memory _ _ _ _ |- _ =>
    destruct (ice_field_location ge env temps memory IMB._m IMB._MarioState
      IMB._particleFlags tuint mb mo 8 _ _ _ Hm (ilp_particle_field version) Hl)
      as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  unfold ilh_timer_load. eapply Mem.load_store_other; [eassumption|].
  right. right. cbn [size_chunk]. rewrite !imf_address by (auto; lia). lia.
Qed.

Theorem ilp_dust_update_preserves_timer : forall version e le m mb mo t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> imf_room mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilc_dust version) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version e le m mb mo t le' m' out Hm Hroom Hrun.
  destruct (ilc_dust_source version) as [test Hsource]. rewrite Hsource in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: try reflexivity.
  all: lazymatch goal with Hwrite : ClightBigstep.exec_stmt _ _ ?env ?temps ?memory ilc_dust_write _ _ _ _ |- _ =>
    unfold ilc_dust_write in Hwrite;
    eapply (ilp_particle_store_preserves_timer version env temps memory mb mo);
      [repeat rewrite PTree.gso by discriminate; exact Hm|exact Hroom|exact Hwrite]
  end.
Qed.

Definition InkLandingDepthGateCut : Prop :=
  forall version ge e le m t le' m' out,
  ocn_exec ge e le m (ilc_depth_gate version) t le' m' out ->
  (m' = m /\ t = E0 /\ out = Out_normal) \/
  exists write_le,
    write_le ! IMB._m = le ! IMB._m /\
    ocn_exec ge e write_le m (imb_landing_write version) t le' m' out.

Theorem ilp_floor_test_reaches_write_or_preserves_memory : InkLandingDepthGateCut.
Proof.
  unfold InkLandingDepthGateCut.
  intros version ge e le m t le' m' out Hrun.
  destruct (ilc_source_cuts version)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hgate & HreadOnly & Hnormal & _).
  rewrite Hgate in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (test_le & test_m & pre & rest & Htrace & Hprobe & Hbranch).
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hprobe HreadOnly)
    as (-> & -> & Hm).
  cbn in Htrace. subst t.
  inversion Hbranch; subst. destruct b.
  - right. exists test_le. split; assumption.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hr; subst end.
    left. repeat split; reflexivity.
Qed.

Definition InkPostSoundNegativeDepthCut : Prop :=
  forall version e le m mb mo depth timer t le' m' out after,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) =
    Some (Vsingle depth) -> ilh_timer_load m mb mo = Some (Vint timer) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilc_after_sound version) t le' m' out ->
  Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) =
    Some (Vsingle after) ->
  JPBinary32FiniteNonnegative depth -> is_finite 24 128 after = true ->
  (B2R 24 128 after < 0)%R -> 4 <= Int.unsigned timer.

Theorem ilp_actual_post_sound_negative_needs_late_timer : InkPostSoundNegativeDepthCut.
Proof.
  unfold InkPostSoundNegativeDepthCut.
  intros version e le m mb mo depth timer t le' m' out after
    Hm Hdepth Htimer Hrun Hafter Hnonnegative Hfinite Hnegative.
  destruct (ilc_source_cuts version)
    as (_ & _ & _ & _ & _ & _ & _ & _ & HafterSound & _ & _ & _ & Hnormals & _).
  assert (ibk_normal (ilc_depth_gate version) = true) as Hnormal
    by (destruct version; reflexivity).
  rewrite HafterSound in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (return_le & return_m & gate_t & return_t & Htrace & Hgate & Hreturn).
  assert (cce_readonly_keep IMB._m ilc_return = true) as HreturnReadOnly by reflexivity.
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hreturn HreturnReadOnly)
    as (_ & -> & _).
  destruct (ilp_floor_test_reaches_write_or_preserves_memory _ _ _ _ _ _ _ _ _ Hgate)
    as [(-> & _)|[write_le [Hsame Hwrite]]].
  - rewrite Hdepth in Hafter. inversion Hafter; subst.
    destruct Hnonnegative as [_ Hpositive]. lra.
  - eapply imb_actual_first_negative_landing_needs_late_timer;
      [rewrite Hsame; exact Hm|exact Hdepth|exact Htimer|exact Hwrite
      |exact Hafter|exact Hnonnegative|exact Hfinite|exact Hnegative].
Qed.
