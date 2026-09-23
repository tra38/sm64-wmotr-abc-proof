(** The actual allocation-and-copy segment of spawn_particle. Allocation
    effects remain visible at their own cut; only the subsequent tail is
    framed. This is an execution connection, not a new whole-frame axiom. *)
From Coq Require Import List.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes
  Events Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import Area1PostCopyChildSource
  Area1PostCopyChildFrame Area1PostCopyChildCall InkBackwardExecution
  ContactConsumerExecution ObjectContactNecessity OrdinaryArea1EntryMemory
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition pcp_segment version := match fn_body (pcc_particle_body version) with
| Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence _ segment) _)) => segment
| _ => Sskip end.
Definition pcp_allocation version := match pcp_segment version with
| Ssequence (Ssequence allocation _) _ => allocation | _ => Sskip end.
Definition pcp_bind := Sset PCP._particle (Etempvar PCP._t'1 pcc_object).
Definition pcp_copy := Ssequence (Sset PCP._t'4 (Evar PCP._gCurrentObject pcc_object))
  (pcc_call PCCBoth PCP._particle PCP._t'4).

Lemma pcp_generated_segment : forall version,
  pcp_segment version = Ssequence (Ssequence (pcp_allocation version) pcp_bind) pcp_copy /\
  pcc_particle_tail = Ssequence pcp_bind pcp_copy /\
  ibk_normal (pcp_allocation version) = true /\ ibk_normal pcp_bind = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma pcp_allocation_returns_to_temp : forall version le m t le' after out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (pcp_allocation version) t le' after out ->
  exists child, le' ! PCP._t'1 = Some child.
Proof.
  intros version le m t le' after out Hrun.
  assert (exists load fn args, pcp_allocation version =
    Ssequence load (Scall (Some PCP._t'1) fn args) /\ ibk_normal load = true) as Hshape
    by (destruct version; do 3 eexists; split; reflexivity).
  destruct Hshape as (load & fn & args & Hshape & Hnormal).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ load _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suffix & Htrace & Hload & Hcall).
  inversion Hcall; subst. eexists; apply PTree.gss.
Qed.

Definition PostCopyParticleExecutionCut : Prop :=
  forall version le m t le' after out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (pcp_segment version) t le' after out ->
  exists allocated_le allocated_m child pre suffix,
    t = pre ++ suffix /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (pcp_allocation version) pre allocated_le allocated_m Out_normal /\
    allocated_le ! PCP._t'1 = Some child /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env allocated_le allocated_m
      pcc_particle_tail suffix le' after out /\
    (forall ob slot, (slot < object_pool_capacity)%nat ->
      child = Vptr ob (Ptrofs.repr (object_slot_offset slot)) ->
      pcc_frame ob slot allocated_m after).

Theorem pcp_actual_spawn_segment_has_framed_copy_tail : PostCopyParticleExecutionCut.
Proof.
  intros version le m t le' after out Hrun.
  destruct (pcp_generated_segment version) as (Hsegment & Htail & HallocNormal & HbindNormal).
  rewrite Hsegment in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Ssequence (pcp_allocation version) pcp_bind) _ _ _ _ _
    ltac:(cbn [ibk_normal]; rewrite HallocNormal, HbindNormal; reflexivity) Hrun)
    as (copied_le & copied_m & before_copy & copy_trace & Htrace & HbeforeCopy & Hcopy).
  destruct (ibk_split_sequence _ _ _ _ (pcp_allocation version) _ _ _ _ _ HallocNormal HbeforeCopy)
    as (allocated_le & allocated_m & pre & bind_trace & Hprefix & Hallocation & Hbind).
  destruct (pcp_allocation_returns_to_temp _ _ _ _ _ _ _ Hallocation) as (child & Hreturn).
  assert (ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env allocated_le allocated_m
    pcc_particle_tail (bind_trace ++ copy_trace) le' after out) as HtailRun.
  { rewrite Htail. eapply exec_Sseq_1; eauto. }
  exists allocated_le, allocated_m, child, pre, (bind_trace ++ copy_trace).
  split; [rewrite Htrace, Hprefix; symmetry; apply app_assoc|].
  split; [exact Hallocation|]. split; [exact Hreturn|]. split; [exact HtailRun|].
  intros ob slot Hslot E. subst child.
  eapply pcc_particle_returned_child_tail_frame; eauto.
Qed.

Definition Area1PostCopyParticleCheckedBoundary : Prop :=
  Area1PostCopyChildCheckedBoundary /\ PostCopyParticleExecutionCut.

Theorem area1_postcopy_particle_checked_boundary_holds : Area1PostCopyParticleCheckedBoundary.
Proof.
  split; [exact area1_postcopy_child_checked_boundary_holds|].
  exact pcp_actual_spawn_segment_has_framed_copy_tail.
Qed.
