(** Connect the bounded copy writes to the actual reached calls and the
    post-allocation particle tail. This deliberately starts after allocation:
    it neither assumes nor claims a frame for spawn_object_at_origin. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor jp_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes Area1PostCopyChildSource
  Area1PostCopyChildFrame InkBackwardExecution InkFloorResetExecution
  ObjectContactNecessity SecretContactExecution ContactConsumerExecution
  OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition pcc_call kind dst src := Scall None (Evar (pcc_ident kind) pcc_type)
  [Etempvar dst pcc_object; Etempvar src pcc_object].

Lemma pcc_call_resolves : forall version kind e le m dst src target t le' after out,
  e ! (pcc_ident kind) = None -> le ! dst = Some target ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (pcc_call kind dst src) t le' after out ->
  exists source result,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (pcc_body version kind)) [target; source] t after result.
Proof.
  intros version kind e le m dst src target t le' after out Hlocal Hdst Hrun.
  unfold pcc_call, pcc_type in Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (pcc_selected_helpers_resolve version kind) as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar ?id (Tfunction ?tys ?ret ?cc)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory id tys ret cc fb vf Hlocal Hsymbol Hr)); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hargs : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Hargs; subst; clear Hargs end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar dst _) ?value |- _ =>
    assert (value = target) by (eapply ocn_temp_value; eauto); subst value end.
  repeat match goal with Hcast : sem_cast _ pcc_object pcc_object _ = Some _ |- _ =>
    unfold pcc_object in Hcast; destruct target; cbn in Hcast; try discriminate end.
  all: repeat match goal with Hcast : sem_cast ?v _ _ _ = Some _ |- _ =>
    destruct v; cbn in Hcast; try discriminate; inversion Hcast; subst; clear Hcast end.
  all: eauto.
Qed.

Lemma pcc_both_body : forall version,
  fn_body (pcc_body version PCCBoth) = Ssequence
    (pcc_call PCCPosition PCC._dst PCC._src) (pcc_call PCCAngle PCC._dst PCC._src).
Proof. intros []; reflexivity. Qed.

Theorem pcc_complete_copy_frame : forall version kind m ob slot src t after result,
  (slot < object_pool_capacity)%nat ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (pcc_body version kind))
    [Vptr ob (Ptrofs.repr (object_slot_offset slot)); src] t after result ->
  pcc_frame ob slot m after.
Proof.
  intros version kind m ob slot src t after result Hslot Hcall. destruct kind.
  - exact (pcc_leaf_call_frames_other_slots version false _ _ _ _ _ _ _ Hslot Hcall).
  - exact (pcc_leaf_call_frames_other_slots version true _ _ _ _ _ _ _ Hslot Hcall).
  - destruct (pcc_call_entry _ _ _ _ _ _ _ _ Hcall)
      as (le & final & out & Hdst & Hsrc & Hrun).
    rewrite pcc_both_body in Hrun.
    destruct (ibk_split_sequence _ _ _ _ (pcc_call PCCPosition PCC._dst PCC._src)
      _ _ _ _ _ eq_refl Hrun)
      as (middle & memory & pre & suf & Htrace & Hfirst & Hlast).
    destruct (pcc_call_resolves _ _ _ _ _ _ _ _ _ _ _ _ (PTree.gempty _ _) Hdst Hfirst)
      as (first_source & first_result & HfirstCall).
    pose proof (pcc_leaf_call_frames_other_slots version false _ _ _ _ _ _ _ Hslot HfirstCall) as HfirstFrame.
    assert (middle ! PCC._dst = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as Hmiddle.
    { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hfirst eq_refl). exact Hdst. }
    destruct (pcc_call_resolves _ _ _ _ _ _ _ _ _ _ _ _ (PTree.gempty _ _) Hmiddle Hlast)
      as (last_source & last_result & HlastCall).
    pose proof (pcc_leaf_call_frames_other_slots version true _ _ _ _ _ _ _ Hslot HlastCall) as HlastFrame.
    intros chunk b offset Houtside. rewrite HlastFrame, HfirstFrame; auto.
Qed.

Lemma pcc_distinct_slot_frame : forall ob child mario before after,
  child <> mario -> pcc_frame ob child before after ->
  forall chunk offset, 0 <= offset -> offset + size_chunk chunk <= object_size ->
  Mem.load chunk after ob (object_slot_offset mario + offset) =
    Mem.load chunk before ob (object_slot_offset mario + offset).
Proof.
  intros ob child mario before after Hdistinct Hframe chunk offset Hlo Hhi.
  apply Hframe. unfold pcc_outside.
  destruct (distinct_object_slot_intervals_are_disjoint child mario Hdistinct);
    unfold object_size in *; [right; right; lia|right; left; lia].
Qed.

(** This is the exact suffix after the allocator call returns and before its
    result is assigned to [particle]. Its grouping is checked against the
    actual generated taken branch below. The caller's later reload of
    gCurrentObject supplies only the source, so it needs no preservation
    assumption for this result. *)
Module PCP := us_object_list_processor.
Definition pcc_particle_tail := Ssequence
  (Sset PCP._particle (Etempvar PCP._t'1 pcc_object))
  (Ssequence (Sset PCP._t'4 (Evar PCP._gCurrentObject pcc_object))
    (pcc_call PCCBoth PCP._particle PCP._t'4)).
Definition pcc_particle_body version := match version with
| VersionUS => us_object_list_processor.f_spawn_particle
| VersionJP => jp_object_list_processor.f_spawn_particle end.

Lemma pcc_particle_generated_cut : forall version,
  exists initial flags test flag_write allocate,
  fn_body (pcc_particle_body version) =
    Ssequence initial (Ssequence flags (Sifthenelse test
      (Ssequence flag_write (Ssequence
        (Ssequence allocate (Sset PCP._particle (Etempvar PCP._t'1 pcc_object)))
        (Ssequence (Sset PCP._t'4 (Evar PCP._gCurrentObject pcc_object))
          (pcc_call PCCBoth PCP._particle PCP._t'4)))) Sskip)).
Proof. intros []; do 5 eexists; reflexivity. Qed.

Theorem pcc_particle_returned_child_tail_frame : forall version le m ob child t le' after out,
  (child < object_pool_capacity)%nat ->
  le ! PCP._t'1 = Some (Vptr ob (Ptrofs.repr (object_slot_offset child))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    pcc_particle_tail t le' after out ->
  pcc_frame ob child m after.
Proof.
  intros version le m ob child t le' after out Hchild Hreturn Hrun.
  unfold pcc_particle_tail, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ (Etempvar PCP._t'1 _) ?value |- _ =>
    assert (value = Vptr ob (Ptrofs.repr (object_slot_offset child)))
      by (eapply ocn_temp_value; eauto); subst value end.
  all: match goal with Hcopy : ClightBigstep.exec_stmt _ _ _ ?temps _ (pcc_call _ _ _) _ _ _ _ |- _ =>
    assert (temps ! PCP._particle = Some (Vptr ob (Ptrofs.repr (object_slot_offset child)))) as Htarget
      by (rewrite PTree.gso by discriminate; apply PTree.gss);
    destruct (pcc_call_resolves _ _ _ _ _ _ _ _ _ _ _ _ (PTree.gempty _ _) Htarget Hcopy)
      as (src & result & Hcall) end.
  all: eapply pcc_complete_copy_frame; eauto.
Qed.

Definition Area1PostCopyChildCheckedBoundary : Prop :=
  (forall version kind m ob child src t after result,
    (child < object_pool_capacity)%nat ->
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (pcc_body version kind))
      [Vptr ob (Ptrofs.repr (object_slot_offset child)); src] t after result ->
    pcc_frame ob child m after) /\
  (forall version le m ob child mario mb t le' after out,
    (child < object_pool_capacity)%nat -> (mario < object_pool_capacity)%nat ->
    child <> mario -> mb <> ob ->
    le ! PCP._t'1 = Some (Vptr ob (Ptrofs.repr (object_slot_offset child))) ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      pcc_particle_tail t le' after out ->
    (forall chunk offset, Mem.load chunk after mb offset = Mem.load chunk m mb offset) /\
    (forall chunk offset, 0 <= offset -> offset + size_chunk chunk <= object_size ->
      Mem.load chunk after ob (object_slot_offset mario + offset) =
      Mem.load chunk m ob (object_slot_offset mario + offset))).

Theorem area1_postcopy_child_checked_boundary_holds : Area1PostCopyChildCheckedBoundary.
Proof.
  split; [exact pcc_complete_copy_frame|].
  intros version le m ob child mario mb t le' after out Hchild Hmario Hdistinct Hstate Hreturn Hrun.
  pose proof (pcc_particle_returned_child_tail_frame _ _ _ _ _ _ _ _ _ Hchild Hreturn Hrun) as Hframe.
  split.
  - intros chunk offset. apply Hframe. left; exact Hstate.
  - eapply pcc_distinct_slot_frame; eauto.
Qed.
