(** A whole selected sink invocation, including either matrix branch. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkQuicksandSource
  InkQuicksandExpressions InkQuicksandStores InkBackwardSource InkBackwardExecution
  InkCopyCaller InkFloorResetExecution InkRawCopyStores OrdinaryArea1EntryMemory
  ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iq_matrix_stage version := Ssequence (Sset IQ._t'3 iq_matrix)
  (Sifthenelse (Etempvar IQ._t'3 iq_matrix_type) (iq_matrix_branch version) Sskip).

Theorem iq_actual_matrix_stage_frame :
  forall version e le m mb ob slot matrix t le' m' out,
  (slot < object_pool_capacity)%nat ->
  le ! IQ._o = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 m ob (object_slot_offset slot + 80) = Some (iq_optional_pointer matrix) ->
  iq_matrix_storage_separate mb ob slot matrix ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iq_matrix_stage version) t le' m' out ->
  iq_matrix_frame mb ob slot m m'.
Proof.
  intros version e le m mb ob slot matrix t le' m' out Hslot Ho Hq Hseparate Hrun.
  assert (Mem.load Mint32 m ob (Ptrofs.unsigned
    (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 80))) =
    Some (iq_optional_pointer matrix)) as HqAddress.
  { rewrite irc_slot_address by (auto; lia). exact Hq. }
  destruct (ibk_split_sequence _ _ _ _ (Sset IQ._t'3 iq_matrix) _ _ _ _ _ eq_refl Hrun)
    as (guard_le & guard_m & pre & rest & Htrace & Hread & Hbranch).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ iq_matrix ?value |- _ =>
    pose proof (iq_matrix_read _ _ _ _ _ _ _ _ Ho HqAddress Hr) as Hvalue; subst value end.
  inversion Hbranch; subst.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IQ._t'3 _) ?value |- _ =>
    assert (value = iq_optional_pointer matrix) by
      (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst value end.
  destruct matrix as [[qb qo]|].
  - match goal with Hb : bool_val (iq_optional_pointer _) _ ?memory = Some ?choice |- _ =>
      change ((if Mem.weak_valid_pointer memory qb (Ptrofs.unsigned qo)
        then Some true else None) = Some choice) in Hb;
      destruct (Mem.weak_valid_pointer memory qb (Ptrofs.unsigned qo));
        inversion Hb; subst end.
    lazymatch goal with Hcase : ClightBigstep.exec_stmt _ _ ?env ?temps ?memory
      (iq_matrix_branch _) ?tr ?last_le ?last_m ?last_out |- _ =>
      destruct (iq_matrix_branch_actual_store version env temps memory ob
        (Ptrofs.repr (object_slot_offset slot)) qb qo tr last_le last_m last_out
        ltac:(rewrite PTree.gso by discriminate; exact Ho) HqAddress Hcase)
        as (written & Hstore & _) end.
    exact (iq_matrix_store_frame _ _ _ _ _ _ _ _ Hseparate Hstore).
  - match goal with Hb : bool_val (iq_optional_pointer _) _ _ = Some ?choice |- _ =>
      change (Some false = Some choice) in Hb; inversion Hb; subst end.
    match goal with Hcase : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hcase; subst end.
    intros chunk b ofs _. reflexivity.
Qed.

Definition iq_outside_display (ob : block) slot chunk b ofs : Prop :=
  b <> ob \/ ofs + size_chunk chunk <= object_slot_offset slot + 36 \/
    object_slot_offset slot + 40 <= ofs.

Definition InkQuicksandCallEffect : Prop :=
  forall version m mb ob slot matrix height depth t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 m ob (object_slot_offset slot + 80) = Some (iq_optional_pointer matrix) ->
  Mem.load Mfloat32 m mb 192 = Some (Vsingle depth) ->
  Mem.load Mfloat32 m ob (object_slot_offset slot + 36) = Some (Vsingle height) ->
  iq_matrix_storage_separate mb ob slot matrix ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (iq_body version))
    [Vptr mb Ptrofs.zero] t m' result ->
  Mem.load Mfloat32 m' ob (object_slot_offset slot + 36) =
    Some (Vsingle (Float32.sub height depth)) /\
  (forall chunk b ofs,
    iq_protected_read mb ob slot chunk b ofs -> iq_outside_display ob slot chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs).

Theorem iq_completed_sink_has_exact_effect : InkQuicksandCallEffect.
Proof.
  unfold InkQuicksandCallEffect.
  intros version m mb ob slot matrix height depth t m' result Hslot
    HstateSymbol HpoolSymbol Hobject Hmatrix Hdepth Hheight HmatrixSeparate Hcall.
  pose proof (ibcc_ordinary_storage_separate _ _ _ HstateSymbol HpoolSymbol) as Hseparate.
  destruct (iq_generated_cuts version) as (Hvars & Hparams & Hbody & _).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IQ._m = Some (Vptr mb Ptrofs.zero)) as Hm
      by (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; apply PTree.gss) end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hrun;
    destruct (ibk_split_sequence _ _ _ _ (Sset IQ._o ibk_object_read) _ _ _ _ _ eq_refl Hrun)
      as (cache_le & cache_m & cache_trace & rest_trace & Htrace & Hcache & Hrest) end.
  inversion Hcache; subst; clear Hcache.
  match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?value |- _ =>
    assert (value = Vptr ob (Ptrofs.repr (object_slot_offset slot))) by
      (eapply ibcc_actual_object_read; [exact Hm|exact Hobject|exact Hr]); subst value end.
  assert (ibk_normal (iq_matrix_stage version) = true) as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (display_le & display_m & matrix_trace & display_trace & HrestTrace & HmatrixRun & HdisplayRun).
  pose proof (iq_actual_matrix_stage_frame _ _ _ _ _ _ _ _ _ _ _ _ Hslot
    (PTree.gss _ _ _) Hmatrix HmatrixSeparate HmatrixRun) as Hframe.
  assert (display_le ! IQ._m = Some (Vptr mb Ptrofs.zero)) as HdisplayM.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IQ._m HmatrixRun
      ltac:(destruct version; reflexivity)).
    rewrite PTree.gso by discriminate. exact Hm. }
  assert (display_le ! IQ._o = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HdisplayO.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IQ._o HmatrixRun
      ltac:(destruct version; reflexivity)). apply PTree.gss. }
  assert (Mem.load Mfloat32 display_m mb 192 = Some (Vsingle depth)) as HdepthNow.
  { rewrite Hframe; [exact Hdepth|left; reflexivity]. }
  assert (Mem.load Mfloat32 display_m ob (Ptrofs.unsigned
    (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 36))) = Some (Vsingle height))
    as HheightNow.
  { rewrite irc_slot_address by (auto; lia).
    rewrite Hframe; [exact Hheight|right; repeat split; cbn [size_chunk]; lia]. }
  destruct (iq_display_tail_actual_store _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HdisplayM HdisplayO HdepthNow HheightNow HdisplayRun) as (Hstore & _).
  rewrite irc_slot_address in Hstore by (auto; lia).
  split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  intros chunk b ofs Hprotected Houtside.
  rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore chunk b ofs).
  - apply Hframe. exact Hprotected.
  - unfold iq_outside_display in Houtside. cbn [size_chunk]. lia.
Qed.
