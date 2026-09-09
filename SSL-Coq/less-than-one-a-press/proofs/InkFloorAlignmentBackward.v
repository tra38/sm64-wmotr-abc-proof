(** Floor alignment passes a retained-height question back to its entry floor.
    The matrix-building tail remains part of the same actual invocation. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkBackwardExecution InkCopyCaller InkFloorResetSource InkFloorResetExecution
  ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Local Open Scope Z_scope.

Definition InkFloorAlignmentHeightCut : Prop :=
  forall version m mb ob height t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle height) ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (imb_body version IMBAlign))
    [Vptr mb Ptrofs.zero] t m' result ->
  exists snap_le snap_m final_le out,
    Mem.store Mfloat32 m mb 64 (Vsingle height) = Some snap_m /\
    Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle height) /\
    (forall chunk ofs, Mem.load chunk snap_m ob ofs = Mem.load chunk m ob ofs) /\
    snap_le ! IMB._m = Some (Vptr mb Ptrofs.zero) /\
    ocn_exec ge empty_env snap_le snap_m (imb_align_tail version) t final_le m' out.

Theorem imb_alignment_copies_entry_floor_and_preserves_object : InkFloorAlignmentHeightCut.
Proof.
  unfold InkFloorAlignmentHeightCut.
  intros version m mb ob height t m' result HstateSymbol HpoolSymbol Hfloor Hcall.
  pose proof (ibcc_ordinary_storage_separate _ _ _ HstateSymbol HpoolSymbol) as Hdifferent.
  destruct (imb_source_cuts version) as (Hvars & Hparams & Hbody & _).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb Ptrofs.zero)) as Hm
      by (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; apply PTree.gss) end.
  assert (ibk_normal (ifr_snap version IFRStationary) = true) as Hnormal
    by (destruct version; reflexivity).
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hrun;
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
      as (snap_le & snap_m & pre & rest & Htrace & Hsnap & Htail) end.
  destruct (ifr_snap_writes_floor_height _ _ _ _ _ _ _ _ _ _ _ _ Hm Hfloor Hsnap)
    as (Hstore & Htemps & -> & _).
  change (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr 64))) with 64 in Hstore.
  match type of Htail with ocn_exec _ _ _ _ _ _ ?last_le _ ?out =>
    exists snap_le, snap_m, last_le, out end.
  split; [exact Hstore|]. split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  split.
  - intros. eapply Mem.load_store_other; [exact Hstore|left; congruence].
  - split.
    + rewrite Htemps, PTree.gso by discriminate. exact Hm.
    + cbn in Htrace. subst. exact Htail.
Qed.

(** This is a necessary entry condition, not a promise about the matrix tail.
    If a high display is retained at the snap, it was already that far above
    the sampled floor on entry. The snap itself never raises the display. *)
Corollary imb_alignment_snap_retains_only_the_entry_display :
  forall version m mb ob height t m' result object_offset displayed,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle height) ->
  Mem.load Mfloat32 m ob (object_offset + 36) = Some (Vsingle displayed) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (imb_body version IMBAlign)) [Vptr mb Ptrofs.zero] t m' result ->
  exists snap_m,
    Mem.store Mfloat32 m mb 64 (Vsingle height) = Some snap_m /\
    Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle height) /\
    Mem.load Mfloat32 snap_m ob (object_offset + 36) = Some (Vsingle displayed) /\
    Mem.load Mfloat32 snap_m ob (object_offset + 164) = Mem.load Mfloat32 m ob (object_offset + 164).
Proof.
  intros version m mb ob height t m' result object_offset displayed Hs Hp Hfloor Hdisplay Hcall.
  destruct (imb_alignment_copies_entry_floor_and_preserves_object _ _ _ _ _ _ _ _
    Hs Hp Hfloor Hcall) as (le & snap & last & out & Hstore & Hheight & Hframe & _).
  exists snap. split; [exact Hstore|]. split; [exact Hheight|].
  rewrite !Hframe. auto.
Qed.
