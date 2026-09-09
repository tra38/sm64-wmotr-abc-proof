(** A backward condition on a completed real sink call. This does not assert
    that every live entry supplies ordinary storage or nonnegative depth. *)
From Coq Require Import Lia Reals.
From compcert Require Import AST Clight ClightBigstep Ctypes Floats Globalenvs
  Integers Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InkQuicksandSource
  InkQuicksandStores InkQuicksandExecution InkQuicksandArithmetic
  InkRawCopyHeight InkCopyCaller OrdinaryArea1EntryMemory SelectedClightTarget.
Local Open Scope Z_scope.

Definition InkQuicksandBackwardCut : Prop :=
  forall version m mb ob slot matrix height depth t m' result after,
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
    (Vptr mb Ptrofs.zero :: nil) t m' result ->
  Mem.load Mfloat32 m' ob (object_slot_offset slot + 36) = Some (Vsingle after) ->
  is_finite 24 128 height = true -> is_finite 24 128 depth = true ->
  is_finite 24 128 after = true ->
  (forall chunk ofs, Mem.load chunk m' mb ofs = Mem.load chunk m mb ofs) /\
  Mem.load Mfloat32 m' ob (object_slot_offset slot + 164) =
    Mem.load Mfloat32 m ob (object_slot_offset slot + 164) /\
  ((0 <= B2R 24 128 depth)%R -> (B2R 24 128 after <= B2R 24 128 height)%R) /\
  ((B2R 24 128 height < B2R 24 128 after)%R -> (B2R 24 128 depth < 0)%R).

Theorem iq_actual_sink_raise_requires_negative_depth : InkQuicksandBackwardCut.
Proof.
  unfold InkQuicksandBackwardCut.
  intros version m mb ob slot matrix height depth t m' result after Hslot
    HstateSymbol HpoolSymbol Hobject Hmatrix Hdepth Hheight HmatrixSeparate
    Hcall Hafter HheightFinite HdepthFinite HafterFinite.
  pose proof (ibcc_ordinary_storage_separate _ _ _ HstateSymbol HpoolSymbol) as Hseparate.
  destruct (iq_completed_sink_has_exact_effect version m mb ob slot matrix
    height depth t m' result Hslot HstateSymbol HpoolSymbol Hobject Hmatrix
    Hdepth Hheight HmatrixSeparate Hcall) as [Hexact Hframe].
  rewrite Hexact in Hafter. inversion Hafter; subst after.
  split.
  - intros chunk ofs. apply Hframe; [left; reflexivity|left; exact Hseparate].
  - split.
    + apply Hframe.
      * right; repeat split; cbn [size_chunk]; lia.
      * right; right; lia.
    + split.
      * apply iq_nonnegative_subtraction_cannot_raise; assumption.
      * apply iq_finite_raise_requires_negative_depth; assumption.
Qed.

Definition InkQuicksandCheckedBoundary : Prop :=
  InkRawCopyCheckedBoundary /\
  (forall version, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      IQ._sink_mario_in_quicksand = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (iq_body version))) /\
  InkQuicksandCallEffect /\ InkQuicksandBackwardCut.

Theorem iq_quicksand_boundary_checked : InkQuicksandCheckedBoundary.
Proof.
  split; [exact irc_raw_copy_boundary_checked|].
  split; [exact iq_selected_body_resolves|].
  split; [exact iq_completed_sink_has_exact_effect|].
  exact iq_actual_sink_raise_requires_negative_depth.
Qed.
