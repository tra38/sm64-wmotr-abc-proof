(** Quantitative consequences of the ACTUAL selected US/JP sink callee.

    The exact negative-depth example makes the Original display height in
    one call.  The smaller -4 example exceeds that height after 293 calls
    when no intervening display refresh occurs.  These are supplied-depth
    transfer tests, not constructions of either depth or a dialog history.

    [iqps_invocations] is a sequence of real, completed callee invocations
    with consecutive memories.  Applying it across full Mario updates
    still requires deriving the intervening calls' relevant frame effects.
    In particular this does not assume that dialog waiting supplies the
    failed first floor lookup, the low collision position or usable timing.
*)
From Coq Require Import Lia List Reals Lra ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes Floats Globalenvs
  Integers Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InputSemantics InkQuicksandSource
  InkQuicksandStores InkQuicksandExecution InkCopyCaller
  InkQuicksandArithmetic InkStockSeedConditional JPBinary32DepthWrites
  InkVerticalRetryGeometry OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iqps_low_height := Float32.of_bits (Int.repr 1145044992).
Definition iqps_exact_negative_depth := Float32.of_bits (Int.repr 3297926061).
Definition iqps_small_negative_depth := Float32.of_bits (Int.repr 3229614080).

(** Float equality is reconstructed from bits rather than expanding the
    complete Flocq terms in a conversion proof. *)
Lemma iqps_exact_negative_depth_hits_checked_top :
  Float32.sub iqps_low_height iqps_exact_negative_depth = ivr_contact_height.
Proof.
  assert (Int.unsigned (Float32.to_bits
    (Float32.sub iqps_low_height iqps_exact_negative_depth)) = 1156733869)
    as Hbits by (vm_compute; reflexivity).
  apply (f_equal Int.repr) in Hbits. rewrite Int.repr_unsigned in Hbits.
  rewrite <- (Float32.of_to_bits
    (Float32.sub iqps_low_height iqps_exact_negative_depth)), Hbits.
  reflexivity.
Qed.

Fixpoint iqps_retained_sink_height (count : nat) (height depth : float32) : float32 :=
  match count with
  | O => height
  | S rest => iqps_retained_sink_height rest (Float32.sub height depth) depth
  end.

(** Every edge is the real callee at the same selected version and receiver.
    This deliberately describes no gameplay scheduler or action history. *)
Inductive iqps_invocations (version : GameVersion) (mb : block) :
    nat -> mem -> mem -> Prop :=
| IQPSZero : forall m, iqps_invocations version mb O m m
| IQPSNext : forall count before middle after trace result,
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version))
      before (Internal (iq_body version)) [Vptr mb Ptrofs.zero]
      trace middle result ->
    iqps_invocations version mb count middle after ->
    iqps_invocations version mb (S count) before after.

Definition InkRetainedSinkExactEffect : Prop :=
  forall version count before after mb ob slot matrix height depth,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.load Mint32 before mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 before ob (object_slot_offset slot + 80) = Some (iq_optional_pointer matrix) ->
  Mem.load Mfloat32 before mb 192 = Some (Vsingle depth) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 36) = Some (Vsingle height) ->
  iq_matrix_storage_separate mb ob slot matrix ->
  iqps_invocations version mb count before after ->
  Mem.load Mfloat32 after ob (object_slot_offset slot + 36) =
    Some (Vsingle (iqps_retained_sink_height count height depth)) /\
  (forall chunk b ofs,
    iq_protected_read mb ob slot chunk b ofs -> iq_outside_display ob slot chunk b ofs ->
    Mem.load chunk after b ofs = Mem.load chunk before b ofs).

Theorem iqps_completed_retained_calls_have_exact_effect : InkRetainedSinkExactEffect.
Proof.
  unfold InkRetainedSinkExactEffect.
  intros version count before after mb ob slot matrix height depth Hslot
    Hstate Hpool Hobj Hmatrix Hd Hy Hsep Hcalls.
  revert height Hobj Hmatrix Hd Hy.
  induction Hcalls as [m|n before middle after trace result Hcall Hcalls IH];
    intros height Hobj Hmatrix Hd Hy.
  - split; [exact Hy|]. intros; reflexivity.
  - destruct (iq_completed_sink_has_exact_effect version before mb ob slot matrix
      height depth trace middle result Hslot Hstate Hpool Hobj Hmatrix Hd Hy Hsep Hcall)
      as [Hnext Hframe].
    pose proof (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool) as Hblocks.
    assert (Mem.load Mint32 middle mb 136 =
      Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HobjNext.
    { rewrite Hframe; [exact Hobj|left; reflexivity|left; exact Hblocks]. }
    assert (Mem.load Mint32 middle ob (object_slot_offset slot + 80) =
      Some (iq_optional_pointer matrix)) as HmatrixNext.
    { rewrite Hframe; [exact Hmatrix|right; repeat split; cbn [size_chunk]; lia|
        right; right; lia]. }
    assert (Mem.load Mfloat32 middle mb 192 = Some (Vsingle depth)) as HdNext.
    { rewrite Hframe; [exact Hd|left; reflexivity|left; exact Hblocks]. }
    destruct (IH (Float32.sub height depth) HobjNext HmatrixNext HdNext Hnext)
      as [Hlast Hrest].
    split; [exact Hlast|].
    intros chunk b ofs Hprotected Houtside.
    rewrite (Hrest chunk b ofs Hprotected Houtside).
    exact (Hframe chunk b ofs Hprotected Houtside).
Qed.

(** Exact binary32 accumulation: -4, not an enormous supplied negative,
    suffices for the magnitude test if display retention lasts long enough.
    292 calls give 1936; 293 give 1940.  No claim about a reached 293-frame
    dialog or simultaneous low pose is made by this finite certificate. *)
Definition InkSmallNegativeAccumulationCertificate : Prop :=
  map (fun n => Int.unsigned (Float32.to_bits
    (iqps_retained_sink_height n iqps_low_height iqps_small_negative_depth)))
    [1%nat; 292%nat; 293%nat] = [1145110528; 1156710400; 1156743168] /\
  Float32.cmp Clt
    (iqps_retained_sink_height 292 iqps_low_height iqps_small_negative_depth)
    ivr_contact_height = true /\
  Float32.cmp Cge
    (iqps_retained_sink_height 293 iqps_low_height iqps_small_negative_depth)
    ivr_contact_height = true.

Theorem iqps_small_negative_accumulation_checked :
  InkSmallNegativeAccumulationCertificate.
Proof. vm_compute; repeat split; reflexivity. Qed.

Definition InkOriginalSizedSinkCall : Prop :=
  forall version before after mb ob slot matrix trace result,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.load Mint32 before mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 before ob (object_slot_offset slot + 80) = Some (iq_optional_pointer matrix) ->
  Mem.load Mfloat32 before mb 192 = Some (Vsingle iqps_exact_negative_depth) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 36) = Some (Vsingle iqps_low_height) ->
  iq_matrix_storage_separate mb ob slot matrix ->
  ClightBigstep.Clight2.eval_funcall ge before (Internal (iq_body version))
    [Vptr mb Ptrofs.zero] trace after result ->
  Mem.load Mfloat32 after ob (object_slot_offset slot + 36) = Some (Vsingle ivr_contact_height) /\
  Mem.load Mfloat32 after mb 64 = Mem.load Mfloat32 before mb 64 /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 164) =
    Mem.load Mfloat32 before ob (object_slot_offset slot + 164) /\
  Mem.load Mfloat32 after mb 192 = Mem.load Mfloat32 before mb 192.

Theorem iqps_real_sink_can_supply_original_display_size : InkOriginalSizedSinkCall.
Proof.
  unfold InkOriginalSizedSinkCall.
  intros version before after mb ob slot matrix trace result Hslot Hstate
    Hpool Hobj Hmatrix Hd Hy Hsep Hcall.
  destruct (iq_completed_sink_has_exact_effect version before mb ob slot matrix
    iqps_low_height iqps_exact_negative_depth trace after result Hslot Hstate
    Hpool Hobj Hmatrix Hd Hy Hsep Hcall) as [Hdisplay Hframe].
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool) as Hblocks.
  rewrite iqps_exact_negative_depth_hits_checked_top in Hdisplay.
  split; [exact Hdisplay|].
  split.
  - apply Hframe; [left; reflexivity|left; exact Hblocks].
  - split.
    + apply Hframe; [right; repeat split; cbn [size_chunk]; lia|right; right; lia].
    + apply Hframe; [left; reflexivity|left; exact Hblocks].
Qed.

(** Compose the accepted conditional stock history package with the actual
    sink.  The classified writers and physical-controller action history
    remain visible premises: this is not an all-gameplay coverage theorem. *)
Definition InkClassifiedNoASinkInsufficient : Prop :=
  forall version inputs seed before after mb ob slot matrix height depth trace result,
  let ge := Clight.globalenv (selected_clight_target version) in
  InkClassifiedDepthHistory inputs seed depth ->
  JPBinary32FiniteNonnegative seed -> fewer_than_one_a_press inputs ->
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.load Mint32 before mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 before ob (object_slot_offset slot + 80) = Some (iq_optional_pointer matrix) ->
  Mem.load Mfloat32 before mb 192 = Some (Vsingle depth) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 36) = Some (Vsingle height) ->
  iq_matrix_storage_separate mb ob slot matrix ->
  ClightBigstep.Clight2.eval_funcall ge before (Internal (iq_body version))
    [Vptr mb Ptrofs.zero] trace after result ->
  is_finite 24 128 height = true -> is_finite 24 128 depth = true ->
  is_finite 24 128 (Float32.sub height depth) = true ->
  Mem.load Mfloat32 after ob (object_slot_offset slot + 36) =
    Some (Vsingle (Float32.sub height depth)) /\
  (B2R 24 128 (Float32.sub height depth) <= B2R 24 128 height)%R.

Theorem iqps_classified_no_a_sink_cannot_create_upward_gap :
  InkClassifiedNoASinkInsufficient.
Proof.
  unfold InkClassifiedNoASinkInsufficient.
  intros version inputs seed before after mb ob slot matrix height depth trace result
    Hhistory Hseed Hno Hslot Hstate Hpool Hobj Hmatrix Hd Hy Hsep Hcall
    HheightFinite HdepthFinite HafterFinite.
  destruct (iq_completed_sink_has_exact_effect version before mb ob slot matrix height
    depth trace after result Hslot Hstate Hpool Hobj Hmatrix Hd Hy Hsep Hcall)
    as [Hdisplay Hframe].
  pose proof (isc_no_a_excludes_classified_negative_seed inputs seed depth
    Hhistory Hseed Hno) as Hnonnegative.
  split; [exact Hdisplay|].
  apply iq_nonnegative_subtraction_cannot_raise; try assumption. lra.
Qed.

Definition InkQuicksandProducerSizeBoundary : Prop :=
  InkRetainedSinkExactEffect /\ InkSmallNegativeAccumulationCertificate /\
  InkOriginalSizedSinkCall /\ InkClassifiedNoASinkInsufficient.

Theorem iqps_quicksand_producer_size_checked : InkQuicksandProducerSizeBoundary.
Proof.
  split; [exact iqps_completed_retained_calls_have_exact_effect|].
  split; [exact iqps_small_negative_accumulation_checked|].
  split; [exact iqps_real_sink_can_supply_original_display_size|].
  exact iqps_classified_no_a_sink_cannot_create_upward_gap.
Qed.
