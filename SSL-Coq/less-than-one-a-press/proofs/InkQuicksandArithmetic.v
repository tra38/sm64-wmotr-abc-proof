(** Binary32 subtraction cannot raise a finite height with finite nonnegative
    depth. Later execution lemmas instantiate this with the actual sink reads. *)
From Coq Require Import Reals Lia Lra ZArith Logic.ProofIrrelevance.
From compcert Require Import Floats.
From Flocq Require Import BinarySingleNaN Binary Core.
Local Open Scope R_scope.
Local Transparent Float32.sub.

Local Instance iq_precision_positive : Prec_gt_0 24.
Proof. constructor; lia. Defined.
Local Instance iq_precision_below_exponent : Prec_lt_emax 24 128.
Proof. constructor; lia. Defined.

Theorem iq_nonnegative_subtraction_cannot_raise : forall height depth,
  is_finite 24 128 height = true ->
  is_finite 24 128 depth = true ->
  is_finite 24 128 (Float32.sub height depth) = true ->
  0 <= B2R 24 128 depth ->
  B2R 24 128 (Float32.sub height depth) <= B2R 24 128 height.
Proof.
  intros height depth Hheight Hdepth Hresult Hsign.
  pose proof (Binary.Bminus_correct 24 128 _ _ Float32.binop_nan mode_NE
    height depth Hheight Hdepth) as Hminus.
  assert (Hsub : Float32.sub height depth =
    Binary.Bminus 24 128 iq_precision_positive iq_precision_below_exponent
      Float32.binop_nan mode_NE height depth).
  { unfold Float32.sub. f_equal; apply proof_irrelevance. }
  rewrite Hsub in Hresult |- *.
  destruct (Rlt_bool (Rabs (round radix2 (SpecFloat.fexp 24 128)
    (round_mode mode_NE) (B2R 24 128 height - B2R 24 128 depth))) (bpow radix2 128)).
  - destruct Hminus as [Hvalue _]. rewrite Hvalue.
    rewrite <- (round_generic radix2 (SpecFloat.fexp 24 128)
      (round_mode mode_NE) (B2R 24 128 height)) at 2.
    + apply round_le; [typeclasses eauto|typeclasses eauto|lra].
    + apply Binary.generic_format_B2R.
  - destruct Hminus as [Hoverflow _].
    destruct (Binary.Bminus 24 128 iq_precision_positive iq_precision_below_exponent
      Float32.binop_nan mode_NE height depth); cbn in Hresult; try discriminate;
      cbn [B2FF binary_overflow] in Hoverflow; discriminate.
Qed.

Corollary iq_finite_raise_requires_negative_depth : forall height depth,
  is_finite 24 128 height = true ->
  is_finite 24 128 depth = true ->
  is_finite 24 128 (Float32.sub height depth) = true ->
  B2R 24 128 height < B2R 24 128 (Float32.sub height depth) ->
  B2R 24 128 depth < 0.
Proof.
  intros height depth Hheight Hdepth Hresult Hraise.
  destruct (Rle_dec 0 (B2R 24 128 depth)); [|lra].
  pose proof (iq_nonnegative_subtraction_cannot_raise _ _ Hheight Hdepth Hresult r). lra.
Qed.
