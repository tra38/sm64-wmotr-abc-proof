(** Sign of the exact Float32 operation tree at the landing depth write. *)
From Coq Require Import Reals Lia Lra ZArith Logic.ProofIrrelevance.
From compcert Require Import Floats Integers.
From Flocq Require Import BinarySingleNaN Binary Core.
From LessThanOneAPress.Proofs Require Import JPBinary32DepthWrites.
Local Open Scope Z_scope.
Local Transparent Float32.add Float32.sub Float32.mul Float32.of_int.

Definition imb_depth_delta (timer : int) : float32 :=
  Float32.sub (Float32.mul (Float32.of_int (Int.sub (Int.repr 4) timer))
    (Float32.of_bits (Int.repr 1080033280)))
    (Float32.of_bits (Int.repr 1056964608)).

Lemma imb_early_delta_is_nonnegative : forall timer,
  Int.unsigned timer <= 3 -> JPBinary32FiniteNonnegative (imb_depth_delta timer).
Proof.
  intros timer Hsmall. pose proof (Int.unsigned_range timer) as Hrange.
  assert (Int.unsigned timer = 0 \/ Int.unsigned timer = 1 \/
    Int.unsigned timer = 2 \/ Int.unsigned timer = 3) as Hcases by lia.
  rewrite <- (Int.repr_unsigned timer).
  destruct Hcases as [Ht | [Ht | [Ht | Ht]]]; rewrite Ht;
    unfold JPBinary32FiniteNonnegative, imb_depth_delta; vm_compute; split; nra.
Qed.

(** A finite result supplies the no-overflow fact instead of assuming one. *)
Lemma imb_add_finite_nonnegative : forall x y,
  JPBinary32FiniteNonnegative x -> JPBinary32FiniteNonnegative y ->
  is_finite 24 128 (Float32.add x y) = true ->
  JPBinary32FiniteNonnegative (Float32.add x y).
Proof.
  intros x y Hx Hy Hfinite.
  apply jp_binary32_add_preserves_finite_nonnegative; try assumption.
  unfold JPBinary32AddNoOverflow.
  pose proof (Binary.Bplus_correct 24 128 jp_binary32_prec_positive
    jp_binary32_prec_lt_emax Float32.binop_nan mode_NE
    x y (proj1 Hx) (proj1 Hy)) as Hplus.
  assert (Hadd : Float32.add x y =
    Binary.Bplus 24 128 jp_binary32_prec_positive jp_binary32_prec_lt_emax
      Float32.binop_nan mode_NE x y).
  { unfold Float32.add. f_equal; apply proof_irrelevance. }
  rewrite Hadd in Hfinite.
  destruct (Rlt_bool (Rabs (round radix2 (SpecFloat.fexp 24 128)
    (round_mode mode_NE) (B2R 24 128 x + B2R 24 128 y))) (bpow radix2 128));
    [reflexivity|].
  destruct Hplus as [Hoverflow _].
  destruct (Binary.Bplus 24 128 jp_binary32_prec_positive jp_binary32_prec_lt_emax
    Float32.binop_nan mode_NE x y); cbn in Hfinite; try discriminate;
    cbn [B2FF binary_overflow] in Hoverflow; discriminate.
Qed.

Theorem imb_first_negative_landing_needs_timer_at_least_four : forall depth timer,
  JPBinary32FiniteNonnegative depth ->
  is_finite 24 128 (Float32.add depth (imb_depth_delta timer)) = true ->
  (B2R 24 128 (Float32.add depth (imb_depth_delta timer)) < 0)%R ->
  4 <= Int.unsigned timer.
Proof.
  intros depth timer Hdepth Hfinite Hnegative.
  destruct (Z_le_gt_dec (Int.unsigned timer) 3); [|lia].
  pose proof (imb_add_finite_nonnegative _ _ Hdepth
    (imb_early_delta_is_nonnegative _ l) Hfinite) as [_ Hnonnegative]. lra.
Qed.
