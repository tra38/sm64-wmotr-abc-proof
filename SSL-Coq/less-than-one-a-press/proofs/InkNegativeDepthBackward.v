(** Backward from the real first negative landing write to a stock duration.
    The duration gate and this write must still be linked in live execution. *)
From Coq Require Import Lia Reals ZArith.
From compcert Require Import AST Clight ClightBigstep Floats Globalenvs Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkLandingExecution InkLongJumpGuard JPBinary32DepthWrites ObjectContactNecessity
  ZeroAQuicksandEntryBoundary NegativeDepthDefinedProducerClosure SelectedClightTarget.
Local Open Scope Z_scope.

Definition InkNegativeLandingStockDurationCut : Prop :=
  forall kind version e le m mb mo depth timer t le' m' out after,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26))) = Some (Vint timer) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (imb_landing_write version) t le' m' out ->
  Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) ->
  JPBinary32FiniteNonnegative depth -> is_finite 24 128 after = true ->
  (B2R 24 128 after < 0)%R ->
  stock_landing_body_runs kind (Int.unsigned timer) ->
  kind = StockLongJumpLand /\ 4 <= Int.unsigned timer <= 5.

Theorem imb_actual_negative_landing_with_stock_gate_requires_long_jump :
  InkNegativeLandingStockDurationCut.
Proof.
  unfold InkNegativeLandingStockDurationCut.
  intros kind version e le m mb mo depth timer t le' m' out after
    Hm Hdepth Htimer Hrun Hafter Hnonnegative Hfinite Hnegative Hgate.
  pose proof (imb_actual_first_negative_landing_needs_late_timer _ _ _ _ _ _ _ _ _ _ _ _ _
    Hm Hdepth Htimer Hrun Hafter Hnonnegative Hfinite Hnegative) as Hlate.
  destruct kind; unfold stock_landing_body_runs in Hgate;
    cbn [stock_landing_frames] in Hgate; try (exfalso; lia).
  split; [reflexivity|lia].
Qed.

(** The existing source/alias census is retained as evidence, NOT promoted to
    an execution projection. The conditional stock gate remains explicit. *)
Definition InkNegativeDepthCheckedBoundary : Prop :=
  NegativeDepthDefinedProducerCheckedBoundary /\
  InkFirstNegativeLandingCut /\ InkNegativeLandingStockDurationCut /\ InkCrouchGuardNoA.

Theorem imb_negative_depth_backward_checked : InkNegativeDepthCheckedBoundary.
Proof.
  split; [exact negative_depth_defined_producer_checked_boundary_holds|].
  split; [exact imb_actual_first_negative_landing_needs_late_timer|].
  split; [exact imb_actual_negative_landing_with_stock_gate_requires_long_jump|].
  exact imb_actual_crouch_a_guard_skips_without_pressed_bit.
Qed.
