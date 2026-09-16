(** The actual reached distance argument is in the ordinary SQRT.S domain.
    The concrete routine proof then supplies both number and RAM frame for
    a matching machine realization. This does not identify CompCert's
    unspecified external_functions_sem with that realization. *)
From Coq Require Import Bool Lia List ZArith Reals Lra.
From Flocq Require Import BinarySingleNaN Binary Core.
From compcert Require Import AST Clight ClightBigstep Ctypes Events Floats
  Globalenvs Integers Memory Values.
From LessThanOneAPress.Proofs Require Import
  GameTypes Area2TripletSpawner Area2TripletDistance SqrtfMachine
  Area2Rank9ACoinFlight SelectedClightTarget InkTimer131RetailMipsCode.
Import ListNotations.
Local Open Scope Z_scope.

Theorem tsp_actual_argument_is_normal : forall y b,
  ts_in_base (vec_x b) (vec_z b) ->
  rank9cf_finite (Float32.sub y (vec_y b)) ->
  (-16384 <= rank9cf_real (Float32.sub y (vec_y b)) <= 16384)%R ->
  let a := {| vec_x := ts_float 3181; vec_y := y; vec_z := ts_float 3587 |} in
  sqrtf_operand_domain (td_squared a b) /\
  (15070322 <= rank9cf_real (td_squared a b) <= 536870912)%R.
Proof.
  intros y b Hbase Fy Hy a.
  destruct (ts_squared_input_range (vec_x b) (vec_z b)
    (Float32.sub y (vec_y b)) Hbase Fy Hy) as [F H].
  change (rank9cf_finite (td_squared a b)) in F.
  change (15070322 <= rank9cf_real (td_squared a b) <= 536870912)%R in H.
  assert (Hsmall : (bpow radix2 (-126) <= 1)%R).
  { change (bpow radix2 (-126) <= bpow radix2 0)%R. apply bpow_le. lia. }
  split; [unfold sqrtf_operand_domain; repeat split; try assumption; try lra; right; lra|exact H].
Qed.

Definition TripletReachedSqrtInput : Prop :=
  forall version m ab ao y bb bo b t after result,
  let a := {| vec_x := ts_float 3181; vec_y := y; vec_z := ts_float 3587 |} in
  td_position m ab ao a -> td_position m bb bo b ->
  ts_in_base (vec_x b) (vec_z b) ->
  rank9cf_finite (Float32.sub y (vec_y b)) ->
  (-16384 <= rank9cf_real (Float32.sub y (vec_y b)) <= 16384)%R ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ts_distance_body version)) [Vptr ab ao; Vptr bb bo] t after result ->
  sqrtf_operand_domain (td_squared a b) /\
  exists fb fd,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m fd
      [Vsingle (td_squared a b)] t after result.

Theorem tsp_reached_sqrt_input_is_normal : TripletReachedSqrtInput.
Proof.
  intros version m ab ao y bb bo b t after result a Ha Hb Hbase Fy Hy Hcall.
  split; [exact (proj1 (tsp_actual_argument_is_normal y b Hbase Fy Hy))|].
  destruct (td_live_distance_call_reduces_to_sqrt _ _ _ _ _ _ _ _ _ _ _
    Ha Hb Hcall) as (fb & fd & Hsymbol & Hfun & Htype & Hsqrt).
  exists fb, fd. auto.
Qed.

(** This extra premise is the explicit cross-language realization of THIS
    call, not an assertion that all reached externals have been covered. *)
Definition TripletRealizedDistanceRejection : Prop :=
  forall version m ab ao y bb bo b t after result,
  let a := {| vec_x := ts_float 3181; vec_y := y; vec_z := ts_float 3587 |} in
  td_position m ab ao a -> td_position m bb bo b ->
  ts_in_base (vec_x b) (vec_z b) ->
  rank9cf_finite (Float32.sub y (vec_y b)) ->
  (-16384 <= rank9cf_real (Float32.sub y (vec_y b)) <= 16384)%R ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ts_distance_body version)) [Vptr ab ao; Vptr bb bo] t after result ->
  SqrtfMachineCall (td_squared a b) m t result after ->
  sqrtf_operand_domain (td_squared a b) /\ after = m /\
  exists distance, result = Vsingle distance /\
    Float32.cmp Clt distance ts_threshold = false.
Theorem tsp_realized_distance_rejects_and_preserves_memory : TripletRealizedDistanceRejection.
Proof.
  intros version m ab ao y bb bo b t after result a Ha Hb Hbase Fy Hy Hcall Hmachine.
  destruct (tsp_reached_sqrt_input_is_normal _ _ _ _ _ _ _ _ _ _ _
    Ha Hb Hbase Fy Hy Hcall) as [Hnormal Hreached].
  destruct (sqrtf_machine_call_value_and_memory _ _ _ _ _ Hmachine)
    as [Hr [Hm Htrace]].
  split; [exact Hnormal|]. split; [exact Hm|].
  exists (Float32.sqrt (td_squared a b)). split; [exact Hr|].
  exact (ts_elevator_distance_rejects_native_guard _ _ _ Hbase Fy Hy).
Qed.

Definition TripletSqrtImplementationBoundary : Prop :=
  TripletReachedSqrtInput /\ TripletRealizedDistanceRejection /\
  (forall argument before trace result after,
    SqrtfMachineCall argument before trace result after ->
    result = Vsingle (Float32.sqrt argument) /\ after = before /\ trace = E0) /\
  (forall before after,
    sqrtf_rounding before = mode_NE ->
    SqrtfWordExecution jp_sqrtf_words before after ->
    rank9cf_real (sqrtf_fpr after 0) =
      rank9cf_round (sqrt (rank9cf_real (sqrtf_fpr before 12)))) /\
  (forall argument before,
    sqrtf_operand_domain argument ->
    exists result after, SqrtfMachineCall argument before E0 result after).
Theorem tsp_sqrt_implementation_boundary_checked : TripletSqrtImplementationBoundary.
Proof.
  split; [exact tsp_reached_sqrt_input_is_normal|].
  split; [exact tsp_realized_distance_rejects_and_preserves_memory|].
  split; [exact sqrtf_machine_call_value_and_memory|].
  split; [exact sqrtf_result_is_correctly_rounded|exact sqrtf_machine_call_exists].
Qed.
