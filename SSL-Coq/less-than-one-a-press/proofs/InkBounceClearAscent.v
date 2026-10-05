(** Finite binary32 diagnostics for an unchanged, clear-air ascent.

    The generated source contains the quarter position addition and default
    four-unit gravity subtraction checked below.  The supplied 30/80 speeds
    also occur in the actual bounce handlers.  Every operation of these three
    finite traces is checked individually, with integer quarter-unit states
    preventing large nested Float32 terms.

    This is NOT a proof that an air-quarter accepts these coordinates, that
    wind/collision/action changes are absent, or that a bounce reaches either
    supplied starting height.  A flight height is not a preserved display gap.
    Actor placement and legitimate cloning are deliberately not classified
    by this arithmetic certificate. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Floats Integers.
From LessThanOneAPress.Generated Require Import us_mario_step jp_mario_step
  us_interaction jp_interaction.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts InkBounceProducerEffect.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IBCA := us_mario_step.

Fixpoint ibca_assignment_values s := match s with
| Sassign _ rhs => [rhs]
| Ssequence a b | Sloop a b | Sifthenelse _ a b =>
    ibca_assignment_values a ++ ibca_assignment_values b
| Sswitch _ cases => ibca_assignment_cases cases
| Slabel _ body => ibca_assignment_values body
| _ => [] end
with ibca_assignment_cases cases := match cases with
| LSnil => []
| LScons _ body rest => ibca_assignment_values body ++ ibca_assignment_cases rest
end.

(** Compare the inspected operation through its literal bits, not by expanding
    binary32 representation proofs inside structural AST equalities. *)
Definition ibca_is_position_expression expression := match expression with
| Ebinop Oadd (Etempvar first _) (Ebinop Odiv (Etempvar second _)
    (Econst_single four _) _) _ =>
    Pos.eqb first IBCA._t'14 && Pos.eqb second IBCA._t'15 &&
      Int.eq (Float32.to_bits four) (Int.repr 1082130432)
| _ => false end.
Definition ibca_is_gravity_expression expression := match expression with
| Ebinop Osub (Etempvar source _) (Econst_single four _) _ =>
    Pos.eqb source IBCA._t'13 &&
      Int.eq (Float32.to_bits four) (Int.repr 1082130432)
| _ => false end.

Definition InkBounceClearAscentSource : Prop := forall version,
  existsb ibca_is_position_expression (ibca_assignment_values
    (fn_body (match version with VersionUS => us_mario_step.f_perform_air_step
      | VersionJP => jp_mario_step.f_perform_air_step end))) = true /\
  existsb ibca_is_gravity_expression (ibca_assignment_values
    (fn_body (match version with VersionUS => us_mario_step.f_apply_gravity
      | VersionJP => jp_mario_step.f_apply_gravity end))) = true /\
  statement_mentions_float32_bits_s 1106247680
    (fn_body (match version with VersionUS => us_interaction.f_interact_bounce_top
      | VersionJP => jp_interaction.f_interact_bounce_top end)) = true /\
  statement_mentions_float32_bits_s 1117782016
    (fn_body (match version with VersionUS => us_interaction.f_interact_bounce_top
      | VersionJP => jp_interaction.f_interact_bounce_top end)) = true.

Theorem ibca_clear_ascent_operations_are_generated : InkBounceClearAscentSource.
Proof.
  unfold InkBounceClearAscentSource. intros version.
  destruct (ibp_bounce_velocities_are_generated version) as [H30 H80].
  repeat split; try assumption.
  - destruct version; vm_compute; reflexivity.
  - destruct version; vm_compute; reflexivity.
Qed.

Definition ibca_float4 y4 := Float32.div (ibp_f32 y4) (ibp_f32 4).
Definition ibca_bits_equal a b := Int.eq (Float32.to_bits a) (Float32.to_bits b).

(** The pair is (height in quarter units, vertical velocity in units). *)
Definition ibca_next (s : Z * Z) :=
  (fst s + 4 * snd s, snd s - 4).
Fixpoint ibca_trace count s := match count with
| O => []
| S remaining => s :: ibca_trace remaining (ibca_next s)
end.
Fixpoint ibca_after count s := match count with
| O => s
| S remaining => ibca_after remaining (ibca_next s)
end.

Fixpoint ibca_quarters_exact count y4 velocity := match count with
| O => true
| S remaining =>
  ibca_bits_equal
    (Float32.add (ibca_float4 y4) (Float32.div (ibp_f32 velocity) (ibp_f32 4)))
    (ibca_float4 (y4 + velocity)) &&
  ibca_quarters_exact remaining (y4 + velocity) velocity
end.
Definition ibca_frame_exact s :=
  (0 <? snd s) &&
  ibca_quarters_exact 4 (fst s) (snd s) &&
  ibca_bits_equal (Float32.sub (ibp_f32 (snd s)) (ibp_f32 4))
    (ibp_f32 (snd s - 4)) &&
  negb (Float32.cmp Clt (ibp_f32 (snd s - 4)) (ibp_f32 (-75))).

Definition ibca_normal30_start := (4072,30).
Definition ibca_twirl80_start := (4072,80).
Definition ibca_high_twirl80_start := (5000,80).
Definition ibca_normal30_trace := ibca_trace 8 ibca_normal30_start.
Definition ibca_twirl80_trace := ibca_trace 20 ibca_twirl80_start.
Definition ibca_high_twirl80_trace := ibca_trace 20 ibca_high_twirl80_start.

Definition InkBounceClearAscentFinite : Prop :=
  length ibca_normal30_trace = 8%nat /\
  length ibca_twirl80_trace = 20%nat /\
  length ibca_high_twirl80_trace = 20%nat /\
  forallb ibca_frame_exact ibca_normal30_trace = true /\
  forallb ibca_frame_exact ibca_twirl80_trace = true /\
  forallb ibca_frame_exact ibca_high_twirl80_trace = true /\
  ibca_after 8 ibca_normal30_start = (4584,-2) /\
  ibca_after 20 ibca_twirl80_start = (7432,0) /\
  ibca_after 20 ibca_high_twirl80_start = (8360,0) /\
  ibca_float4 4584 = ibp_f32 1146 /\
  ibca_float4 7432 = ibp_f32 1858 /\
  ibca_float4 8360 = ibp_f32 2090 /\
  1146 - 1018 = 128 /\ 1858 - 1018 = 840 /\ 2090 - 1250 = 840 /\
  1861 - 1858 = 3 /\
  Float32.cmp Clt (ibp_f32 1858) (ibp_f32 1861) = true /\
  Float32.cmp Cgt (ibp_f32 2090) (ibp_f32 1861) = true.

Lemma ibca_float_bits_determine : forall first second : float32,
  Float32.to_bits first = Float32.to_bits second -> first = second.
Proof.
  intros first second Hbits.
  rewrite <- (Float32.of_to_bits first), <- (Float32.of_to_bits second).
  now rewrite Hbits.
Qed.

Theorem ibca_three_clear_ascent_profiles_checked : InkBounceClearAscentFinite.
Proof.
  unfold InkBounceClearAscentFinite.
  repeat apply conj.
  all: lazymatch goal with
  | |- @eq nat _ _ => idtac "IBCA length"; vm_compute; reflexivity
  | |- @eq Z _ _ => idtac "IBCA integer"; vm_compute; reflexivity
  | |- @eq (Z * Z)%type _ _ => idtac "IBCA integer endpoint"; vm_compute; reflexivity
  | |- @eq float32 _ _ => idtac "IBCA float endpoint bits";
      apply ibca_float_bits_determine; vm_compute; reflexivity
  | _ => idtac "IBCA remaining Boolean certificate"; vm_compute; reflexivity
  end.
Qed.

Definition InkBounceClearAscentBoundary : Prop :=
  InkBounceClearAscentSource /\ InkBounceClearAscentFinite.
Theorem ibca_clear_ascent_boundary_checked : InkBounceClearAscentBoundary.
Proof.
  split; [exact ibca_clear_ascent_operations_are_generated|
    exact ibca_three_clear_ascent_profiles_checked].
Qed.
