(** The remaining direct MarioState.action stores, as distinct from writes
    to camera/body-state fields with the same name.  This is an exhaustive
    source census plus a semantics lemma for the literal stores. It does not
    classify aliased stores or outside-call effects in a complete history. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts ActionDepthAliasCensus
  InkActionConstructor InkActionInstall InkBackwardSource InkBackwardExecution
  InkActionPassStart InkControllerEdge ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Opaque selected_clight_target.

Definition idas_mario_action_lhs lhs := match lhs with
| Efield base field ty =>
    Pos.eqb field IBM._action &&
    (if type_eq (typeof base) (Tstruct IBM._MarioState noattr) then true else false) &&
    (if type_eq ty tuint then true else false)
| _ => false end.
Definition idas_safe_literal rhs := match rhs with
| Econst_int value ty => iai_safe_integer value &&
    ((if type_eq ty tint then true else false) ||
     (if type_eq ty tuint then true else false))
| _ => false end.
Fixpoint idas_nonliteral_store s := match s with
| Sassign lhs rhs => idas_mario_action_lhs lhs && negb (idas_safe_literal rhs)
| Ssequence a b | Sloop a b | Sifthenelse _ a b =>
    idas_nonliteral_store a || idas_nonliteral_store b
| Sswitch _ cases => idas_nonliteral_cases cases
| Slabel _ body => idas_nonliteral_store body
| _ => false end
with idas_nonliteral_cases cases := match cases with
| LSnil => false
| LScons _ body rest => idas_nonliteral_store body || idas_nonliteral_cases rest end.

Theorem idas_only_setter_and_initialization_have_nonliteral_action_stores :
  internal_statement_predicate_sites idas_nonliteral_store us_generated_definitions =
    [IBM._set_mario_action; IBM._init_mario] /\
  internal_statement_predicate_sites idas_nonliteral_store jp_generated_definitions_for_alias =
    [IBM._set_mario_action; IBM._init_mario].
Proof. vm_compute; split; reflexivity. Qed.

Lemma idas_safe_literal_is_an_integer : forall rhs,
  idas_safe_literal rhs = true ->
  exists value ty, rhs = Econst_int value ty /\ (ty = tint \/ ty = tuint) /\
    iai_safe_value (Vint value).
Proof.
  intros rhs H. destruct rhs; try discriminate.
  cbn [idas_safe_literal] in H. apply andb_true_iff in H as [Hvalue Hty].
  apply orb_true_iff in Hty as [Hty|Hty].
  - destruct (type_eq t tint); try discriminate. subst t.
    do 2 eexists. split; [reflexivity|]. split; [left; reflexivity|now apply iai_safe_integer_sound].
  - destruct (type_eq t tuint); try discriminate. subst t.
    do 2 eexists. split; [reflexivity|]. split; [right; reflexivity|now apply iai_safe_integer_sound].
Qed.

Definition idas_field temp := Efield
  (Ederef (Etempvar temp (tptr (Tstruct IBM._MarioState noattr)))
    (Tstruct IBM._MarioState noattr)) IBM._action tuint.
Definition InkDirectLiteralActionStoreExclusion : Prop :=
  forall version e le m temp mb mo rhs t le' m' out,
  le ! temp = Some (Vptr mb mo) -> idas_safe_literal rhs = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign (idas_field temp) rhs) t le' m' out ->
  exists value,
    iai_action_load m' mb mo = Some (Vint value) /\
    iai_safe_value (Vint value).

Theorem idas_executed_literal_store_excludes_both_long_jump_actions :
  InkDirectLiteralActionStoreExclusion.
Proof.
  intros version e le m temp mb mo rhs t le' m' out Hm Hliteral Hrun.
  destruct (idas_safe_literal_is_an_integer rhs Hliteral) as (value & ty & -> & Hty & Hsafe).
  destruct Hty; subst ty; inversion Hrun; subst.
  all: match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version))
      _ _ _ temp IBM._MarioState IBM._action tuint mb mo 12 _ _ _
      Hm (ias_selected_action_field version) Hl) as (-> & -> & ->) end.
  all: match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in H; subst end.
  all: lazymatch goal with H : sem_cast _ _ _ _ = Some ?answer |- _ =>
    change (Some (Vint value) = Some answer) in H; inversion H; subst end.
  all: match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; try discriminate end.
  all: match goal with H : access_mode _ = By_value _ |- _ =>
    cbn in H; inversion H; subst end.
  all: match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ =>
    unfold iai_action_load; rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore) end.
  all: exists value; split; [reflexivity|exact Hsafe].
Qed.

Definition InkDirectActionStoreBoundary : Prop :=
  (internal_statement_predicate_sites idas_nonliteral_store us_generated_definitions =
    [IBM._set_mario_action; IBM._init_mario] /\
   internal_statement_predicate_sites idas_nonliteral_store jp_generated_definitions_for_alias =
    [IBM._set_mario_action; IBM._init_mario]) /\
  InkDirectLiteralActionStoreExclusion.

Theorem idas_direct_action_stores_checked : InkDirectActionStoreBoundary.
Proof.
  split; [exact idas_only_setter_and_initialization_have_nonliteral_action_stores|
    exact idas_executed_literal_store_excludes_both_long_jump_actions].
Qed.
