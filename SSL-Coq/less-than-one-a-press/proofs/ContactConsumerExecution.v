(** Read-only contact searches, proved from their actual selected bodies.
    A contact consumer cannot silently replace its object arguments while
    searching. Later registration/award chronology is a separate obligation. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ContactConsumerSource
  ObjectContactNecessity Area2Rank12BContact Area2Rank9AStarSource SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Fixpoint cce_readonly_keep (keep : ident) (s : statement) : bool := match s with
| Sskip | Sbreak | Scontinue | Sreturn _ => true
| Sset id _ => negb (Pos.eqb id keep)
| Ssequence a b | Sifthenelse _ a b | Sloop a b =>
    cce_readonly_keep keep a && cce_readonly_keep keep b
| _ => false end.

Lemma cce_readonly_frame : forall ge e le m s t le' m' out keep,
  ocn_exec ge e le m s t le' m' out ->
  cce_readonly_keep keep s = true ->
  t = E0 /\ m' = m /\ le' ! keep = le ! keep.
Proof.
  intros ge e le m s t le' m' out keep Hrun.
  induction Hrun; cbn; intro Hshape; try discriminate;
    try (repeat split; reflexivity).
  - apply negb_true_iff in Hshape. apply Pos.eqb_neq in Hshape.
    repeat split; try reflexivity. apply PTree.gso. congruence.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Ha) as (-> & -> & Hfirst).
    destruct (IHHrun2 Hb) as (-> & -> & Hsecond).
    repeat split; try reflexivity. congruence.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct b; auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Ha) as (-> & -> & Hfirst).
    destruct (IHHrun2 Hb) as (-> & -> & Hsecond).
    repeat split; try reflexivity. congruence.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Ha) as (-> & -> & Hfirst).
    destruct (IHHrun2 Hb) as (-> & -> & Hsecond).
    destruct (IHHrun3 (andb_true_intro (conj Ha Hb))) as (-> & -> & Hthird).
    repeat split; try reflexivity. congruence.
Qed.

Theorem cce_search_source_is_readonly : forall version,
  cce_readonly_keep CCH._obj1 (fn_body (ccs_body version CCPairSearch)) = true /\
  cce_readonly_keep CCH._obj2 (fn_body (ccs_body version CCPairSearch)) = true /\
  cce_readonly_keep CCI._m (fn_body (ccs_body version CCStarSearch)) = true /\
  cce_readonly_keep CCI._interactType (fn_body (ccs_body version CCStarSearch)) = true.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Theorem cce_pair_search_preserves_memory_and_arguments :
  forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ccs_body version CCPairSearch)) t le' m' out ->
  t = E0 /\ m' = m /\ le' ! CCH._obj1 = le ! CCH._obj1 /\
    le' ! CCH._obj2 = le ! CCH._obj2.
Proof.
  intros version e le m t le' m' out Hrun.
  destruct (cce_search_source_is_readonly version) as (Hone & Htwo & _).
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun Hone).
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun Htwo). tauto.
Qed.

Theorem cce_star_search_preserves_memory_and_arguments :
  forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ccs_body version CCStarSearch)) t le' m' out ->
  t = E0 /\ m' = m /\ le' ! CCI._m = le ! CCI._m /\
    le' ! CCI._interactType = le ! CCI._interactType.
Proof.
  intros version e le m t le' m' out Hrun.
  destruct (cce_search_source_is_readonly version) as (_ & _ & Hm & Htype).
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun Hm).
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun Htype). tauto.
Qed.

(** A finite execution returning from one of these loops must return in a
    real iteration, not its increment. The invariant is derived only for
    temporaries the actual loop never assigns. *)
Lemma cce_returning_loop_iteration : forall ge e le m s t le' m' out,
  ocn_exec ge e le m s t le' m' out ->
  forall iteration increment returned,
  s = Sloop iteration increment -> out = Out_return returned ->
  ocn_normal_prefix increment = true ->
  exists il im it,
    ocn_exec ge e il im iteration it le' m' (Out_return returned) /\
    (forall keep, cce_readonly_keep keep (Sloop iteration increment) = true ->
      im = m /\ il ! keep = le ! keep).
Proof.
  intros ge e le m s t le' m' out Hrun.
  induction Hrun; intros iteration increment returned Hs Ho Hinc;
    inversion Hs; subst; try discriminate.
  - inversion H; subst.
    exists le, m, t. split; [assumption | intros; split; reflexivity].
  - pose proof (ocn_normal_prefix_outcome _ _ _ _ _ _ _ _ _ Hinc Hrun2) as Hnormal.
    subst out2. inversion H0.
  - destruct (IHHrun3 _ _ _ eq_refl eq_refl Hinc) as (il & im & it & Hiter & Hframe).
    exists il, im, it. split; [exact Hiter |].
    intros keep Hpure.
    pose proof (Hframe keep Hpure) as [Hmemory Hlocal].
    apply andb_true_iff in Hpure as [Hbody Hstep].
    pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun1 Hbody)
      as (_ & Hm1 & Hl1).
    pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun2 Hstep)
      as (_ & Hm2 & Hl2).
    split; congruence.
Qed.

Lemma cce_cast_zero_value : forall ge e le m value,
  eval_expr ge e le m (Ecast (Econst_int Int.zero tint) (tptr tvoid)) value ->
  value = Vint Int.zero.
Proof.
  intros ge e le m value Hexpr. inversion Hexpr; subst.
  - match goal with Hconst : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hconst; subst end.
    match goal with Hcast : sem_cast _ _ _ _ = Some value |- _ =>
      change (Some (Vint Int.zero) = Some value) in Hcast; congruence end.
  - match goal with Hlv : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ =>
      inversion Hlv end.
Qed.

Lemma cce_search_fallback_returns_zero : forall version consumer ge e le m t le' m' out,
  consumer = CCPairSearch \/ consumer = CCStarSearch ->
  ocn_exec ge e le m (ccs_search_fallback version consumer) t le' m' out ->
  exists ty, out = Out_return (Some (Vint Int.zero, ty)).
Proof.
  intros version consumer ge e le m t le' m' out [Hc | Hc] Hrun; subst consumer.
  - assert (ccs_search_fallback version CCPairSearch = rank12b_return_zero) as Hsource
      by (destruct version; reflexivity).
    rewrite Hsource in Hrun.
    pose proof (ocn_return_zero_outcome _ _ _ _ _ _ _ _ Hrun). eauto.
  - assert (ccs_search_fallback version CCStarSearch =
      Sreturn (Some (Ecast (Econst_int Int.zero tint) (tptr tvoid)))) as Hsource
      by (destruct version; reflexivity).
    rewrite Hsource in Hrun. inversion Hrun; subst.
    match goal with Hexpr : eval_expr _ _ _ _ (Ecast _ _) _ |- _ =>
      apply cce_cast_zero_value in Hexpr; subst end.
    eexists; reflexivity.
Qed.

Theorem cce_successful_search_reaches_returning_iteration :
  forall version consumer e le m t le' m' value ty,
  consumer = CCPairSearch \/ consumer = CCStarSearch -> value <> Vint Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ccs_body version consumer)) t le' m'
    (Out_return (Some (value, ty))) ->
  exists il im it,
    ocn_exec (Clight.globalenv (selected_clight_target version)) e il im
      (ccs_search_iteration version consumer) it le' m'
      (Out_return (Some (value, ty))) /\
    (forall keep, cce_readonly_keep keep (fn_body (ccs_body version consumer)) = true ->
      im = m /\ il ! keep = le ! keep).
Proof.
  intros version consumer e le m t le' m' value ty Hconsumer Hnonzero Hrun.
  rewrite (ccs_search_body_shape _ _ Hconsumer) in Hrun.
  assert (ocn_normal_prefix (ccs_search_increment version consumer) = true) as Hinc
    by (destruct version; destruct Hconsumer as [Hc | Hc]; subst consumer; reflexivity).
  inversion Hrun; subst.
  - match goal with Hfallback : ClightBigstep.exec_stmt _ _ _ _ _
        (ccs_search_fallback _ _) _ _ _ _ |- _ =>
      destruct (cce_search_fallback_returns_zero _ _ _ _ _ _ _ _ _ _ Hconsumer Hfallback)
        as [fallback_ty Hbad]; inversion Hbad; contradiction end.
  - match goal with Hseq : ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
      inversion Hseq; subst end.
    + match goal with Hinit : ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ =>
        inversion Hinit; subst end.
      match goal with Hloop : ClightBigstep.exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ |- _ =>
        destruct (cce_returning_loop_iteration _ _ _ _ _ _ _ _ _ Hloop
          _ _ _ eq_refl eq_refl Hinc) as (il & im & it & Hiter & Hframe) end.
      exists il, im, it. split; [exact Hiter |].
      intros keep Hpure. rewrite (ccs_search_body_shape _ _ Hconsumer) in Hpure.
      cbn [cce_readonly_keep] in Hpure.
      apply andb_true_iff in Hpure as [Hprefix _].
      apply andb_true_iff in Hprefix as [Hinitial Hloop].
      pose proof (Hframe keep Hloop) as [Hmemory Hlocal].
      split; [exact Hmemory |].
      rewrite Hlocal. apply negb_true_iff in Hinitial.
      apply Pos.eqb_neq in Hinitial. apply PTree.gso. congruence.
    + match goal with Hinit : ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ =>
        inversion Hinit end.
Qed.

Definition cce_pair_count_expression :=
  match ccs_search_iteration VersionUS CCPairSearch with
  | Ssequence (Ssequence (Sset _ expression) _) _ => expression
  | _ => Econst_int Int.zero tint end.
Definition cce_pair_entry_expression :=
  match ccs_search_iteration VersionUS CCPairSearch with
  | Ssequence _ (Ssequence (Sset _ expression) _) => expression
  | _ => Econst_int Int.zero tint end.
Definition cce_pair_count_guard := Ebinop Olt (Etempvar CCH._i tint)
  (Etempvar CCH._t'2 tshort) tint.
Definition cce_pair_match_guard := Ebinop Oeq
  (Etempvar CCH._t'1 (tptr (Tstruct CCH._Object noattr)))
  (Etempvar CCH._obj2 (tptr (Tstruct CCH._Object noattr))) tint.

Theorem cce_pair_iteration_source_exact : forall version,
  ccs_search_iteration version CCPairSearch =
    Ssequence
      (Ssequence (Sset CCH._t'2 cce_pair_count_expression)
        (Sifthenelse cce_pair_count_guard Sskip Sbreak))
      (Ssequence (Sset CCH._t'1 cce_pair_entry_expression)
        (Sifthenelse cce_pair_match_guard
          (Sreturn (Some (Econst_int Int.one tint))) Sskip)).
Proof. intros []; reflexivity. Qed.

(** Unroll only a loop-free subtree of an already given Clight derivation.
    This neither runs a substitute interpreter nor manufactures memory reads. *)
Ltac cce_unroll_loop_free_exec :=
  repeat match goal with
  | H : ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
      inversion H; subst; clear H;
      match goal with
      | Hb : ClightBigstep.exec_stmt _ _ _ _ _ (if ?take then _ else _) _ _ _ _ |- _ =>
          destruct take; cbn beta iota in *
      end
  | H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : ClightBigstep.exec_stmt _ _ _ _ _ Sbreak _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn _) _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end; try congruence.

Theorem cce_pair_iteration_reads_a_matching_entry :
  forall version ge e le m t le' m' value ty,
  ocn_exec ge e le m (ccs_search_iteration version CCPairSearch)
    t le' m' (Out_return (Some (value, ty))) ->
  exists count candidate,
    eval_expr ge e le m cce_pair_count_expression count /\
    eval_expr ge e (PTree.set CCH._t'2 count le) m
      cce_pair_entry_expression candidate /\
    ocn_test_value ge e (PTree.set CCH._t'2 count le) m cce_pair_count_guard true /\
    ocn_test_value ge e
      (PTree.set CCH._t'1 candidate (PTree.set CCH._t'2 count le))
      m cce_pair_match_guard true /\
    value = Vint Int.one /\ ty = tint /\ m' = m /\ t = E0.
Proof.
  intros version ge e le m t le' m' value ty Hrun.
  rewrite cce_pair_iteration_source_exact in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  match goal with Hconstant : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hconstant; subst end.
  match goal with
  | Hcount : eval_expr _ _ _ _ cce_pair_count_expression ?count,
    Hentry : eval_expr _ _ _ _ cce_pair_entry_expression ?candidate |- _ =>
    exists count, candidate
  end.
  repeat split; try assumption; try reflexivity; unfold ocn_test_value; eauto.
Qed.

Definition cce_star_owner_expression :=
  match ccs_search_iteration VersionUS CCStarSearch with
  | Ssequence (Ssequence (Sset _ expression) _) _ => expression
  | _ => Econst_int Int.zero tint end.
Definition cce_star_count_expression :=
  match ccs_search_iteration VersionUS CCStarSearch with
  | Ssequence (Ssequence _ (Ssequence (Sset _ expression) _)) _ => expression
  | _ => Econst_int Int.zero tint end.
Definition cce_star_entry_expression :=
  match ccs_search_iteration VersionUS CCStarSearch with
  | Ssequence _ (Ssequence (Ssequence _ (Sset _ expression)) _) => expression
  | _ => Econst_int Int.zero tint end.
Definition cce_star_type_expression version :=
  match ccs_search_iteration version CCStarSearch with
  | Ssequence _ (Ssequence _ (Ssequence (Sset _ expression) _)) => expression
  | _ => Econst_int Int.zero tint end.
Definition cce_star_count_guard := Ebinop Olt (Etempvar CCI._i tint)
  (Etempvar CCI._t'4 tshort) tint.
Definition cce_star_match_guard := Ebinop Oeq (Etempvar CCI._t'1 tuint)
  (Etempvar CCI._interactType tuint) tint.
Definition cce_star_object_type := tptr (Tstruct CCI._Object noattr).

Theorem cce_star_iteration_source_exact : forall version,
  ccs_search_iteration version CCStarSearch =
    Ssequence
      (Ssequence (Sset CCI._t'3 cce_star_owner_expression)
        (Ssequence (Sset CCI._t'4 cce_star_count_expression)
          (Sifthenelse cce_star_count_guard Sskip Sbreak)))
      (Ssequence
        (Ssequence (Sset CCI._t'2 cce_star_owner_expression)
          (Sset CCI._object cce_star_entry_expression))
        (Ssequence (Sset CCI._t'1 (cce_star_type_expression version))
          (Sifthenelse cce_star_match_guard
            (Sreturn (Some (Etempvar CCI._object cce_star_object_type))) Sskip))).
Proof. intros []; reflexivity. Qed.

Definition cce_star_count_locals (le : temp_env) first_owner count :=
  PTree.set CCI._t'4 count (PTree.set CCI._t'3 first_owner le).
Definition cce_star_entry_locals le first_owner count second_owner :=
  PTree.set CCI._t'2 second_owner (cce_star_count_locals le first_owner count).
Definition cce_star_match_locals le first_owner count second_owner candidate kind :=
  PTree.set CCI._t'1 kind (PTree.set CCI._object candidate
    (cce_star_entry_locals le first_owner count second_owner)).

Theorem cce_star_iteration_returns_a_recorded_entry :
  forall version ge e le m t le' m' value ty,
  ocn_exec ge e le m (ccs_search_iteration version CCStarSearch)
    t le' m' (Out_return (Some (value, ty))) ->
  exists first_owner count second_owner kind,
    eval_expr ge e le m cce_star_owner_expression first_owner /\
    eval_expr ge e (PTree.set CCI._t'3 first_owner le) m
      cce_star_count_expression count /\
    ocn_test_value ge e (cce_star_count_locals le first_owner count) m
      cce_star_count_guard true /\
    eval_expr ge e (cce_star_count_locals le first_owner count) m
      cce_star_owner_expression second_owner /\
    eval_expr ge e (cce_star_entry_locals le first_owner count second_owner) m
      cce_star_entry_expression value /\
    eval_expr ge e
      (PTree.set CCI._object value (cce_star_entry_locals le first_owner count second_owner)) m
      (cce_star_type_expression version) kind /\
    ocn_test_value ge e (cce_star_match_locals le first_owner count second_owner value kind) m
      cce_star_match_guard true /\ ty = cce_star_object_type /\ m' = m /\ t = E0.
Proof.
  intros version ge e le m t le' m' value ty Hrun.
  rewrite cce_star_iteration_source_exact in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  match goal with Hreturn : eval_expr _ _ _ _ (Etempvar CCI._object _) _ |- _ =>
    inversion Hreturn; subst; clear Hreturn
  end.
  - repeat match goal with Hread : (PTree.set _ _ _) ! _ = Some _ |- _ =>
      rewrite PTree.gso in Hread by discriminate;
      rewrite PTree.gss in Hread; inversion Hread; subst; clear Hread
    end.
    match goal with
    | Hfirst : eval_expr _ _ ?initial _ cce_star_owner_expression ?first_owner,
      Hcount : eval_expr _ _ _ _ cce_star_count_expression ?count,
      Hsecond : eval_expr _ _ (PTree.set CCI._t'4 ?count
        (PTree.set CCI._t'3 ?first_owner ?initial)) _ cce_star_owner_expression ?second_owner,
      Hkind : eval_expr _ _ _ _ (cce_star_type_expression version) ?kind |- _ =>
      exists first_owner, count, second_owner, kind
    end.
    unfold cce_star_count_locals, cce_star_entry_locals, cce_star_match_locals.
    repeat split; try assumption; try reflexivity; unfold ocn_test_value; eauto.
  - match goal with Hlv : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ =>
      inversion Hlv end.
Qed.

(** The no-write result includes function entry and return, not just a
    hypothetical body environment. Both generated functions have no stack
    variables, so neither allocation nor freeing changes the memory. *)
Theorem cce_search_call_preserves_memory : forall version consumer args m t m' result,
  consumer = CCPairSearch \/ consumer = CCStarSearch ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ccs_body version consumer)) args t m' result ->
  t = E0 /\ m' = m.
Proof.
  intros version consumer args m t m' result Hconsumer Hcall.
  assert (fn_vars (ccs_body version consumer) = []) as Hvars
    by (destruct version; destruct Hconsumer as [Hc | Hc]; subst consumer; reflexivity).
  assert (exists keep, cce_readonly_keep keep (fn_body (ccs_body version consumer)) = true)
    as [keep Hpure].
  { destruct Hconsumer as [Hc | Hc]; subst consumer.
    - exists CCH._obj1. exact (proj1 (cce_search_source_is_readonly version)).
    - exists CCI._m. exact (proj1 (proj2 (proj2 (cce_search_source_is_readonly version)))). }
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _
      (fn_body (ccs_body _ _)) _ _ _ _ |- _ =>
    pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hbody Hpure)
      as (Htrace & Hmemory & _); subst end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  split; reflexivity.
Qed.

(** Calls may change memory, but cannot change an enclosing function's
    argument temporary unless the source explicitly assigns that temporary
    as a result. This is not an object-lifetime or object-content frame. *)
Fixpoint cce_keeps_temp (keep : ident) (s : statement) : bool := match s with
| Sskip | Sassign _ _ | Sbreak | Scontinue | Sreturn _ => true
| Sset id _ => negb (Pos.eqb id keep)
| Scall result _ _ | Sbuiltin result _ _ _ =>
    match result with None => true | Some id => negb (Pos.eqb id keep) end
| Ssequence a b | Sifthenelse _ a b | Sloop a b =>
    cce_keeps_temp keep a && cce_keeps_temp keep b
| _ => false end.

Lemma cce_argument_temporary_is_preserved : forall ge e le m s t le' m' out keep,
  ocn_exec ge e le m s t le' m' out -> cce_keeps_temp keep s = true ->
  le' ! keep = le ! keep.
Proof.
  intros ge e le m s t le' m' out keep Hrun.
  induction Hrun; cbn; intro Hshape; try discriminate; try reflexivity.
  - apply negb_true_iff in Hshape. apply Pos.eqb_neq in Hshape.
    apply PTree.gso. congruence.
  - destruct optid; [|reflexivity].
    apply negb_true_iff in Hshape. apply Pos.eqb_neq in Hshape.
    apply PTree.gso. congruence.
  - destruct optid; [|reflexivity].
    apply negb_true_iff in Hshape. apply Pos.eqb_neq in Hshape.
    apply PTree.gso. congruence.
  - apply andb_true_iff in Hshape as [Ha Hb]. rewrite (IHHrun2 Hb). auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. rewrite (IHHrun2 Hb). auto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    rewrite (IHHrun3 (andb_true_intro (conj Ha Hb))), (IHHrun2 Hb). auto.
Qed.

Theorem cce_star_award_body_preserves_mario_and_star_arguments :
  forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (rank9a_body version R9Collect)) t le' m' out ->
  le' ! CCI._m = le ! CCI._m /\ le' ! CCI._o = le ! CCI._o.
Proof.
  intros version e le m t le' m' out Hrun.
  assert (cce_keeps_temp CCI._m (fn_body (rank9a_body version R9Collect)) = true /\
    cce_keeps_temp CCI._o (fn_body (rank9a_body version R9Collect)) = true)
    as [Hm Ho] by (destruct version; vm_compute; split; reflexivity).
  split; eapply cce_argument_temporary_is_preserved; eauto.
Qed.

Lemma cce_pointer_comparison_identifies_object : forall m candidate target offset answer,
  option_map Val.of_bool
    (Val.cmpu_bool (Mem.valid_pointer m) Ceq candidate (Vptr target offset)) = Some answer ->
  bool_val answer tint m = Some true -> candidate = Vptr target offset.
Proof.
  intros m candidate target offset answer Hcmp Hbool.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) Ceq candidate (Vptr target offset))
    as [equal |] eqn:Htest; cbn in Hcmp; try discriminate.
  injection Hcmp as Hanswer. subst answer.
  destruct equal; cbn in Hbool; vm_compute in Hbool; try discriminate.
  destruct candidate as [|integer|long|double|single|other other_offset];
    cbn [Val.cmpu_bool Archi.ptr64] in Htest; try discriminate.
  - match type of Htest with context [if ?valid then _ else _] =>
      destruct valid; discriminate end.
  - destruct (eq_block other target) as [Hsame | Hdifferent].
    + subst other.
      match type of Htest with context [if ?valid then _ else _] =>
        destruct valid; try discriminate end.
      change (Some (Ptrofs.eq other_offset offset) = Some true) in Htest.
      injection Htest as Heq. pose proof (Ptrofs.eq_spec other_offset offset) as Hoffset.
      rewrite Heq in Hoffset. subst other_offset. reflexivity.
    + match type of Htest with context [if ?valid then _ else _] =>
        destruct valid; discriminate end.
Qed.

Lemma cce_pair_match_identifies_the_read_pointer : forall ge e le m candidate target offset,
  le ! CCH._t'1 = Some candidate -> le ! CCH._obj2 = Some (Vptr target offset) ->
  ocn_test_value ge e le m cce_pair_match_guard true -> candidate = Vptr target offset.
Proof.
  intros ge e le m candidate target offset Hcandidate Htarget [answer [Hexpr Hbool]].
  unfold cce_pair_match_guard in Hexpr. inversion Hexpr; subst.
  - match goal with
    | Ha : eval_expr _ _ _ _ (Etempvar CCH._t'1 _) ?va,
      Hb : eval_expr _ _ _ _ (Etempvar CCH._obj2 _) ?vb |- _ =>
      assert (va = candidate) by (eapply ocn_temp_value; eauto);
      assert (vb = Vptr target offset) by (eapply ocn_temp_value; eauto); subst
    end.
    match goal with Hsem : sem_binary_operation _ Oeq _ _ _ _ _ = Some answer |- _ =>
      change (option_map Val.of_bool
        (Val.cmpu_bool (Mem.valid_pointer m) Ceq candidate (Vptr target offset)) = Some answer)
        in Hsem;
      eapply cce_pointer_comparison_identifies_object; eauto
    end.
  - match goal with Hlv : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ =>
      inversion Hlv end.
Qed.

(** For the requested second Object pointer, success really reads that exact
    pointer from obj1's indexed list in the unchanged input memory. The
    current list bound is checked at that same iteration. *)
Theorem cce_successful_pair_search_reads_requested_object :
  forall version e le m t le' m' target offset,
  le ! CCH._obj2 = Some (Vptr target offset) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ccs_body version CCPairSearch)) t le' m'
    (Out_return (Some (Vint Int.one, tint))) ->
  t = E0 /\ m' = m /\ exists il count,
    il ! CCH._obj1 = le ! CCH._obj1 /\
    il ! CCH._obj2 = Some (Vptr target offset) /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e il m
      cce_pair_count_expression count /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (PTree.set CCH._t'2 count il) m cce_pair_entry_expression (Vptr target offset) /\
    ocn_test_value (Clight.globalenv (selected_clight_target version)) e
      (PTree.set CCH._t'2 count il) m cce_pair_count_guard true.
Proof.
  intros version e le m t le' m' target offset Htarget Hrun.
  pose proof (cce_pair_search_preserves_memory_and_arguments _ _ _ _ _ _ _ _ Hrun)
    as (Ht & Hm & _). subst t m'. split; [reflexivity |]. split; [reflexivity |].
  assert (Hnonzero : Vint Int.one <> Vint Int.zero) by (vm_compute; discriminate).
  destruct (cce_successful_search_reaches_returning_iteration
    version CCPairSearch e le m E0 le' m (Vint Int.one) tint
    (or_introl eq_refl) Hnonzero Hrun) as (il & im & it & Hiter & Hframe).
  destruct (cce_search_source_is_readonly version) as (Hobj1 & Hobj2 & _).
  pose proof (Hframe _ Hobj1) as [Hmemory Hone].
  pose proof (Hframe _ Hobj2) as [_ Htwo]. subst im.
  destruct (cce_pair_iteration_reads_a_matching_entry _ _ _ _ _ _ _ _ _ _ Hiter)
    as (count & candidate & Hcount & Hentry & Hbound & Hmatch & _).
  assert (candidate = Vptr target offset) as Hsame.
  { eapply cce_pair_match_identifies_the_read_pointer; [apply PTree.gss | | exact Hmatch].
    rewrite !PTree.gso by discriminate. rewrite Htwo. exact Htarget. }
  subst candidate. exists il, count. repeat split; try assumption; congruence.
Qed.

Theorem cce_successful_star_search_reads_returned_object :
  forall version e le m t le' m' target offset ty,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ccs_body version CCStarSearch)) t le' m'
    (Out_return (Some (Vptr target offset, ty))) ->
  t = E0 /\ m' = m /\ exists il first_owner count second_owner kind,
    il ! CCI._m = le ! CCI._m /\ il ! CCI._interactType = le ! CCI._interactType /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e il m
      cce_star_owner_expression first_owner /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (PTree.set CCI._t'3 first_owner il) m cce_star_count_expression count /\
    ocn_test_value (Clight.globalenv (selected_clight_target version)) e
      (cce_star_count_locals il first_owner count) m cce_star_count_guard true /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (cce_star_count_locals il first_owner count) m cce_star_owner_expression second_owner /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (cce_star_entry_locals il first_owner count second_owner) m
      cce_star_entry_expression (Vptr target offset) /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (PTree.set CCI._object (Vptr target offset)
        (cce_star_entry_locals il first_owner count second_owner)) m
      (cce_star_type_expression version) kind /\
    ocn_test_value (Clight.globalenv (selected_clight_target version)) e
      (cce_star_match_locals il first_owner count second_owner (Vptr target offset) kind)
      m cce_star_match_guard true.
Proof.
  intros version e le m t le' m' target offset ty Hrun.
  pose proof (cce_star_search_preserves_memory_and_arguments _ _ _ _ _ _ _ _ Hrun)
    as (Ht & Hm & _). subst t m'. split; [reflexivity |]. split; [reflexivity |].
  destruct (cce_successful_search_reaches_returning_iteration
    version CCStarSearch e le m E0 le' m (Vptr target offset) ty
    (or_intror eq_refl) ltac:(discriminate) Hrun) as (il & im & it & Hiter & Hframe).
  destruct (cce_search_source_is_readonly version) as (_ & _ & Hmario & Hkind).
  pose proof (Hframe _ Hmario) as [Hmemory HmarioLocal].
  pose proof (Hframe _ Hkind) as [_ HkindLocal]. subst im.
  destruct (cce_star_iteration_returns_a_recorded_entry _ _ _ _ _ _ _ _ _ _ Hiter)
    as (first_owner & count & second_owner & kind & Hreads).
  exists il, first_owner, count, second_owner, kind. tauto.
Qed.
