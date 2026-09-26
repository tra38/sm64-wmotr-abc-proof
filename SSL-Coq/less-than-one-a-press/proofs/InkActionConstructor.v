(** Completed action initializers cannot manufacture a first long jump.
    Their callees keep their real memory effects; only the local action value
    is tracked here.  Caller history and physical input provenance are separate. *)
From Coq Require Import Bool List Lia ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkActionConstructorSource
  InkLandingHistoryReturn InkActionTimerReset InkBackwardSource InkBackwardExecution
  InkFloorResetExecution ContactConsumerExecution ObjectContactNecessity
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Opaque selected_clight_target.

Definition iai_safe_value (v : val) : Prop :=
  v <> Vint (Int.repr 50333832) /\ v <> Vint (Int.repr 1145).
Definition iai_safe_temps (le : temp_env) : Prop :=
  forall value, le ! IBM._action = Some value -> iai_safe_value value.
Definition iai_safe_result out : Prop := match out with
| Out_return (Some (v, ty)) => iai_safe_value v /\ ty = tuint
| _ => True end.
Definition iai_safe_integer i :=
  negb (Int.eq i (Int.repr 50333832)) && negb (Int.eq i (Int.repr 1145)).
Definition iai_set_ok id rhs :=
  if Pos.eqb id IBM._action then
    match rhs with Econst_int i _ => iai_safe_integer i | _ => false end
  else true.
Definition iai_dest_ok opt :=
  match opt with None => true | Some id => negb (Pos.eqb id IBM._action) end.

Fixpoint iai_statement_ok (s : statement) : bool := match s with
| Sskip | Sassign _ _ | Sbreak | Scontinue => true
| Sset id rhs => iai_set_ok id rhs
| Scall opt _ _ | Sbuiltin opt _ _ _ => iai_dest_ok opt
| Ssequence a b | Sifthenelse _ a b =>
    iai_statement_ok a && iai_statement_ok b
| Sswitch _ cases => iai_cases_ok cases
| Sreturn None => true
| Sreturn (Some (Etempvar id ty)) =>
    Pos.eqb id IBM._action && if type_eq ty tuint then true else false
| Sreturn _ => false
| Sloop _ _ | Slabel _ _ | Sgoto _ => false end
with iai_cases_ok cases : bool := match cases with
| LSnil => true
| LScons _ body rest => iai_statement_ok body && iai_cases_ok rest end.

Lemma iai_safe_integer_sound : forall i,
  iai_safe_integer i = true -> iai_safe_value (Vint i).
Proof.
  intros i H. apply andb_true_iff in H as [Ha Hb].
  apply negb_true_iff in Ha, Hb.
  unfold iai_safe_value. split; intros Heq; inversion Heq; subst;
    rewrite Int.eq_true in *; discriminate.
Qed.

Lemma iai_set_safe : forall le id rhs v ge e m,
  iai_safe_temps le -> iai_set_ok id rhs = true ->
  eval_expr ge e le m rhs v -> iai_safe_temps (PTree.set id v le).
Proof.
  intros le id rhs v ge e m Hsafe Hok Hread value Hget.
  unfold iai_set_ok in Hok. destruct (Pos.eqb id IBM._action) eqn:Hid.
  - apply Pos.eqb_eq in Hid. subst id. rewrite PTree.gss in Hget.
    inversion Hget; subst value. destruct rhs; try discriminate.
    apply ocn_const_int_value in Hread. subst v.
    now apply iai_safe_integer_sound.
  - apply Pos.eqb_neq in Hid. rewrite PTree.gso in Hget by congruence.
    exact (Hsafe value Hget).
Qed.

Lemma iai_opttemp_safe : forall le opt v,
  iai_safe_temps le -> iai_dest_ok opt = true ->
  iai_safe_temps (set_opttemp opt v le).
Proof.
  intros le [id|] v Hsafe Hok; cbn [set_opttemp] in *; [|exact Hsafe].
  unfold iai_dest_ok in Hok. apply negb_true_iff in Hok. apply Pos.eqb_neq in Hok.
  intros value Hget. rewrite PTree.gso in Hget by congruence. exact (Hsafe value Hget).
Qed.

Lemma iai_seq_cases : forall cases,
  iai_cases_ok cases = true -> iai_statement_ok (seq_of_labeled_statement cases) = true.
Proof.
  induction cases; cbn; auto. intros H. apply andb_true_iff in H as [Ha Hb].
  rewrite Ha, IHcases by exact Hb. reflexivity.
Qed.

Lemma iai_select_case_ok : forall cases n,
  iai_cases_ok cases = true ->
  match select_switch_case n cases with None => True | Some found => iai_cases_ok found = true end.
Proof.
  induction cases as [|[label|] body rest IH]; cbn; intros n H; auto;
    apply andb_true_iff in H as [Ha Hb].
  - destruct (zeq label n); cbn; [now rewrite Ha, Hb|exact (IH n Hb)].
  - exact (IH n Hb).
Qed.

Lemma iai_default_ok : forall cases,
  iai_cases_ok cases = true -> iai_cases_ok (select_switch_default cases) = true.
Proof.
  induction cases as [|[label|] body rest IH]; cbn; intros H; auto.
  - apply andb_true_iff in H as [Ha Hb]. auto.
Qed.

Lemma iai_selected_ok : forall cases n,
  iai_cases_ok cases = true ->
  iai_statement_ok (seq_of_labeled_statement (select_switch n cases)) = true.
Proof.
  intros cases n H. apply iai_seq_cases. unfold select_switch.
  pose proof (iai_select_case_ok cases n H) as Hcase.
  destruct (select_switch_case n cases); [exact Hcase|now apply iai_default_ok].
Qed.

Theorem iai_statement_keeps_non_target_action : forall ge e le m s t le' m' out,
  ocn_exec ge e le m s t le' m' out ->
  iai_statement_ok s = true -> iai_safe_temps le ->
  iai_safe_temps le' /\ iai_safe_result out.
Proof.
  intros ge e le m s t le' m' out Hrun. induction Hrun;
    cbn [iai_statement_ok]; intros Hok Hsafe;
    try discriminate; try (split; [exact Hsafe|exact I]).
  - split; [eapply iai_set_safe; eauto|exact I].
  - split; [eapply iai_opttemp_safe; eauto|exact I].
  - split; [eapply iai_opttemp_safe; eauto|exact I].
  - apply andb_true_iff in Hok as [Ha Hb].
    destruct (IHHrun1 Ha Hsafe) as [Hmid _]. exact (IHHrun2 Hb Hmid).
  - apply andb_true_iff in Hok as [Ha Hb]. exact (IHHrun Ha Hsafe).
  - apply andb_true_iff in Hok as [Ha Hb]. destruct b;
      [exact (IHHrun Ha Hsafe)|exact (IHHrun Hb Hsafe)].
  - destruct a; try discriminate.
    apply andb_true_iff in Hok as [Hid Hty]. apply Pos.eqb_eq in Hid; subst i.
    match type of Hty with (if type_eq ?ty tuint then _ else _) = true =>
      destruct (type_eq ty tuint); try discriminate; subst ty end.
    split; [exact Hsafe|]. split; [|reflexivity].
    match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ =>
      inversion Hr; subst; [eapply Hsafe; eassumption|] end.
    match goal with Hr : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion Hr end.
  - destruct (IHHrun (iai_selected_ok _ _ Hok) Hsafe) as [Hlast Hout].
    split; [exact Hlast|]. destruct out; exact I || exact Hout.
Qed.

Theorem iai_generated_initializers_only_keep_or_replace_with_safe_actions : forall version kind,
  iai_statement_ok (fn_body (iai_body version kind)) = true /\
  fn_vars (iai_body version kind) = [] /\
  fn_params (iai_body version kind) =
    [(IBM._m, tptr (Tstruct IBM._MarioState noattr));
     (IBM._action, tuint); (IBM._actionArg, tuint)] /\
  fn_return (iai_body version kind) = tuint.
Proof. intros [] []; vm_compute; repeat split; reflexivity. Qed.

Definition InkActionInitializerExclusion : Prop :=
  forall version kind m mario action arg t m' result,
  iai_safe_value action ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (iai_body version kind)) [mario; action; arg] t m' result ->
  iai_safe_value result.

Theorem iai_completed_initializer_cannot_manufacture_long_jump : InkActionInitializerExclusion.
Proof.
  intros version kind m mario action arg t m' result Hsafe Hcall.
  destruct (iai_generated_initializers_only_keep_or_replace_with_safe_actions version kind)
    as (Hshape & Hvars & Hparams & Hreturn).
  inversion Hcall; subst.
  match goal with H : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with H : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in H; inversion H; subst; clear H end.
  match goal with H : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (iai_safe_temps temps) as Htemps by
      (intros value Hget; rewrite Hparams in H; cbn in H; inversion H; subst;
       rewrite PTree.gso, PTree.gss in Hget by discriminate; inversion Hget; subst; exact Hsafe) end.
  match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (iai_statement_keeps_non_target_action _ _ _ _ _ _ _ _ _ H Hshape Htemps)
      as [_ Hout] end.
  match goal with H : outcome_result_value ?out _ _ _ |- _ =>
    rewrite Hreturn in H; destruct out as [| | |[ [v ty] |]]; cbn in H; try contradiction;
      unfold iai_safe_value; try (destruct H as [_ ->]; split; discriminate);
      destruct Hout as [Hv ->]; destruct H as [_ Hcast];
      destruct v; cbn in Hcast; try discriminate;
      inversion Hcast; subst; exact Hv end.
Qed.
