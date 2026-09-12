(** A certificate for a call-free, store-free path through an actual Clight
    statement. Unselected branches are unrestricted. Soundness and uniqueness
    are proved against Clight2, not an alternative gameplay transition. *)
From Coq Require Import List.
From compcert Require Import Clight ClightBigstep Cop Events Maps Memory Values.
From LessThanOneAPress.Proofs Require Import ObjectContactReadback.

Inductive readonly_path (ge : genv) (e : env) (m : mem) :
    temp_env -> statement -> temp_env -> Prop :=
| ro_skip : forall le, readonly_path ge e m le Sskip le
| ro_set : forall le id a v,
    eval_expr ge e le m a v ->
    readonly_path ge e m le (Sset id a) (PTree.set id v le)
| ro_seq : forall le middle final first second,
    readonly_path ge e m le first middle ->
    readonly_path ge e m middle second final ->
    readonly_path ge e m le (Ssequence first second) final
| ro_if : forall le final a yes no v choice,
    eval_expr ge e le m a v ->
    bool_val v (typeof a) m = Some choice ->
    readonly_path ge e m le (if choice then yes else no) final ->
    readonly_path ge e m le (Sifthenelse a yes no) final.

Theorem readonly_path_executes : forall ge e m le s final,
  readonly_path ge e m le s final ->
  ClightBigstep.Clight2.exec_stmt ge e le m s E0 final m Out_normal.
Proof.
  intros ge e m le s final H. induction H.
  - constructor.
  - constructor; assumption.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto.
  - eapply exec_Sifthenelse; eauto.
Qed.

Theorem readonly_path_forces_every_execution : forall ge e m le s final,
  readonly_path ge e m le s final ->
  forall trace le' m' out,
  ClightBigstep.Clight2.exec_stmt ge e le m s trace le' m' out ->
  trace = E0 /\ le' = final /\ m' = m /\ out = Out_normal.
Proof.
  intros ge e m le s final Hpath. induction Hpath;
    intros trace le' m' out Hrun; inversion Hrun; subst.
  - repeat split; reflexivity.
  - match goal with Hv : eval_expr _ _ _ _ _ ?v,
      Hw : eval_expr _ _ _ _ _ ?w |- _ =>
      assert (v = w) by (eapply ocr_expr_unique; eauto); subst end.
    repeat split; reflexivity.
  - match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ first _ _ _ Out_normal |- _ =>
      destruct (IHHpath1 _ _ _ _ Hfirst) as (? & ? & ? & ?); subst end.
    match goal with Hlast : ClightBigstep.exec_stmt _ _ _ _ _ second _ _ _ _ |- _ =>
      destruct (IHHpath2 _ _ _ _ Hlast) as (? & ? & ? & ?); subst end.
    repeat split; reflexivity.
  - match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ first _ _ _ _ |- _ =>
      destruct (IHHpath1 _ _ _ _ Hfirst) as (? & ? & ? & ?); subst end.
    contradiction.
  - match goal with Hv : eval_expr _ _ _ _ _ ?v,
      Hw : eval_expr _ _ _ _ _ ?w |- _ =>
      assert (v = w) by (eapply ocr_expr_unique; eauto); subst end.
    match goal with H1 : bool_val ?v ?ty ?m = Some ?b,
      H2 : bool_val ?v ?ty ?m = Some ?c |- _ =>
      assert (b = c) by congruence; subst end.
    eapply IHHpath; eauto.
Qed.
