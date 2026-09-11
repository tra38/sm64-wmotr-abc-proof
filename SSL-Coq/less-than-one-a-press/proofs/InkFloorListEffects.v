(** The real floor-list traversal only writes its height output. This covers
    every completed generated US/JP traversal, including early rejection,
    camera filters and list order. It does not identify the selected floor. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ObjectContactNecessity
  ContactConsumerExecution UpperElevatorQueryResolution.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IFL := UEQR_UC.

(** A structural induction over actual Clight executions. Both semantic
    write/call obligations below are discharged for the floor helpers. *)
Fixpoint ifl_shape keep (write_ok : expr -> bool)
    (call_ok : expr -> list expr -> bool) (s : statement) : bool :=
  match s with
  | Sskip | Sbreak | Scontinue | Sreturn _ => true
  | Sset id _ => negb (Pos.eqb id keep)
  | Sassign lhs _ => write_ok lhs
  | Scall opt fn args =>
      (match opt with None => true | Some id => negb (Pos.eqb id keep) end)
        && call_ok fn args
  | Ssequence a b | Sifthenelse _ a b | Sloop a b =>
      ifl_shape keep write_ok call_ok a && ifl_shape keep write_ok call_ok b
  | _ => false
  end.

Lemma ifl_set_keep : forall (le : temp_env) id keep v,
  negb (Pos.eqb id keep) = true -> (PTree.set id v le) ! keep = le ! keep.
Proof.
  intros. apply negb_true_iff in H. apply Pos.eqb_neq in H.
  apply PTree.gso. congruence.
Qed.

Theorem ifl_checked_frame : forall ge e keep pointer (observe : mem -> option val)
    write_ok call_ok,
  (forall le m lhs rhs t le' m' out,
    le ! keep = Some pointer -> write_ok lhs = true ->
    ocn_exec ge e le m (Sassign lhs rhs) t le' m' out ->
    t = E0 /\ observe m' = observe m) ->
  (forall le m opt fn args t le' m' out,
    le ! keep = Some pointer -> call_ok fn args = true ->
    ocn_exec ge e le m (Scall opt fn args) t le' m' out ->
    t = E0 /\ observe m' = observe m) ->
  forall le m s t le' m' out,
    ocn_exec ge e le m s t le' m' out ->
    ifl_shape keep write_ok call_ok s = true -> le ! keep = Some pointer ->
    t = E0 /\ observe m' = observe m /\ le' ! keep = Some pointer.
Proof.
  intros ge e keep pointer observe write_ok call_ok Hwrite Hcall
    le m s t le' m' out Hrun.
  induction Hrun; cbn [ifl_shape]; intros Hshape Hkeep; try discriminate;
    try solve [repeat split; auto].
  - destruct (Hwrite _ _ _ _ _ _ _ _ Hkeep Hshape ltac:(econstructor; eauto)).
    auto.
  - repeat split; auto. rewrite ifl_set_keep by exact Hshape. exact Hkeep.
  - apply andb_true_iff in Hshape as [Hfresh Hallowed].
    destruct (Hcall le m optid a al t (set_opttemp optid vres le) m' Out_normal
      Hkeep Hallowed ltac:(econstructor; eauto)).
    repeat split; auto. destruct optid; cbn; auto.
    rewrite ifl_set_keep by exact Hfresh. exact Hkeep.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Hwrite Hcall Ha Hkeep) as (-> & Hfirst & Hmiddle).
    destruct (IHHrun2 Hwrite Hcall Hb Hmiddle) as (-> & Hsecond & Hfinal).
    repeat split; auto; congruence.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Hwrite Hcall Ha Hkeep) as (-> & Hfirst & Hmiddle).
    destruct (IHHrun2 Hwrite Hcall Hb Hmiddle) as (-> & Hsecond & Hfinal).
    repeat split; auto; congruence.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Hwrite Hcall Ha Hkeep) as (-> & Hfirst & Hmiddle).
    destruct (IHHrun2 Hwrite Hcall Hb Hmiddle) as (-> & Hsecond & Hnext).
    destruct (IHHrun3 Hwrite Hcall (andb_true_intro (conj Ha Hb)) Hnext)
      as (-> & Hthird & Hfinal).
    repeat split; auto; congruence.
  Unshelve. all: exact None.
Qed.

Definition ifl_pointer_write id ty lhs := match lhs with
  | Ederef (Etempvar found pty) actual =>
      Pos.eqb found id &&
      (if type_eq pty (tptr ty) then if type_eq actual ty then true else false else false)
  | _ => false end.

Lemma ifl_pointer_write_exact : forall id ty lhs,
  ifl_pointer_write id ty lhs = true -> lhs = Ederef (Etempvar id (tptr ty)) ty.
Proof.
  intros id ty lhs. destruct lhs; try discriminate.
  destruct lhs; try discriminate. cbn [ifl_pointer_write].
  intro H. apply andb_true_iff in H as [Hid Htypes]. apply Pos.eqb_eq in Hid.
  destruct (type_eq t0 (tptr ty)); try discriminate.
  destruct (type_eq t ty); try discriminate. subst. reflexivity.
Qed.

Lemma ifl_pointer_store : forall ge e le m id ty chunk b ofs rhs t le' m' out,
  le ! id = Some (Vptr b ofs) -> access_mode ty = By_value chunk ->
  ocn_exec ge e le m (Sassign (Ederef (Etempvar id (tptr ty)) ty) rhs) t le' m' out ->
  t = E0 /\ exists value, Mem.store chunk m b (Ptrofs.unsigned ofs) value = Some m'.
Proof.
  intros ge e le m id ty chunk b ofs rhs t le' m' out Hptr Hmode Hrun.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ =>
    inversion Hl; subst; clear Hl end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar id _) ?value |- _ =>
    assert (value = Vptr b ofs) as Hvalue by (eapply ocn_temp_value; eauto);
    inversion Hvalue; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    cbn [typeof] in Ha;
    inversion Ha; subst; try congruence end.
  match goal with Haccess : access_mode ty = By_value _ |- _ =>
    rewrite Hmode in Haccess; inversion Haccess; subst end.
  split; [reflexivity|]. eexists; eassumption.
Qed.

Definition ifl_disjoint (target : block) offset length chunk (b : block) ofs :=
  b <> target \/ ofs + size_chunk chunk <= offset \/ offset + length <= ofs.

Lemma ifl_source : forall version,
  fn_vars (ueqr_native_body version UEQRFindFloorFromList) = [] /\
  fn_params (ueqr_native_body version UEQRFindFloorFromList) =
    [(IFL._surfaceNode, tptr (Tstruct IFL._SurfaceNode noattr));
     (IFL._x, tint); (IFL._y, tint); (IFL._z, tint); (IFL._pheight, tptr tfloat)] /\
  ifl_shape IFL._pheight (ifl_pointer_write IFL._pheight tfloat) (fun _ _ => false)
    (fn_body (ueqr_native_body version UEQRFindFloorFromList)) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem ifl_completed_list_only_writes_height :
  forall version ge m node x y z hb ho t m' result,
  ClightBigstep.Clight2.eval_funcall ge m
    (Internal (ueqr_native_body version UEQRFindFloorFromList))
    [node; x; y; z; Vptr hb ho] t m' result ->
  t = E0 /\ forall chunk b ofs,
    ifl_disjoint hb (Ptrofs.unsigned ho) 4 chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version ge m node x y z hb ho t m' result Hcall.
  destruct (ifl_source version) as (Hvars & Hparams & Hshape).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IFL._pheight = Some (Vptr hb ho)) as Hptr by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ ?initial (fn_body _) _ _ _ _ |- _ =>
    rename initial into m end.
  assert (forall chunk b ofs, ifl_disjoint hb (Ptrofs.unsigned ho) 4 chunk b ofs ->
    t = E0 /\ Mem.load chunk m' b ofs = Mem.load chunk m b ofs) as Hframe.
  { intros chunk b ofs Hseparate.
    lazymatch goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
      destruct (ifl_checked_frame ge empty_env IFL._pheight (Vptr hb ho)
        (fun memory => Mem.load chunk memory b ofs)
        (ifl_pointer_write IFL._pheight tfloat) (fun _ _ => false)
        ltac:(intros temps memory lhs rhs tr last after outcome Hp Hw Hs;
          apply ifl_pointer_write_exact in Hw; subst lhs;
          destruct (ifl_pointer_store _ _ _ _ _ tfloat Mfloat32 _ _ _ _ _ _ _ Hp eq_refl Hs)
            as (Ht & value & Hstore); split; [exact Ht|];
          eapply Mem.load_store_other; [exact Hstore|exact Hseparate])
        ltac:(intros; discriminate) _ _ _ _ _ _ _ Hr Hshape Hptr)
        as (Ht & Hloads & _); auto end. }
  split.
  - exact (proj1 (Hframe Mfloat32 hb (Ptrofs.unsigned ho + 4) ltac:(right; right; lia))).
  - intros chunk b ofs Hdisjoint; exact (proj2 (Hframe _ _ _ Hdisjoint)).
Qed.
