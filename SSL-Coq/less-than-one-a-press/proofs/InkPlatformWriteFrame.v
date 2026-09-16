(** Memory footprints for the actual platform-displacement helpers.
    A syntactic root certificate is proved sound for Clight evaluation;
    it is not a frame assumption about arbitrary outside calls. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Inductive ipw_root := IPWvar (id : ident) | IPWtemp (id : ident).
Definition ipw_aggregate ty := match access_mode ty with
| By_reference | By_copy => true | _ => false end.
Fixpoint ipw_roots (a : expr) : option ipw_root * option ipw_root :=
  match a with
  | Evar id ty =>
      (if ipw_aggregate ty then Some (IPWvar id) else None, Some (IPWvar id))
  | Etempvar id _ => (Some (IPWtemp id), None)
  | Ederef p ty =>
      (if ipw_aggregate ty then fst (ipw_roots p) else None, fst (ipw_roots p))
  | Efield p _ ty =>
      (if ipw_aggregate ty then fst (ipw_roots p) else None, fst (ipw_roots p))
  | Eaddrof p _ => (snd (ipw_roots p), None)
  | Ebinop Oadd p i _ =>
      (match classify_add (typeof p) (typeof i) with
       | add_case_pi _ _ => fst (ipw_roots p)
       | _ => None end, None)
  | _ => (None, None)
  end.

Definition ipw_root_safe (ge : genv) (e : env) (le : temp_env) ob r : Prop := match r with
| IPWvar id =>
    (forall b ty, e ! id = Some (b,ty) -> b <> ob) /\
    (e ! id = None -> forall b, Genv.find_symbol ge id = Some b -> b <> ob)
| IPWtemp id => forall b ofs, le ! id = Some (Vptr b ofs) -> b <> ob
end.

Lemma ipw_add_preserves_block : forall ce m a i ty si v w result,
  classify_add a i = add_case_pi ty si ->
  sem_binary_operation ce Oadd v a w i m = Some result ->
  forall b ofs, result = Vptr b ofs -> exists off, v = Vptr b off.
Proof.
  intros ce m a i ty si v w result Hclass Hsem b ofs E. subst result.
  unfold sem_binary_operation, sem_add in Hsem. rewrite Hclass in Hsem.
  destruct v, w; try discriminate; inversion Hsem; subst; eauto.
Qed.

Lemma ipw_lvalue_roots : forall ge e le m a b ofs bf,
  eval_lvalue ge e le m a b ofs bf ->
  fst (ipw_roots a) =
    if ipw_aggregate (typeof a) then snd (ipw_roots a) else None.
Proof. intros; inversion H; subst; reflexivity. Qed.

Lemma ipw_root_sound : forall ge e le m,
  (forall a v, eval_expr ge e le m a v ->
    forall r ob, fst (ipw_roots a) = Some r -> ipw_root_safe ge e le ob r ->
    forall b ofs, v = Vptr b ofs -> b <> ob) /\
  (forall a b ofs bf, eval_lvalue ge e le m a b ofs bf ->
    forall r ob, snd (ipw_roots a) = Some r -> ipw_root_safe ge e le ob r -> b <> ob).
Proof.
  intros ge e le m. apply eval_expr_lvalue_ind; intros;
    cbn [ipw_roots fst snd] in *; try discriminate.
  - inversion H0; subst. eapply H1; eauto.
  - inversion H3; subst. eapply H0; eauto.
  - destruct op; cbn in H4; try discriminate.
    destruct (classify_add (typeof a1) (typeof a2)) eqn:C; try discriminate.
    destruct (ipw_add_preserves_block _ _ _ _ _ _ _ _ _ C H3 _ _ H6) as [off E].
    eapply H0; eauto.
  - rewrite (ipw_lvalue_roots _ _ _ _ _ _ _ _ H) in H2.
    unfold ipw_aggregate in H2. inversion H1; subst;
      try match goal with Hm : access_mode _ = _ |- _ => rewrite Hm in H2 end;
      try discriminate.
    all: try match goal with E : Vptr _ _ = Vptr _ _ |- _ =>
      inversion E; subst; eapply H0; eauto end.
    inversion H5.
  - inversion H0; subst. destruct H1 as [Hlocal _]. eapply Hlocal; eauto.
  - inversion H1; subst. destruct H2 as [_ Hglobal]. eapply Hglobal; eauto.
  - eapply H0; eauto.
  - eapply H0; eauto.
  - eapply H0; eauto.
Qed.

Definition ipw_member (id : ident) ids := existsb (Pos.eqb id) ids.
Lemma ipw_member_spec : forall id ids, ipw_member id ids = true <-> In id ids.
Proof.
  intros. unfold ipw_member. rewrite existsb_exists.
  split.
  - intros [x [Hx E]]. apply Pos.eqb_eq in E. subst; assumption.
  - intro H. exists id. split; auto. apply Pos.eqb_refl.
Qed.
Definition ipw_allowed vars temps r := match r with
| IPWvar id => ipw_member id vars | IPWtemp id => ipw_member id temps end.
Definition ipw_context ge e le ob vars temps trues : Prop :=
  (forall id, In id vars -> ipw_root_safe ge e le ob (IPWvar id)) /\
  (forall id, In id temps -> ipw_root_safe ge e le ob (IPWtemp id)) /\
  (forall id, In id trues -> le ! id = Some (Vint Int.one)).
Definition ipw_frame ob before after := forall chunk ofs,
  Mem.load chunk after ob ofs = Mem.load chunk before ob ofs.

Definition ipw_write vars temps lhs : bool :=
  (match lhs with Evar _ _ | Ederef _ _ => true | _ => false end) &&
  (match access_mode (typeof lhs) with By_value _ => true | _ => false end) &&
  (match snd (ipw_roots lhs) with Some r => ipw_allowed vars temps r | None => false end).
Definition ipw_true trues a := match a with
| Etempvar id tint => ipw_member id trues &&
    (if type_eq tint tuint then true else false)
| _ => false end.

Lemma ipw_context_root : forall ge e le ob vars temps trues r,
  ipw_context ge e le ob vars temps trues ->
  ipw_allowed vars temps r = true -> ipw_root_safe ge e le ob r.
Proof.
  intros ge e le ob vars temps trues [] [Hv [Ht Htrue]] H;
    apply ipw_member_spec in H; auto.
Qed.

Lemma ipw_write_frame : forall ge e le ob vars temps trues lhs rhs m t le' m' out,
  ipw_context ge e le ob vars temps trues -> ipw_write vars temps lhs = true ->
  ClightBigstep.Clight2.exec_stmt ge e le m (Sassign lhs rhs) t le' m' out ->
  t = E0 /\ ipw_frame ob m m'.
Proof.
  intros ge e le ob vars temps trues lhs rhs m t le' m' out Hctx Hshape Hrun.
  unfold ipw_write in Hshape. apply andb_true_iff in Hshape as [Hlm Hroot].
  apply andb_true_iff in Hlm as [Hlhs Hmode].
  destruct (snd (ipw_roots lhs)) as [r|] eqn:Hr; try discriminate.
  pose proof (ipw_context_root _ _ _ _ _ _ _ _ Hctx Hroot) as Hsafe.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ ?b _ ?field |- _ =>
    assert (b <> ob) as Hother by
      (eapply (proj2 (ipw_root_sound _ _ _ _)); [exact Hl|exact Hr|exact Hsafe]);
    assert (field = Full) as -> by (destruct lhs; try discriminate; inversion Hl; reflexivity)
  end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
  - split; [reflexivity|]. intros observed offset.
    match goal with Hs : Mem.storev _ _ _ _ = Some _ |- _ =>
      eapply Mem.load_store_other; [exact Hs|left; congruence] end.
  - match goal with Hm : access_mode _ = By_copy |- _ => rewrite Hm in Hmode; discriminate end.
Qed.

Lemma ipw_set_context : forall ge e le ob vars temps trues id value,
  ipw_context ge e le ob vars temps trues ->
  ipw_member id (temps ++ trues) = false ->
  ipw_context ge e (PTree.set id value le) ob vars temps trues.
Proof.
  intros ge e le ob vars temps trues id value [Hv [Ht Htr]] Hfresh.
  assert (~ In id (temps ++ trues)) as Hnot
    by (intro H; apply ipw_member_spec in H; congruence).
  split; [exact Hv|]. split.
  - intros j Hj b ofs Hread. rewrite PTree.gso in Hread by
      (intro; subst; apply Hnot; apply in_or_app; auto).
    eapply Ht; eauto.
  - intros j Hj. rewrite PTree.gso by
      (intro; subst; apply Hnot; apply in_or_app; auto). auto.
Qed.

Lemma ipw_forced_true : forall ge e le m ob vars temps trues a value choice,
  ipw_context ge e le ob vars temps trues -> ipw_true trues a = true ->
  eval_expr ge e le m a value -> bool_val value (typeof a) m = Some choice ->
  choice = true.
Proof.
  intros ge e le m ob vars temps trues a value choice [_ [_ Htrue]] Hshape Hr Hb.
  destruct a; try discriminate. cbn [ipw_true] in Hshape.
  apply andb_true_iff in Hshape as [Hid Hty].
  destruct (type_eq t tuint); try discriminate. subst.
  apply ipw_member_spec in Hid. specialize (Htrue _ Hid).
  inversion Hr; subst.
  - assert (value = Vint Int.one) by congruence. subst.
    change (Some true = Some choice) in Hb; congruence.
  - match goal with H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end.
Qed.

Fixpoint ipw_shape vars temps trues (call_ok : expr -> list expr -> bool) s : bool :=
  match s with
  | Sskip | Sbreak | Scontinue | Sreturn _ => true
  | Sset id _ => negb (ipw_member id (temps ++ trues))
  | Sassign lhs _ => ipw_write vars temps lhs
  | Scall None fn args => call_ok fn args
  | Ssequence a b | Sloop a b =>
      ipw_shape vars temps trues call_ok a && ipw_shape vars temps trues call_ok b
  | Sifthenelse test yes no =>
      if ipw_true trues test then ipw_shape vars temps trues call_ok yes
      else ipw_shape vars temps trues call_ok yes && ipw_shape vars temps trues call_ok no
  | _ => false end.

Theorem ipw_checked_frame : forall ge e ob vars temps trues call_ok,
  (forall le m fn args t le' m' out,
    ipw_context ge e le ob vars temps trues -> call_ok fn args = true ->
    ClightBigstep.Clight2.exec_stmt ge e le m (Scall None fn args) t le' m' out ->
    t = E0 /\ ipw_frame ob m m') ->
  forall le m s t le' m' out,
  ClightBigstep.Clight2.exec_stmt ge e le m s t le' m' out ->
  ipw_shape vars temps trues call_ok s = true ->
  ipw_context ge e le ob vars temps trues ->
  t = E0 /\ ipw_frame ob m m' /\ ipw_context ge e le' ob vars temps trues.
Proof.
  intros ge e ob vars temps trues call_ok Hcall le m s t le' m' out Hrun.
  unfold ipw_frame in *.
  induction Hrun; cbn [ipw_shape]; intros Hshape Hctx; try discriminate;
    try solve [split; [reflexivity|]; split; [intros; reflexivity|exact Hctx]].
  - destruct (ipw_write_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx Hshape
      ltac:(econstructor; eauto)) as [Ht Hframe]. auto.
  - split; [reflexivity|]. split; [intros; reflexivity|].
    eapply ipw_set_context; [exact Hctx|now apply negb_true_iff in Hshape].
  - destruct optid; try discriminate.
    destruct (Hcall le m a al t (set_opttemp None vres le) m' Out_normal Hctx Hshape
      ltac:(eapply exec_Scall with (vres := vres); eauto)) as [Ht Hframe]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Hcall Ha Hctx) as (-> & Hf1 & Hc1).
    destruct (IHHrun2 Hcall Hb Hc1) as (-> & Hf2 & Hc2).
    split; [reflexivity|]. split; [intros; rewrite Hf2, Hf1; reflexivity|exact Hc2].
  - apply andb_true_iff in Hshape as [Ha Hb]. eauto.
  - destruct (ipw_true trues a) eqn:Htrue.
    + assert (b = true) as -> by (eapply ipw_forced_true; eauto).
      eauto.
    + apply andb_true_iff in Hshape as [Ha Hb]. destruct b; eauto.
  - apply andb_true_iff in Hshape as [Ha Hb]. eauto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Hcall Ha Hctx) as (-> & Hf1 & Hc1).
    destruct (IHHrun2 Hcall Hb Hc1) as (-> & Hf2 & Hc2).
    split; [reflexivity|]. split; [intros; rewrite Hf2, Hf1; reflexivity|exact Hc2].
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Hcall Ha Hctx) as (-> & Hf1 & Hc1).
    destruct (IHHrun2 Hcall Hb Hc1) as (-> & Hf2 & Hc2).
    destruct (IHHrun3 Hcall (andb_true_intro (conj Ha Hb)) Hc2) as (-> & Hf3 & Hc3).
    split; [reflexivity|]. split;
      [intros; rewrite Hf3, Hf2, Hf1; reflexivity|exact Hc3].
Qed.


Definition ipw_value_safe ob value := forall b ofs, value = Vptr b ofs -> b <> ob.
Lemma ipw_cast_keeps_block : forall value from to m b ofs,
  sem_cast value from to m = Some (Vptr b ofs) -> value = Vptr b ofs.
Proof.
  intros value from to m b ofs H.
  unfold sem_cast in H. destruct (classify_cast from to); destruct value;
    cbn in H; try discriminate; try congruence;
    repeat match type of H with
    | context [if ?test then _ else _] => destruct test; try discriminate
    | context [match ?test with Some _ => _ | None => _ end] =>
        destruct test; try discriminate
    end; congruence.
Qed.


Definition ipw_inputs_safe (protected : list ident) ob
    (params : list (ident * type)) args :=
  Forall2 (fun param value => In (fst param) protected -> ipw_value_safe ob value) params args.
Definition ipw_temps_safe ob protected (le : temp_env) :=
  forall id b ofs, In id protected -> le ! id = Some (Vptr b ofs) -> b <> ob.

Lemma ipw_bind_safe : forall params args protected ob,
  ipw_inputs_safe protected ob params args ->
  forall initial final,
  bind_parameter_temps params args initial = Some final ->
  ipw_temps_safe ob protected initial -> ipw_temps_safe ob protected final.
Proof.
  intros params args protected ob Hsafe. induction Hsafe;
    intros initial final Hbind Hinitial; cbn in Hbind.
  - inversion Hbind; subst; assumption.
  - destruct x as [param ty]. cbn in Hbind, H.
    apply IHHsafe with (initial := PTree.set param y initial); [exact Hbind|].
    intros id b ofs Hid Hread. rewrite PTree.gsspec in Hread.
    destruct (peq id param) as [->|Hne].
    + inversion Hread; subst. eapply H; eauto.
    + eapply Hinitial; eauto.
Qed.

Lemma ipw_undef_safe : forall temps ob protected,
  ipw_temps_safe ob protected (create_undef_temps temps).
Proof.
  intros temps. induction temps as [|[id ty] rest IH]; intros ob protected j b ofs Hmem Hread;
    cbn in Hread.
  - rewrite PTree.gempty in Hread; discriminate.
  - rewrite PTree.gsspec in Hread. destruct (peq j id); try discriminate. eapply IH; eauto.
Qed.

Fixpoint ipw_arg_shapes vars temps protected (params : list (ident * type)) args : bool :=
  match params, args with
  | [], [] => true
  | (id,_) :: ps, arg :: rest =>
      (if ipw_member id protected then
        match fst (ipw_roots arg) with Some r => ipw_allowed vars temps r | None => false end
       else true) && ipw_arg_shapes vars temps protected ps rest
  | _, _ => false end.

Lemma ipw_arguments_safe : forall ge e le m ob vars temps trues protected params args values,
  ipw_context ge e le ob vars temps trues ->
  ipw_arg_shapes vars temps protected params args = true ->
  eval_exprlist ge e le m args (map snd params) values ->
  ipw_inputs_safe protected ob params values.
Proof.
  intros ge e le m ob vars temps trues protected params.
  induction params as [|[id ty] ps IH]; intros args values Hctx Hshape Heval.
  - destruct args; try discriminate. inversion Heval; constructor.
  - destruct args as [|arg rest]; try discriminate. cbn [ipw_arg_shapes] in Hshape.
    apply andb_true_iff in Hshape as [Harg Hrest]. inversion Heval; subst.
    constructor.
    + intros Hid b ofs E. cbn in Hid. apply ipw_member_spec in Hid. rewrite Hid in Harg.
      destruct (fst (ipw_roots arg)) as [root|] eqn:Hr; try discriminate.
      pose proof (ipw_context_root _ _ _ _ _ _ _ _ Hctx Harg) as Hsafe.
      subst. match goal with Hc : sem_cast _ _ _ _ = Some (Vptr b ofs) |- _ =>
        apply ipw_cast_keeps_block in Hc;
        eapply (proj1 (ipw_root_sound ge e le m)); eauto end.
    + eapply IH; eauto.
Qed.


Lemma ipw_alloc_frame : forall ge e m vars e' m',
  alloc_variables ge e m vars e' m' ->
  forall ob, Mem.valid_block m ob ->
  (forall id b ty, e ! id = Some (b,ty) -> b <> ob) ->
  (forall id b ty, e' ! id = Some (b,ty) -> b <> ob) /\
  ipw_frame ob m m' /\
  (forall id, ~ In id (map fst vars) -> e' ! id = e ! id).
Proof.
  intros ge e m vars e' m' Halloc. induction Halloc;
    intros ob Hvalid Henv.
  - split; [exact Henv|]. split; [intros chunk ofs; reflexivity|auto].
  - assert (b1 <> ob) as Hfresh by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
    destruct (IHHalloc ob (Mem.valid_block_alloc _ _ _ _ _ H _ Hvalid)
      ltac:(intros j b ty' Hread; rewrite PTree.gsspec in Hread;
        destruct (peq j id); [inversion Hread; subst; exact Hfresh|eapply Henv; eauto]))
      as (Henv' & Hframe & Houtside).
    split; [exact Henv'|]. split.
    + intros chunk ofs. rewrite Hframe. eapply Mem.load_alloc_unchanged; eauto.
    + intros j Hj. rewrite Houtside by (cbn in Hj; tauto).
      apply PTree.gso. intro E. subst. apply Hj. left; reflexivity.
Qed.
