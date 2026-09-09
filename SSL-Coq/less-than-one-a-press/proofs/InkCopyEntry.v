(** Backward through the real vector-copy entry and its two writes before Y.
    Ordinary separate source/destination storage is an explicit premise;
    fresh local storage and the intervening memory effects are derived. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution ObjectContactNecessity ContactConsumerExecution
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ibc_local_init := Sassign (Evar IBV._dest (tptr tfloat))
  (Etempvar IBV._dest (tptr tfloat)).
Definition ibc_index (id : ident) (n : Z) := Ederef
  (Ebinop Oadd (Etempvar id (tptr tfloat))
    (Econst_int (Int.repr n) tint) (tptr tfloat)) tfloat.
Definition ibc_x_stage := Ssequence
  (Sset IBV._t'5 (Evar IBV._dest (tptr tfloat)))
  (Ssequence (Sset IBV._t'6 (ibc_index IBV._src 0))
    (Sassign (ibc_index IBV._t'5 0) (Etempvar IBV._t'6 tfloat))).

Lemma ibc_prefix_is_generated : forall version,
  ibk_copy_before_y version = [ibc_local_init; ibc_x_stage].
Proof. intros []; reflexivity. Qed.

(** No invented local environment: the actual function entry allocates one
    pointer cell and binds the two actual arguments to their temporaries. *)
Lemma ibc_actual_entry : forall version ge destination source m e le entry,
  function_entry2 ge (ibk_copy_body version) [destination; source] m e le entry ->
  exists local,
    Mem.alloc m 0 (sizeof ge (tptr tfloat)) = (entry, local) /\
    e = PTree.set IBV._dest (local, tptr tfloat) empty_env /\
    le ! IBV._dest = Some destination /\ le ! IBV._src = Some source.
Proof.
  intros version ge destination source m e le entry Hentry.
  assert (fn_vars (ibk_copy_body version) = [(IBV._dest, tptr tfloat)])
    as Hvars by (destruct version; reflexivity).
  inversion Hentry; subst; clear Hentry.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hnil : alloc_variables _ _ _ [] _ _ |- _ =>
    inversion Hnil; subst; clear Hnil end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some le |- _ =>
    destruct version; cbn in Hbind; inversion Hbind; subst le end;
    eexists; repeat split; eauto; reflexivity.
Qed.

Lemma ibc_local_location : forall ge e le m id b ty loc ofs bf,
  e ! id = Some (b, ty) ->
  eval_lvalue ge e le m (Evar id ty) loc ofs bf ->
  loc = b /\ ofs = Ptrofs.zero /\ bf = Full.
Proof. intros. inversion H0; subst; repeat split; congruence. Qed.

Lemma ibc_pointer_local_read : forall ge e le m id b value answer,
  e ! id = Some (b, tptr tfloat) ->
  Mem.load Mint32 m b 0 = Some value ->
  eval_expr ge e le m (Evar id (tptr tfloat)) answer -> answer = value.
Proof.
  intros ge e le m id b value answer Hlocal Hload Hexpr.
  inversion Hexpr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ Hlocal Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mint32 m b 0 = Some answer) in Hr; congruence end.
Qed.

Lemma ibc_index_location : forall ge e le m id n b ofs loc offset bf,
  le ! id = Some (Vptr b ofs) ->
  eval_lvalue ge e le m (ibc_index id n) loc offset bf ->
  loc = b /\
  offset = Ptrofs.add ofs
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr n))) /\
  bf = Full.
Proof.
  intros ge e le m id n b ofs loc offset bf Htemp Hl.
  unfold ibc_index in Hl. inversion Hl; subst.
  match goal with Hb : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hb; subst; clear Hb end.
  - match goal with Ht : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vptr b ofs) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hc : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hc; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn in Hsem; inversion Hsem; subst end.
    repeat split; reflexivity.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ =>
      inversion Hbad end.
Qed.

Lemma ibc_float_read : forall ge e le m id n b ofs answer,
  le ! id = Some (Vptr b ofs) ->
  eval_expr ge e le m (ibc_index id n) answer ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned (Ptrofs.add ofs
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr n))))) = Some answer.
Proof.
  intros ge e le m id n b ofs answer Htemp Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_index_location _ _ _ _ _ _ _ _ _ _ _ Htemp Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  assumption.
Qed.

Lemma ibc_local_init_store : forall ge e le m local destination t le' m' out,
  e ! IBV._dest = Some (local, tptr tfloat) ->
  le ! IBV._dest = Some destination ->
  (exists b ofs, destination = Vptr b ofs) ->
  ocn_exec ge e le m ibc_local_init t le' m' out ->
  Mem.store Mint32 m local 0 destination = Some m' /\
    t = E0 /\ le' = le /\ out = Out_normal.
Proof.
  intros ge e le m local destination t le' m' out Hlocal Htemp
    (b & ofs & ->) Hrun.
  unfold ibc_local_init in Hrun. inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ Hlocal Hl)
      as (-> & -> & ->) end.
  match goal with He : eval_expr _ _ _ _ (Etempvar _ _) ?value |- _ =>
    assert (value = Vptr b ofs) by (eapply ocn_temp_value; eauto); subst value end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Hstore : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Hstore; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  repeat split; try reflexivity; assumption.
Qed.

(** X writes to the destination obtained from the initialized local cell.
    No arbitrary pre-existing temporary is allowed to supply that address. *)
Lemma ibc_x_stage_store : forall ge e le m local db dofs t le' m' out,
  e ! IBV._dest = Some (local, tptr tfloat) ->
  Mem.load Mint32 m local 0 = Some (Vptr db dofs) ->
  ocn_exec ge e le m ibc_x_stage t le' m' out ->
  exists value,
    Mem.store Mfloat32 m db (Ptrofs.unsigned dofs) value = Some m' /\
    le' ! IBV._src = le ! IBV._src /\ t = E0 /\ out = Out_normal.
Proof.
  intros ge e le m local db dofs t le' m' out Hlocal Hload Hrun.
  unfold ibc_x_stage, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ (Evar IBV._dest _) ?v |- _ =>
    assert (v = Vptr db dofs) by (eapply ibc_pointer_local_read; eauto); subst v end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _
    (Sassign _ _) _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ ?temps _ (ibc_index IBV._t'5 0) _ _ _ |- _ =>
    assert (temps ! IBV._t'5 = Some (Vptr db dofs)) as Hdest
      by (rewrite PTree.gso by discriminate; apply PTree.gss);
    destruct (ibc_index_location _ _ _ _ _ _ _ _ _ _ _ Hdest Hl)
      as (-> & -> & ->) end.
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 0)))
    with Ptrofs.zero in *.
  rewrite Ptrofs.add_zero in *.
  match goal with Hstore : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Hstore; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  eexists. split; [eassumption|]. split.
  - repeat rewrite PTree.gso by discriminate. reflexivity.
  - auto.
Qed.

(** Fresh allocation and the real first two stores preserve an old source
    cell when source and destination are in distinct existing allocations. *)
Theorem ibc_entry_and_prefix_preserve_source_y :
  forall version ge m db dofs sb sofs e le entry pre y_le y_m,
  db <> sb -> Mem.valid_block m db -> Mem.valid_block m sb ->
  function_entry2 ge (ibk_copy_body version)
    [Vptr db dofs; Vptr sb sofs] m e le entry ->
  ocn_exec ge e le entry (ocn_prepend (ibk_copy_before_y version) Sskip)
    pre y_le y_m Out_normal ->
  le ! IBV._src = Some (Vptr sb sofs) /\
  y_le ! IBV._src = Some (Vptr sb sofs) /\
  Mem.load Mfloat32 y_m sb
    (Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr 4))) =
  Mem.load Mfloat32 m sb
    (Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr 4))) /\
  exists local, e ! IBV._dest = Some (local, tptr tfloat) /\
    Mem.load Mint32 y_m local 0 = Some (Vptr db dofs).
Proof.
  intros version ge m db dofs sb sofs e le entry pre y_le y_m
    Hdifferent Hdvalid Hsvalid Hentry Hprefix.
  destruct (ibc_actual_entry _ _ _ _ _ _ _ _ Hentry)
    as (local & Halloc & -> & Hdest & Hsrc).
  assert (local <> db) as Hld.
  { intro Heq; subst. eapply Mem.fresh_block_alloc; eauto. }
  assert (local <> sb) as Hls.
  { intro Heq; subst. eapply Mem.fresh_block_alloc; eauto. }
  rewrite ibc_prefix_is_generated in Hprefix.
  cbn [ocn_prepend] in Hprefix.
  destruct (ibk_split_sequence _ _ _ _ ibc_local_init _ _ _ _ _ eq_refl Hprefix)
    as (init_le & init_m & init_t & rest_t & Htrace & Hinit & Hrest).
  destruct (ibc_local_init_store _ _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) Hdest (ex_intro _ db (ex_intro _ dofs eq_refl)) Hinit)
    as (Hlocalstore & -> & -> & _).
  destruct (ibk_split_sequence _ _ _ _ ibc_x_stage _ _ _ _ _ eq_refl Hrest)
    as (x_le & x_m & x_t & skip_t & Hresttrace & Hx & Hskip).
  inversion Hskip; subst; clear Hskip.
  assert (Mem.load Mint32 init_m local 0 = Some (Vptr db dofs)) as Hlocalread.
  { exact (Mem.load_store_same _ _ _ _ _ _ Hlocalstore). }
  destruct (ibc_x_stage_store _ _ _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) Hlocalread Hx)
    as (xvalue & Hxstore & Hsrcsame & _).
  split; [exact Hsrc|]. split; [congruence|]. split.
  - erewrite Mem.load_store_other; [|exact Hxstore|left; congruence].
    erewrite Mem.load_store_other; [|exact Hlocalstore|left; congruence].
    eapply Mem.load_alloc_unchanged; eauto.
  - exists local. split; [apply PTree.gss|].
    erewrite Mem.load_store_other; [exact Hlocalread|exact Hxstore|left; congruence].
Qed.

Definition InkCopyEntryHeightCut : Prop :=
  forall version m db dofs sb sofs t m' result,
  db <> sb -> Mem.valid_block m db -> Mem.valid_block m sb ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ibk_copy_body version)) [Vptr db dofs; Vptr sb sofs]
    t m' result ->
  exists e y_le y_m after_le after_m value pre store suf,
    t = pre ++ (store ++ suf) /\
    Mem.load Mfloat32 m sb
      (Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr 4))) = Some value /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBV._t'3 (Vptr db dofs) y_le) y_m ibk_source_y value /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBV._t'4 value (PTree.set IBV._t'3 (Vptr db dofs) y_le)) y_m
      ibk_y_store store after_le after_m Out_normal.

(** The same actual call reads its Y from BEFORE function entry, not merely
    from the memory after X. The later Z assignment cannot supply this read. *)
Theorem ibc_actual_copy_reads_entry_height : InkCopyEntryHeightCut.
Proof.
  unfold InkCopyEntryHeightCut.
  intros version m db dofs sb sofs t m' result Hdifferent Hdvalid Hsvalid Hcall.
  inversion Hcall; subst.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibk_copy_body_has_ordered_y_predecessor _ _ _ _ _ _ _ _ _ Hbody)
      as (y_le & y_m & after_le & after_m & destination & value & pre & store & suf &
        Htrace & Hprefix & Hdest & Hread & Hstore & Hsuffix) end.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_entry_and_prefix_preserve_source_y _ _ _ _ _ _ _ _ _ _ _ _ _
      Hdifferent Hdvalid Hsvalid Hentry Hprefix)
      as (_ & Hsrc & Hpreserve & local & Hlocal & Hlocalread) end.
  assert (destination = Vptr db dofs) by (eapply ibc_pointer_local_read; eauto).
  subst destination.
  assert ((PTree.set IBV._t'3 (Vptr db dofs) y_le) ! IBV._src = Some (Vptr sb sofs))
    as Hsrcnow by (rewrite PTree.gso by discriminate; exact Hsrc).
  pose proof (ibc_float_read _ _ _ _ _ _ _ _ _ Hsrcnow Hread) as Hload.
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1)))
    with (Ptrofs.repr 4) in Hload.
  rewrite Hpreserve in Hload.
  do 9 eexists. repeat split; eassumption.
Qed.
