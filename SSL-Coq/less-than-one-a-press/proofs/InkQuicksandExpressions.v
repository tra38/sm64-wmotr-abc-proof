(** Actual field reads and both real sink destinations, not supplied temps. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkQuicksandSource
  InkCopyCaller InkBackwardSource InkFloorResetExecution ObjectContactNecessity
  EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma iq_selected_fields : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IQ._MarioState IQ._quicksandDepth 192 = true /\
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IQ._GraphNodeObject IQ._throwMatrix 80 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IQ._MarioState IQ._quicksandDepth 192 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IQ._GraphNodeObject IQ._throwMatrix 80 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; split; reflexivity.
Qed.

Lemma iq_graphics_value : forall version e le m ob oo answer,
  le ! IQ._o = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m iq_graphics answer ->
  answer = Vptr ob oo.
Proof.
  intros version e le m ob oo answer Hobject Hread.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & _).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iq_object v -> v = Vptr ob oo) as Hobj
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iq_header v -> v = Vptr ob oo) as Hhead.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _ iq_object IQ._Object
      IQ._header (Tstruct IQ._ObjectNode noattr) ob oo 0 v eq_refl Hobj Hheader
      (or_intror eq_refl) Hr) as H. rewrite Ptrofs.add_zero in H. exact H. }
  pose proof (ibcc_aggregate_field _ _ _ _ iq_header IQ._ObjectNode
    IQ._gfx (Tstruct IQ._GraphNodeObject noattr) ob oo 0 answer eq_refl Hhead Hgfx
    (or_intror eq_refl) Hread) as H. rewrite Ptrofs.add_zero in H. exact H.
Qed.

Lemma iq_graphics_position_value : forall version e le m ob oo answer,
  le ! IQ._o = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m iq_graphics_pos answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)).
Proof.
  intros. destruct (ibcc_selected_fields version) as (_ & _ & _ & _ & Hpos).
  eapply ibcc_aggregate_field with (base := iq_graphics) (tag := IQ._GraphNodeObject)
    (field := IQ._pos) (ty := tarray tfloat 3) (delta := 32);
    [reflexivity| |exact Hpos|left; reflexivity|eassumption].
  intros. eapply iq_graphics_value; eauto.
Qed.

Lemma iq_graphics_y_location : forall version e le m ob oo b ofs bf,
  le ! IQ._o = Some (Vptr ob oo) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m iq_y b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr 36) /\ bf = Full.
Proof.
  intros version e le m ob oo b ofs bf Ho Hl.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iq_graphics_pos v -> v = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)))
    as Hbase by (intros; eapply iq_graphics_position_value; eauto).
  destruct (ifr_array_index_location _ _ _ _ iq_graphics_pos _ _ _ _ _ _
    eq_refl Hbase Hl) as (-> & -> & ->).
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1))) with (Ptrofs.repr 4).
  rewrite Ptrofs.add_assoc. repeat split; reflexivity.
Qed.

Lemma iq_graphics_y_read : forall version e le m ob oo value answer,
  le ! IQ._o = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36))) = Some value ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m iq_y answer ->
  answer = value.
Proof.
  intros version e le m ob oo value answer Ho Hload Hread. inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ iq_y _ _ _ |- _ =>
    destruct (iq_graphics_y_location _ _ _ _ _ _ _ _ _ Ho Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36))) = Some answer)
      in Hr; congruence end.
Qed.

Lemma iq_depth_read : forall version e le m mb mo value answer,
  le ! IQ._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some value ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m iq_depth answer ->
  answer = value.
Proof.
  intros version e le m mb mo value answer Hm Hload Hread.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_state v -> v = Vptr mb mo) as Hbase by (intros; eapply ibcc_deref_struct; eauto).
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ iq_depth _ _ _ |- _ =>
    destruct (ibcc_field_location _ _ _ _ ibcc_state IQ._MarioState IQ._quicksandDepth
      tfloat _ _ _ _ _ _ eq_refl Hbase (proj1 (iq_selected_fields version)) Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some answer)
      in Hr; congruence end.
Qed.

Lemma iq_matrix_read : forall version e le m ob oo value answer,
  le ! IQ._o = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 80))) = Some value ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m iq_matrix answer ->
  answer = value.
Proof.
  intros version e le m ob oo value answer Ho Hload Hread.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iq_graphics v -> v = Vptr ob oo) as Hbase by (intros; eapply iq_graphics_value; eauto).
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ iq_matrix _ _ _ |- _ =>
    destruct (ibcc_field_location _ _ _ _ iq_graphics IQ._GraphNodeObject IQ._throwMatrix
      iq_matrix_type _ _ _ _ _ _ eq_refl Hbase (proj2 (iq_selected_fields version)) Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 80))) = Some answer)
      in Hr; congruence end.
Qed.

Lemma iq_array_location : forall ge e le m base element length index b oo loc ofs bf,
  typeof base = tarray element length ->
  (forall v, eval_expr ge e le m base v -> v = Vptr b oo) ->
  eval_lvalue ge e le m (Ederef (Ebinop Oadd base
    (Econst_int (Int.repr index) tint) (tptr element)) element) loc ofs bf ->
  loc = b /\ ofs = Ptrofs.add oo
    (Ptrofs.mul (Ptrofs.repr (sizeof ge element)) (ptrofs_of_int Signed (Int.repr index))) /\ bf = Full.
Proof.
  intros ge e le m base element length index b oo loc ofs bf Htype Hbase Hl.
  inversion Hl; subst.
  match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion Hr; subst; clear Hr end.
  - match goal with Hr : eval_expr _ _ _ _ base _ |- _ => apply Hbase in Hr; subst end.
    match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in Hr; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn [typeof] in Hsem; rewrite Htype in Hsem; cbn in Hsem; inversion Hsem; subst end.
    repeat split; reflexivity.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Lemma iq_array_value : forall ge e le m base element length index b oo answer,
  typeof base = tarray element length -> access_mode element = By_reference ->
  (forall v, eval_expr ge e le m base v -> v = Vptr b oo) ->
  eval_expr ge e le m (Ederef (Ebinop Oadd base
    (Econst_int (Int.repr index) tint) (tptr element)) element) answer ->
  answer = Vptr b (Ptrofs.add oo
    (Ptrofs.mul (Ptrofs.repr (sizeof ge element)) (ptrofs_of_int Signed (Int.repr index)))).
Proof.
  intros ge e le m base element length index b oo answer Htype Hmode Hbase Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (iq_array_location _ _ _ _ _ _ _ _ _ _ _ _ _ Htype Hbase Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end;
    try reflexivity.
  all: match goal with Haccess : access_mode (typeof _) = _ |- _ =>
    cbn [typeof] in Haccess; congruence end.
Qed.

Lemma iq_matrix_y_location : forall ge e le m receiver qb qo b ofs bf,
  le ! receiver = Some (Vptr qb qo) ->
  eval_lvalue ge e le m (iq_matrix_y receiver) b ofs bf ->
  b = qb /\ ofs = Ptrofs.add qo (Ptrofs.repr 52) /\ bf = Full.
Proof.
  intros ge e le m receiver qb qo b ofs bf Htemp Hl.
  set (base := Ederef (Etempvar receiver iq_matrix_type) (tarray (tarray tfloat 4) 4)).
  assert (forall v, eval_expr ge e le m base v -> v = Vptr qb qo) as Hbase.
  { intros v Hr. unfold base in Hr. inversion Hr; subst.
    match goal with Hloc : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hloc; subst end.
    lazymatch goal with He : eval_expr _ _ _ _ (Etempvar receiver _) ?value |- _ =>
      assert (value = Vptr qb qo) as Hvalue by (eapply ocn_temp_value; [exact He|exact Htemp]);
      inversion Hvalue; subst end.
    match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
    reflexivity. }
  set (row := Ederef (Ebinop Oadd base (Econst_int (Int.repr 3) tint)
    (tptr (tarray tfloat 4))) (tarray tfloat 4)).
  assert (forall v, eval_expr ge e le m row v ->
    v = Vptr qb (Ptrofs.add qo (Ptrofs.repr 48))) as Hrow.
  { intros v Hr. exact (iq_array_value ge e le m base (tarray tfloat 4) 4 3 qb qo v
      eq_refl eq_refl Hbase Hr). }
  destruct (iq_array_location ge e le m row tfloat 4 1 qb
    (Ptrofs.add qo (Ptrofs.repr 48)) _ _ _ eq_refl Hrow Hl) as (-> & -> & ->).
  change (Ptrofs.mul (Ptrofs.repr (sizeof ge tfloat)) (ptrofs_of_int Signed (Int.repr 1)))
    with (Ptrofs.repr 4).
  rewrite Ptrofs.add_assoc. repeat split; reflexivity.
Qed.
