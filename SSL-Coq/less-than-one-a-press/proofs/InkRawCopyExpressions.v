(** Actual reads and addresses used by the selected collision-position copy. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkRawCopySource
  InkCopyCaller InkFloorResetExecution ObjectContactNecessity
  Area1Rank18CopyRead Area1Rank18StateArrayBound EyerokRank15LiveMovement
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma irc_global_pointer_read : forall (ge : Clight.genv) e le m id b value answer,
  e ! id = None -> Genv.find_symbol ge id = Some b ->
  Mem.load Mint32 m b 0 = Some value ->
  eval_expr ge e le m (Evar id (tptr (Tstruct IRC._Object noattr))) answer ->
  answer = value.
Proof.
  intros ge e le m id b value answer Hlocal Hsymbol Hload Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl; subst end;
    try congruence.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some ?v |- _ =>
    match type of Hr with Mem.loadv _ _ (Vptr ?loc _) = _ =>
      assert (loc = b) by congruence; subst loc end;
    change (Mem.load Mint32 m b 0 = Some v) in Hr; congruence end.
Qed.

Lemma irc_constant_read : forall ge e le m index number answer,
  irc_constant index = Some number ->
  eval_expr ge e le m index answer -> answer = Vint number.
Proof.
  intros ge e le m index number answer Hconstant Hread.
  unfold irc_constant in Hconstant.
  repeat match type of Hconstant with
  | context [match ?x with _ => _ end] => destruct x; cbn in Hconstant; try discriminate
  end.
  all: inversion Hconstant; subst.
  all: try solve [eapply ocn_const_int_value; eauto].
  all:
    inversion Hread; subst.
  all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end].
  all: repeat match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
        inversion H; subst; clear H end.
  all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion Hbad end].
  all: match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
        cbn in Hsem; inversion Hsem; reflexivity end.
Qed.

Definition irc_raw_object receiver := Ederef
  (Etempvar receiver (tptr (Tstruct IRC._Object noattr))) (Tstruct IRC._Object noattr).
Definition irc_raw_union version receiver := Efield (irc_raw_object receiver)
  IRC._rawData (Tunion (rank15_raw_union_tag version) noattr).
Definition irc_raw_array version receiver := Efield (irc_raw_union version receiver)
  IRC._asF32 (tarray tfloat 80).

Lemma irc_raw_array_value : forall version e le m receiver ob oo answer,
  le ! receiver = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (irc_raw_array version receiver) answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136)).
Proof.
  intros version e le m receiver ob oo answer Htemp Hread.
  destruct (rank15_selected_raw_layout version)
    as (object_type & raw_type & Hobject & Hraw & HobjectOffset & HrawOffset).
  assert (ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IRC._Object IRC._rawData 136 = true) as Hfield.
  { unfold ibcc_field_ok.
    change ((genv_cenv (Clight.globalenv (selected_clight_target version))) ! IRC._Object =
      Some object_type) in Hobject.
    change (field_offset (Clight.globalenv (selected_clight_target version))
      IRC._rawData (co_members object_type) = OK (136, Full)) in HobjectOffset.
    rewrite Hobject, HobjectOffset. reflexivity. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m (irc_raw_union version receiver) v ->
    v = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136))) as Hbase.
  { intros. eapply ibcc_aggregate_field with (base := irc_raw_object receiver)
      (tag := IRC._Object) (field := IRC._rawData)
      (ty := Tunion (rank15_raw_union_tag version) noattr) (delta := 136);
      [reflexivity| |exact Hfield|right; reflexivity|eassumption].
    intros. eapply ibcc_deref_struct; eauto. }
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl; subst; try discriminate end.
  match goal with Hr : eval_expr _ _ _ _ (irc_raw_union _ _) _ |- _ => apply Hbase in Hr; inversion Hr; subst end.
  match goal with Htype : typeof (irc_raw_union _ _) = _ |- _ =>
    cbn [typeof irc_raw_union] in Htype; inversion Htype; subst end.
  match goal with Hco : (genv_cenv _) ! _ = Some ?co |- _ =>
    assert (co = raw_type) by congruence; subst co end.
  change (union_field_offset (Clight.globalenv (selected_clight_target version))
    IRC._asF32 (co_members raw_type) = OK (0, Full)) in HrawOffset.
  match goal with Hoff : union_field_offset _ _ _ = OK (?offset, ?bf) |- _ =>
    assert (offset = 0 /\ bf = Full) as Hfields by (split; congruence);
    destruct Hfields as [Hdelta Hbits]; subst offset bf end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  all: try solve [match goal with Hmode : access_mode _ = _ |- _ =>
    cbn [typeof irc_raw_array access_mode] in Hmode; discriminate end].
  all: rewrite Ptrofs.add_zero; reflexivity.
Qed.

Lemma irc_raw_location : forall version e le m receiver index number ob oo b ofs bf,
  le ! receiver = Some (Vptr ob oo) ->
  typeof index = tint -> irc_constant index = Some (Int.repr number) ->
  In number [6; 7; 9; 10; 11] ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (rank15_raw_float_expression version receiver index) b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr (136 + 4 * number)) /\ bf = Full.
Proof.
  intros version e le m receiver index number ob oo b ofs bf Htemp Htype Hindex Hnumber Hl.
  inversion Hl; subst.
  match goal with Hb : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion Hb; subst; clear Hb end.
  - match goal with Ha : eval_expr _ _ _ _ (Efield _ _ _) ?value |- _ =>
      assert (value = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136)))
        by (eapply irc_raw_array_value; eauto); subst value end.
    match goal with Hi : eval_expr _ _ _ _ index ?value |- _ =>
      assert (value = Vint (Int.repr number)) by (eapply irc_constant_read; eauto); subst value end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn [typeof] in Hsem; rewrite Htype in Hsem; cbn in Hsem; inversion Hsem; subst end.
    rewrite Ptrofs.add_assoc.
    destruct Hnumber as [<-|[<-|[<-|[<-|[<-|[]]]]]]; repeat split; reflexivity.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Lemma irc_state_zero_value : forall version e le m mb answer,
  e ! IRC._gMarioStates = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IRC._gMarioStates = Some mb ->
  le ! IRC._i = Some (Vint Int.zero) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m irc_state_zero answer ->
  answer = Vptr mb Ptrofs.zero.
Proof.
  intros version e le m mb answer Hlocal Hsymbol Hindex Hread.
  unfold irc_state_zero in Hread.
  repeat match goal with
  | H : eval_expr _ _ _ _ _ _ |- _ => inversion H; subst; clear H
  | H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
  end; try congruence.
  repeat match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; clear Hd; try discriminate end.
  match goal with Htemp : le ! IRC._i = Some ?value |- _ =>
    assert (value = Vint Int.zero) by congruence; subst value end.
  match goal with Hsym : Genv.find_symbol _ IRC._gMarioStates = Some ?b |- _ =>
    assert (b = mb) by congruence; subst b end.
  lazymatch goal with Hsem : sem_binary_operation _ Oadd _ _ _ _ _ = Some ?value |- _ =>
    cbn [typeof] in Hsem;
    change (Some (Vptr mb (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr (sizeof (Clight.globalenv (selected_clight_target version))
        (Tstruct IRC._MarioState noattr))) Ptrofs.zero))) = Some value) in Hsem;
    rewrite Ptrofs.mul_zero, Ptrofs.add_zero in Hsem; inversion Hsem; reflexivity end.
Qed.

Lemma irc_source_y_read : forall version e le m mb height answer,
  e ! IRC._gMarioStates = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IRC._gMarioStates = Some mb ->
  le ! IRC._i = Some (Vint Int.zero) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m irc_source_y answer ->
  answer = Vsingle height.
Proof.
  intros version e le m mb height answer Hlocal Hsymbol Hindex Hload Hread.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m irc_state_position v -> v = Vptr mb (Ptrofs.repr 60)) as Hbase.
  { intros. eapply ibcc_aggregate_field with (base := irc_state_zero)
      (tag := IRC._MarioState) (field := IRC._pos) (ty := tarray tfloat 3)
      (b := mb) (ofs := Ptrofs.zero) (delta := 60);
      [reflexivity| |exact (proj1 (ibcc_selected_fields version))|left; reflexivity|eassumption].
    intros. eapply irc_state_zero_value; eauto. }
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ifr_array_index_location _ _ _ _ irc_state_position _ _ _ _ _ _
      eq_refl Hbase Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m mb 64 = Some answer) in Hr; congruence end.
Qed.
