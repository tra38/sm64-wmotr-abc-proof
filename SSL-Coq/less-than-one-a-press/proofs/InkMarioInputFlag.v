(** Mario's complete button-input body cannot manufacture A-pressed from
    held A, B/Z input, or its two button-age counters. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib Ctypes
  Events Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkControllerSource
  InkControllerEdge InkBackwardSource InkCopyCaller InkBackwardExecution
  InkLongJumpGuard InkMovingBackwardSource ContactConsumerExecution ObjectContactNecessity
  EyerokRank15LiveMovement Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition imf_input_load m mb mo :=
  Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 2))).
Definition imf_room mo := Ptrofs.unsigned mo + 200 <= Ptrofs.max_unsigned.

Lemma imf_address : forall mo delta,
  imf_room mo -> 0 <= delta <= 200 ->
  Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr delta)) = Ptrofs.unsigned mo + delta.
Proof.
  intros mo delta Hroom Hdelta. unfold imf_room in Hroom.
  pose proof (Ptrofs.unsigned_range mo).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr delta)
    by (change (0 <= delta <= 4294967295); lia).
  apply Ptrofs.unsigned_repr. lia.
Qed.

Lemma imf_single_bit_mask_clear : forall flags n,
  0 <= n < 32 -> Int.testbit flags n = false ->
  Int.and flags (Int.repr (2 ^ n)) = Int.zero.
Proof.
  intros flags n Hn Hclear. apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_and by exact Hi. rewrite Int.bits_zero.
  rewrite Int.testbit_repr by exact Hi. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb n i) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst i. rewrite Hclear. reflexivity.
  - apply andb_false_r.
Qed.

Lemma imf_and_constant_value : forall ge e le m id mask word answer,
  le ! id = Some (Vint word) ->
  eval_expr ge e le m (Ebinop Oand (Etempvar id tushort)
    (Econst_int mask tint) tint) answer -> answer = Vint (Int.and word mask).
Proof.
  intros ge e le m id mask word answer Htemp Hr. inversion Hr; subst.
  - match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vint word) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in H; subst end.
    match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn in H; inversion H; reflexivity end.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Theorem imf_a_guard_skips_without_controller_edge :
  forall version e le m mb mo cb co pressed t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 156))) = Some (Vptr cb co) ->
  Mem.load Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))) = Some (Vint pressed) ->
  Int.testbit pressed 15 = false ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ics_mario_a version) t le' m' out ->
  t = E0 /\ m' = m /\ out = Out_normal /\ le' ! IBM._m = le ! IBM._m.
Proof.
  intros version e le m mb mo cb co pressed t le' m' out Hm Hcontroller Hpressed Hclear Hrun.
  destruct (ice_selected_fields version) as (_ & _ & HpressedField & _ & HcontrollerField & _).
  destruct (ics_source_cuts version) as (_ & _ & _ & Hshape & _). rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IBM._t'20 ics_mario_controller) _ _ _ _ _ eq_refl Hrun)
    as (cl & cm & ct & rt & Htrace & Hread & Hrest).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ ics_mario_controller ?v |- _ =>
    assert (v = Vptr cb co) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tptr (Tstruct IBM._Controller noattr));
      [exact Hm|exact HcontrollerField|reflexivity|exact Hcontroller|exact Hr]); subst v end.
  destruct (ibk_split_sequence _ _ _ _
    (Sset IBM._t'21 (ics_field IBM._t'20 IBM._Controller IBM._buttonPressed tushort))
    _ _ _ _ _ eq_refl Hrest) as (al & am & read_trace & bt & Htrace2 & Hread2 & Hbranch).
  inversion Hread2; subst.
  match goal with Hr : eval_expr _ _ _ _ (ics_field _ _ _ _) ?v |- _ =>
    assert (v = Vint pressed) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tushort);
      [apply PTree.gss|exact HpressedField|reflexivity|exact Hpressed|exact Hr]); subst v end.
  inversion Hbranch; subst.
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Ebinop Oand _ _ _) ?v |- _ =>
    assert (v = Vint (Int.and pressed (Int.repr 32768))) as Hvalue by
      (eapply (imf_and_constant_value ge env temps memory IBM._t'21 (Int.repr 32768) pressed);
        [apply PTree.gss|exact Hr]); subst v end.
  assert (Int.and pressed (Int.repr 32768) = Int.zero) as Hmask
    by (apply (imf_single_bit_mask_clear pressed 15); [lia|exact Hclear]).
  match goal with Hb : bool_val (Vint (Int.and _ _)) _ _ = Some ?choice |- _ =>
    rewrite Hmask in Hb; change (Some false = Some choice) in Hb; inversion Hb; subst end.
  match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion Hskip; subst end.
  repeat split; try reflexivity. repeat rewrite PTree.gso by discriminate. reflexivity.
Qed.

Definition imf_or_stage id mask := Ssequence (Sset id ics_input)
  (Sassign ics_input (Ebinop Oor (Etempvar id tushort) (Econst_int mask tint) tint)).

Lemma imf_or_stage_preserves_a : forall version e le m mb mo id mask before t le' m' out,
  id <> IBM._m -> Int.testbit mask 1 = false ->
  le ! IBM._m = Some (Vptr mb mo) -> imf_input_load m mb mo = Some (Vint before) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (imf_or_stage id mask) t le' m' out ->
  exists after, imf_input_load m' mb mo = Some (Vint after) /\
    Int.testbit after 1 = Int.testbit before 1 /\ t = E0 /\ out = Out_normal /\
    le' ! IBM._m = le ! IBM._m.
Proof.
  intros version e le m mb mo id mask before t le' m' out Hdifferent Hmask Hm Hload Hrun.
  destruct (ice_selected_fields version) as (_ & _ & _ & _ & _ & Hfield).
  unfold imf_or_stage in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset id ics_input) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hstore).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ ics_input ?v |- _ =>
    assert (v = Vint before) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tushort);
      [exact Hm|exact Hfield|reflexivity|exact Hload|exact Hr]); subst v end.
  inversion Hstore; subst.
  match goal with Hl : eval_lvalue _ ?env ?temps ?memory ics_input _ _ _ |- _ =>
    assert (temps ! IBM._m = Some (Vptr mb mo)) as Hnow
      by (rewrite PTree.gso by congruence; exact Hm);
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) env temps memory
      IBM._m IBM._MarioState IBM._input tushort mb mo 2 _ _ _ Hnow Hfield Hl)
      as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Ebinop Oor _ _ _) _ |- _ => inversion Hr; subst end.
  all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end].
  match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vint before) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in Hr; subst end.
  match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ => cbn in Hsem; inversion Hsem; subst end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  exists (Int.zero_ext 16 (Int.or before mask)). split.
  - unfold imf_input_load. erewrite Mem.load_store_same by eassumption.
    change (Some (Vint (Int.zero_ext 16 (Int.zero_ext 16 (Int.or before mask)))) =
      Some (Vint (Int.zero_ext 16 (Int.or before mask)))).
    rewrite Int.zero_ext_idem by lia. reflexivity.
  - split.
    + rewrite Int.bits_zero_ext by lia. cbn [zlt].
      rewrite Int.bits_or by (change (0 <= 1 < 32); lia). rewrite Hmask. apply orb_false_r.
    + repeat split; try reflexivity. apply PTree.gso. congruence.
Qed.

Definition imf_counter_offset field :=
  if Pos.eqb field IBM._framesSinceA then 40 else 41.
Lemma imf_counter_field : forall version field,
  field = IBM._framesSinceA \/ field = IBM._framesSinceB ->
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IBM._MarioState field (imf_counter_offset field) = true /\
  40 <= imf_counter_offset field <= 41.
Proof.
  intros version field Hfield.
  change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState field (imf_counter_offset field) = true /\
    40 <= imf_counter_offset field <= 41).
  rewrite <- rank15_selected_header_environment_exact.
  destruct Hfield as [Hfield | Hfield]; subst field; destruct version; vm_compute; intuition discriminate.
Qed.

Lemma imf_counter_store_preserves_input :
  forall version e le m mb mo field rhs t le' m' out,
  field = IBM._framesSinceA \/ field = IBM._framesSinceB -> imf_room mo ->
  le ! IBM._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign (ics_field IBM._m IBM._MarioState field tuchar) rhs) t le' m' out ->
  imf_input_load m' mb mo = imf_input_load m mb mo /\ t = E0 /\
    out = Out_normal /\ le' = le.
Proof.
  intros version e le m mb mo field rhs t le' m' out Hfield Hroom Hm Hrun.
  destruct (imf_counter_field version field Hfield) as [Hlayout Hrange].
  inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue _ ?env ?temps ?memory _ _ _ _ |- _ =>
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) env temps memory
      IBM._m IBM._MarioState field tuchar mb mo (imf_counter_offset field) _ _ _ Hm Hlayout Hl)
      as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  split.
  - unfold imf_input_load. eapply Mem.load_store_other; [eassumption|].
    right; left. cbn [size_chunk]. rewrite !imf_address by (auto; lia). lia.
  - repeat split; reflexivity.
Qed.

(** A classification of this real, call-free tail, not a substitute game
    transition system. In particular, arbitrary assignments are not admitted. *)
Inductive imf_safe : statement -> Prop :=
| imf_skip : imf_safe Sskip
| imf_set : forall id expr, id <> IBM._m -> imf_safe (Sset id expr)
| imf_counter : forall field rhs,
    field = IBM._framesSinceA \/ field = IBM._framesSinceB ->
    imf_safe (Sassign (ics_field IBM._m IBM._MarioState field tuchar) rhs)
| imf_or : forall id mask, id <> IBM._m -> Int.testbit mask 1 = false ->
    imf_safe (imf_or_stage id mask)
| imf_seq : forall first rest, imf_safe first -> imf_safe rest ->
    imf_safe (Ssequence first rest)
| imf_if : forall cond yes no, imf_safe yes -> imf_safe no ->
    imf_safe (Sifthenelse cond yes no).

Lemma imf_safe_normal : forall s, imf_safe s -> ibk_normal s = true.
Proof. intros s H; induction H; cbn [ibk_normal imf_or_stage]; auto; rewrite IHimf_safe1, IHimf_safe2; reflexivity. Qed.

Lemma imf_safe_execution : forall s, imf_safe s ->
  forall version e le m mb mo before t le' m' out,
  imf_room mo -> le ! IBM._m = Some (Vptr mb mo) -> imf_input_load m mb mo = Some (Vint before) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m s t le' m' out ->
  exists after, imf_input_load m' mb mo = Some (Vint after) /\
    Int.testbit after 1 = Int.testbit before 1 /\ t = E0 /\ out = Out_normal /\
    le' ! IBM._m = le ! IBM._m.
Proof.
  intros s Hsafe. induction Hsafe;
    intros version e le m mb mo before t le' m' out Hroom Hm Hload Hrun.
  - inversion Hrun; subst. exists before. repeat split; auto.
  - inversion Hrun; subst. exists before. repeat split; auto. apply PTree.gso. congruence.
  - destruct (imf_counter_store_preserves_input _ _ _ _ _ _ _ _ _ _ _ _ H Hroom Hm Hrun)
      as (Hsame & -> & -> & ->).
    exists before. rewrite Hsame. repeat split; auto.
  - eapply imf_or_stage_preserves_a; eauto.
  - destruct (ibk_split_sequence _ _ _ _ first rest _ _ _ _ (imf_safe_normal _ Hsafe1) Hrun)
      as (middle & memory & pre & suf & Htrace & Hfirst & Hrest).
    destruct (IHHsafe1 _ _ _ _ _ _ _ _ _ _ _ Hroom Hm Hload Hfirst)
      as (mid & Hmid & Hbit1 & Hpre & _ & Htemp1).
    destruct (IHHsafe2 _ _ _ _ _ _ _ _ _ _ _ Hroom (eq_trans Htemp1 Hm) Hmid Hrest)
      as (after & Hafter & Hbit2 & Hsuf & Hout & Htemp2).
    exists after. split; [exact Hafter|].
    split; [rewrite Hbit2; exact Hbit1|].
    split; [rewrite Htrace, Hpre, Hsuf; reflexivity|].
    split; [exact Hout|]. rewrite Htemp2, Htemp1. reflexivity.
  - inversion Hrun; subst. destruct b; [eapply IHHsafe1|eapply IHHsafe2]; eauto.
Qed.

Lemma imf_actual_tail_is_safe : forall version, imf_safe (ics_mario_tail version).
Proof.
  intros []. all: unfold ics_mario_tail, ics_body; cbn [fn_body rank12b_drop_sequences].
  all: repeat first
    [apply imf_skip
    |apply imf_or; [discriminate|reflexivity]
    |apply imf_counter; (left; reflexivity) || (right; reflexivity)
    |apply imf_set; discriminate
    |apply imf_seq
    |apply imf_if].
Qed.

Definition InkMarioButtonNoEdgeCut : Prop :=
  forall version e le m mb mo cb co pressed before t le' m' out,
  imf_room mo -> le ! IBM._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 156))) = Some (Vptr cb co) ->
  Mem.load Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))) = Some (Vint pressed) ->
  Int.testbit pressed 15 = false -> imf_input_load m mb mo = Some (Vint before) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ics_body version ICButtons)) t le' m' out ->
  exists after, imf_input_load m' mb mo = Some (Vint after) /\
    Int.testbit after 1 = Int.testbit before 1 /\ t = E0 /\ out = Out_normal.

Theorem imf_complete_button_body_no_new_a : InkMarioButtonNoEdgeCut.
Proof.
  unfold InkMarioButtonNoEdgeCut.
  intros version e le m mb mo cb co pressed before t le' m' out Hroom Hm Hcontroller Hpressed Hclear Hload Hrun.
  destruct (ics_source_cuts version) as (_ & _ & Hbody & _). rewrite Hbody in Hrun.
  assert (ibk_normal (ics_mario_a version) = true) as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suf & Htrace & Hguard & Htail).
  destruct (imf_a_guard_skips_without_controller_edge _ _ _ _ _ _ _ _ _ _ _ _ _
    Hm Hcontroller Hpressed Hclear Hguard) as (Hpre & Hmemory & _ & Htemp).
  subst memory.
  destruct (imf_safe_execution _ (imf_actual_tail_is_safe version) version e middle m mb mo before
    suf le' m' out Hroom (eq_trans Htemp Hm) Hload Htail)
    as (after & Hafter & Hbit & Hsuf & Hout & _).
  exists after. repeat split; try assumption. subst. reflexivity.
Qed.
