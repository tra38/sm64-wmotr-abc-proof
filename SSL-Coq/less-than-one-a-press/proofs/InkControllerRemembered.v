(** The consecutive edge and remembered-button stores in the real controller
    loop. The analog helper is retained, not framed; entering this branch and
    following the rest of the controller loop remain separate obligations. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkControllerSource
  InkControllerEdge InkBackwardSource InkBackwardExecution InkFloorResetExecution
  ContactConsumerExecution ObjectContactNecessity Area2Rank12BContact
  InputSemantics SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition icr_room co := Ptrofs.unsigned co + 28 <= Ptrofs.max_unsigned.

Lemma icr_address : forall co delta,
  icr_room co -> 0 <= delta <= 28 ->
  Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr delta)) = Ptrofs.unsigned co + delta.
Proof.
  intros co delta Hroom Hdelta. unfold icr_room in Hroom.
  pose proof (Ptrofs.unsigned_range co).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr delta)
    by (change (0 <= delta <= 4294967295); lia).
  apply Ptrofs.unsigned_repr. lia.
Qed.

Definition icr_from_edge version := rank12b_drop_sequences 2 (ics_present version).
Definition icr_after_remember version := rank12b_drop_sequences 4 (ics_present version).

Lemma icr_source : forall version,
  icr_from_edge version = Ssequence (ics_edge_stage version)
    (Ssequence (ics_down_stage version) (icr_after_remember version)) /\
  ibk_normal (ics_edge_stage version) = true /\
  ibk_normal (ics_down_stage version) = true /\
  ifr_keeps_temp ICG._controller (ics_edge_stage version) = true /\
  ifr_keeps_temp ICG._controller (ics_down_stage version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem icr_actual_remember_store :
  forall version e le m cb co pb po current t le' m' out,
  le ! ICG._controller = Some (Vptr cb co) ->
  Mem.load Mint32 m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 24))) = Some (Vptr pb po) ->
  Mem.load Mint16unsigned m pb (Ptrofs.unsigned po) = Some (Vint current) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ics_down_stage version) t le' m' out ->
  Mem.store Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 16)))
    (Vint (Int.zero_ext 16 current)) = Some m' /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m cb co pb po current t le' m' out Hcontroller Hdata Hsample Hrun.
  destruct (ice_selected_fields version) as (HdataField & HdownField & HpressedField & HpadField & _).
  rewrite (proj1 (proj2 (ics_source_cuts version))) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  all: match goal with Hr : eval_expr _ _ ?temps _ ics_data ?v |- _ =>
    assert (temps ! ICG._controller = Some (Vptr cb co)) as Hnow
      by (repeat rewrite PTree.gso by discriminate; exact Hcontroller);
    assert (v = Vptr pb po) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tptr (Tstruct ICG.__319 noattr));
      [exact Hnow|exact HdataField|reflexivity|exact Hdata|exact Hr]); subst v; clear Hr Hnow end.
  all: match goal with Hr : eval_expr _ _ ?temps _ (ics_pad_field ?id) ?v |- _ =>
    assert (temps ! id = Some (Vptr pb po)) as Hnow
      by (repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (v = Vint current) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tushort);
      [exact Hnow|exact HpadField|reflexivity|rewrite Ptrofs.add_zero; exact Hsample|exact Hr]); subst v; clear Hr Hnow end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  lazymatch goal with Hl : eval_lvalue _ ?env ?temps ?memory ics_down _ _ _ |- _ =>
    assert (temps ! ICG._controller = Some (Vptr cb co)) as Hnow
      by (repeat rewrite PTree.gso by discriminate; exact Hcontroller);
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) env temps memory
      ICG._controller ICG._Controller ICG._buttonDown tushort cb co 16 _ _ _ Hnow HdownField Hl)
      as (-> & -> & ->) end.
  lazymatch goal with Hr : eval_expr _ _ ?temps _ (Etempvar ICG._t'24 _) ?v |- _ =>
    assert (temps ! ICG._t'24 = Some (Vint current)) as HsampleTemp by (apply PTree.gss);
    assert (v = Vint current) by (eapply ocn_temp_value; [exact Hr|exact HsampleTemp]); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  split; [assumption|]. split; reflexivity.
Qed.

Lemma icr_pressed_store_preserves_data : forall m m' cb co value,
  icr_room co ->
  Mem.store Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))) value = Some m' ->
  Mem.load Mint32 m' cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 24))) =
    Mem.load Mint32 m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 24))).
Proof.
  intros m m' cb co value Hroom Hstore.
  eapply Mem.load_store_other; [exact Hstore|].
  right. right. rewrite !icr_address by (assumption || lia). cbn. lia.
Qed.

Lemma icr_remember_store_preserves_pressed : forall m m' cb co value,
  icr_room co ->
  Mem.store Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 16))) value = Some m' ->
  Mem.load Mint16unsigned m' cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))) =
    Mem.load Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))).
Proof.
  intros m m' cb co value Hroom Hstore.
  eapply Mem.load_store_other; [exact Hstore|].
  right. right. rewrite !icr_address by (assumption || lia). cbn. lia.
Qed.

(** This starts at the actual two-store suffix of the present-controller
    branch. The earlier loop/controller selection is still a predecessor
    obligation; separate global arrays are derived from their real symbols. *)
Definition InkControllerRememberedCut : Prop :=
  forall version e le m cb co pb po current previous t le' m' out,
  let ge := Clight.globalenv (selected_clight_target version) in
  Genv.find_symbol ge ICG._gControllers = Some cb ->
  Genv.find_symbol ge ICG._gControllerPads = Some pb ->
  icr_room co -> le ! ICG._controller = Some (Vptr cb co) ->
  Mem.load Mint32 m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 24))) = Some (Vptr pb po) ->
  Mem.load Mint16unsigned m pb (Ptrofs.unsigned po) = Some (Vint current) ->
  Mem.load Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 16))) = Some (Vint previous) ->
  ocn_exec ge e le m (icr_from_edge version) t le' m' out ->
  exists remembered_le remembered_m,
    remembered_le ! ICG._controller = Some (Vptr cb co) /\
    Mem.load Mint16unsigned remembered_m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 16))) =
      Some (Vint (Int.zero_ext 16 current)) /\
    Mem.load Mint16unsigned remembered_m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))) =
      Some (Vint (Int.zero_ext 16 (edge_pressed current previous))) /\
    ocn_exec ge e remembered_le remembered_m (icr_after_remember version) t le' m' out.

Theorem icr_actual_edge_then_remember : InkControllerRememberedCut.
Proof.
  unfold InkControllerRememberedCut.
  intros version e le m cb co pb po current previous t le' m' out
    Hcontrollers Hpads Hroom Hcontroller Hdata Hsample Hprevious Hrun.
  assert (cb <> pb) as Hseparate by (eapply Genv.global_addresses_distinct; eauto; discriminate).
  destruct (icr_source version) as (Hsource & HnormalEdge & HnormalDown & HkeepEdge & HkeepDown).
  rewrite Hsource in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HnormalEdge Hrun)
    as (edge_le & edge_m & edge_t & rest_t & Htrace & Hedge & Hrest).
  destruct (ice_actual_edge_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcontroller Hdata Hsample Hprevious Hedge)
    as (HedgeStore & -> & _).
  assert (edge_le ! ICG._controller = Some (Vptr cb co)) as Hcontroller2 by
    (rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hedge HkeepEdge); exact Hcontroller).
  assert (Mem.load Mint32 edge_m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 24))) =
    Some (Vptr pb po)) as Hdata2 by
    (rewrite (icr_pressed_store_preserves_data _ _ _ _ _ Hroom HedgeStore); exact Hdata).
  assert (Mem.load Mint16unsigned edge_m pb (Ptrofs.unsigned po) = Some (Vint current)) as Hsample2 by
    (rewrite <- Hsample; eapply Mem.load_store_other; [exact HedgeStore|left; congruence]).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HnormalDown Hrest)
    as (remembered_le & remembered_m & remember_t & suf & Htrace2 & Hremember & Hsuffix).
  destruct (icr_actual_remember_store _ _ _ _ _ _ _ _ _ _ _ _ _
    Hcontroller2 Hdata2 Hsample2 Hremember) as (HrememberStore & -> & _).
  exists remembered_le, remembered_m. split.
  - rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hremember HkeepDown). exact Hcontroller2.
  - split.
    + rewrite (Mem.load_store_same _ _ _ _ _ _ HrememberStore).
      change (Some (Vint (Int.zero_ext 16 (Int.zero_ext 16 current))) =
        Some (Vint (Int.zero_ext 16 current))).
      rewrite Int.zero_ext_idem by lia. reflexivity.
    + split.
      * rewrite (icr_remember_store_preserves_pressed _ _ _ _ _ Hroom HrememberStore).
        rewrite (Mem.load_store_same _ _ _ _ _ _ HedgeStore).
        change (Some (Vint (Int.zero_ext 16 (Int.zero_ext 16 (edge_pressed current previous)))) =
          Some (Vint (Int.zero_ext 16 (edge_pressed current previous)))).
        rewrite Int.zero_ext_idem by lia. reflexivity.
      * cbn in Htrace, Htrace2. subst. exact Hsuffix.
Qed.

Corollary icr_remembered_a_is_current_sample : forall current,
  a_button_down (Int.zero_ext 16 current) = a_button_down current.
Proof.
  intro current. unfold a_button_down.
  rewrite Int.bits_zero_ext by lia. reflexivity.
Qed.
