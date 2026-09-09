(** The actual controller expression reads one sample twice, then stores the
    new-press mask. No physical-device or demo-playback effect is assumed here. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib Ctypes
  Events Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkControllerSource
  InkCopyCaller InkBackwardSource InkBackwardExecution ContactConsumerExecution ObjectContactNecessity
  EyerokRank15LiveMovement InputSemantics SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma ice_selected_fields : forall version,
  let ce := prog_comp_env (selected_clight_target version) in
  ibcc_field_ok ce ICG._Controller ICG._controllerData 24 = true /\
  ibcc_field_ok ce ICG._Controller ICG._buttonDown 16 = true /\
  ibcc_field_ok ce ICG._Controller ICG._buttonPressed 18 = true /\
  ibcc_field_ok ce ICG.__319 ICG._button 0 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._controller 156 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._input 2 = true.
Proof.
  intro version. cbn zeta. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Lemma ice_field_location : forall (ge : genv) e le m id tag field ty b ofs delta loc offset bf,
  le ! id = Some (Vptr b ofs) -> ibcc_field_ok ge tag field delta = true ->
  eval_lvalue ge e le m (ics_field id tag field ty) loc offset bf ->
  loc = b /\ offset = Ptrofs.add ofs (Ptrofs.repr delta) /\ bf = Full.
Proof.
  intros ge e le m id tag field ty b ofs delta loc offset bf Htemp Hfield Hl.
  eapply (ibcc_field_location ge e le m
    (Ederef (Etempvar id (tptr (Tstruct tag noattr))) (Tstruct tag noattr))
    tag field ty b ofs delta loc offset bf); [reflexivity| |exact Hfield|exact Hl].
  intros. eapply ibcc_deref_struct; eauto.
Qed.

Lemma ice_field_read : forall (ge : genv) e le m id tag field ty b ofs delta chunk value answer,
  le ! id = Some (Vptr b ofs) -> ibcc_field_ok ge tag field delta = true ->
  access_mode ty = By_value chunk ->
  Mem.load chunk m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some value ->
  eval_expr ge e le m (ics_field id tag field ty) answer -> answer = value.
Proof.
  intros ge e le m id tag field ty b ofs delta chunk value answer Htemp Hfield Hmode Hload Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ice_field_location _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htemp Hfield Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst end.
  all: match goal with Haccess : access_mode (typeof (ics_field _ _ _ _)) = ?mode |- _ =>
    change (access_mode ty = mode) in Haccess;
    rewrite Hmode in Haccess; try discriminate; inversion Haccess; subst end.
  match goal with Hread : Mem.loadv ?actual_chunk _ _ = Some answer |- _ =>
    change (Mem.load actual_chunk m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some answer)
      in Hread; congruence end.
Qed.

Lemma ice_edge_value : forall ge e le m current previous answer,
  le ! ICG._t'26 = Some (Vint current) ->
  le ! ICG._t'28 = Some (Vint current) ->
  le ! ICG._t'29 = Some (Vint previous) ->
  eval_expr ge e le m ics_edge_expression answer ->
  answer = Vint (edge_pressed current previous).
Proof.
  intros ge e le m current previous answer Ha Hb Hc Hr.
  unfold ics_edge_expression in Hr.
  repeat match goal with H : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion H; subst; clear H end.
  all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end].
  all: repeat match goal with
  | H : eval_expr _ _ _ _ (Etempvar ICG._t'26 _) ?v |- _ =>
      assert (v = Vint current) by (eapply ocn_temp_value; eauto); subst v; clear H
  | H : eval_expr _ _ _ _ (Etempvar ICG._t'28 _) ?v |- _ =>
      assert (v = Vint current) by (eapply ocn_temp_value; eauto); subst v; clear H
  | H : eval_expr _ _ _ _ (Etempvar ICG._t'29 _) ?v |- _ =>
      assert (v = Vint previous) by (eapply ocn_temp_value; eauto); subst v; clear H
  end.
  all: repeat match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    progress (cbn in H; inversion H; subst; clear H) end.
  reflexivity.
Qed.

Theorem ice_actual_edge_store : forall version e le m cb co pb po current previous t le' m' out,
  le ! ICG._controller = Some (Vptr cb co) ->
  Mem.load Mint32 m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 24))) = Some (Vptr pb po) ->
  Mem.load Mint16unsigned m pb (Ptrofs.unsigned po) = Some (Vint current) ->
  Mem.load Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 16))) = Some (Vint previous) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ics_edge_stage version) t le' m' out ->
  Mem.store Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18)))
    (Vint (Int.zero_ext 16 (edge_pressed current previous))) = Some m' /\
  t = E0 /\ out = Out_normal.
Proof.
  intros version e le m cb co pb po current previous t le' m' out Hcontroller Hdata Hsample Hprevious Hrun.
  destruct (ice_selected_fields version) as (HdataField & HdownField & HpressedField & HpadField & _).
  rewrite (proj1 (ics_source_cuts version)) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  all: repeat match goal with Hr : eval_expr _ _ ?temps _ ics_data ?v |- _ =>
    assert (temps ! ICG._controller = Some (Vptr cb co)) as Hnow
      by (repeat rewrite PTree.gso by discriminate; exact Hcontroller);
    assert (v = Vptr pb po) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tptr (Tstruct ICG.__319 noattr));
      [exact Hnow|exact HdataField|reflexivity|exact Hdata|exact Hr]); subst v; clear Hr Hnow end.
  all: repeat match goal with Hr : eval_expr _ _ ?temps _ (ics_pad_field ?id) ?v |- _ =>
    assert (temps ! id = Some (Vptr pb po)) as Hnow
      by (repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (v = Vint current) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tushort);
      [exact Hnow|exact HpadField|reflexivity|rewrite Ptrofs.add_zero; exact Hsample|exact Hr]);
    subst v; clear Hr Hnow end.
  all: match goal with Hr : eval_expr _ _ ?temps _ ics_down ?v |- _ =>
    assert (temps ! ICG._controller = Some (Vptr cb co)) as Hnow
      by (repeat rewrite PTree.gso by discriminate; exact Hcontroller);
    assert (v = Vint previous) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tushort);
      [exact Hnow|exact HdownField|reflexivity|exact Hprevious|exact Hr]); subst v end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  lazymatch goal with Hl : eval_lvalue _ ?env ?temps ?memory ics_pressed _ _ _ |- _ =>
    assert (temps ! ICG._controller = Some (Vptr cb co)) as HstoreNow
      by (repeat rewrite PTree.gso by discriminate; exact Hcontroller);
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) env temps memory
      ICG._controller ICG._Controller ICG._buttonPressed tushort cb co 18 _ _ _ HstoreNow HpressedField Hl)
      as (-> & -> & ->) end.
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory ics_edge_expression ?v |- _ =>
    assert (v = Vint (edge_pressed current previous)) as Hvalue by
      (eapply (ice_edge_value ge env temps memory current previous);
        [repeat rewrite PTree.gso by discriminate; apply PTree.gss
        |rewrite PTree.gso by discriminate; apply PTree.gss|apply PTree.gss|exact Hr]); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  split; [assumption|]. split; reflexivity.
Qed.

Lemma ice_edge_bit : forall current previous,
  Int.testbit (Int.zero_ext 16 (edge_pressed current previous)) 15 =
    (a_button_down current && negb (a_button_down previous)).
Proof.
  intros. rewrite Int.bits_zero_ext by lia. cbn [zlt].
  unfold edge_pressed, a_button_down.
  rewrite Int.bits_and, Int.bits_xor by (change (0 <= 15 < 32); lia).
  destruct (Int.testbit current 15), (Int.testbit previous 15); reflexivity.
Qed.

Definition InkControllerEdgeCut : Prop :=
  forall version e le m cb co pb po current previous t le' m' out pressed,
  le ! ICG._controller = Some (Vptr cb co) ->
  Mem.load Mint32 m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 24))) = Some (Vptr pb po) ->
  Mem.load Mint16unsigned m pb (Ptrofs.unsigned po) = Some (Vint current) ->
  Mem.load Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 16))) = Some (Vint previous) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ics_edge_stage version) t le' m' out ->
  Mem.load Mint16unsigned m' cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))) = Some (Vint pressed) ->
  Int.testbit pressed 15 = (a_button_down current && negb (a_button_down previous)).

Theorem ice_actual_pressed_bit_is_sample_edge : InkControllerEdgeCut.
Proof.
  unfold InkControllerEdgeCut.
  intros version e le m cb co pb po current previous t le' m' out pressed Hcontroller Hdata Hsample Hprevious Hrun Hpressed.
  destruct (ice_actual_edge_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcontroller Hdata Hsample Hprevious Hrun)
    as [Hstore _].
  rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore) in Hpressed.
  change (Some (Vint (Int.zero_ext 16 (Int.zero_ext 16 (edge_pressed current previous)))) =
    Some (Vint pressed)) in Hpressed.
  rewrite Int.zero_ext_idem in Hpressed by lia. inversion Hpressed; subst pressed.
  apply ice_edge_bit.
Qed.

Corollary ice_held_a_cannot_be_a_new_sample_edge : forall current previous,
  a_button_down current = true -> a_button_down previous = true ->
  Int.testbit (Int.zero_ext 16 (edge_pressed current previous)) 15 = false.
Proof. intros. rewrite ice_edge_bit, H, H0. reflexivity. Qed.

(** A missing previous-down record is genuinely different from a coherent
    held-A boundary. This arithmetic witness is not a reachable SSL setup. *)
Example ice_unmatched_initial_sample_is_distinct :
  Int.testbit (Int.zero_ext 16 (edge_pressed a_button_mask Int.zero)) 15 = true /\
  Int.testbit (Int.zero_ext 16 (edge_pressed a_button_mask a_button_mask)) 15 = false.
Proof. vm_compute. split; reflexivity. Qed.
