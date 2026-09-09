(** The executed duration gate reads, increments, narrows and stores the
    actual action timer, then compares that same value with numFrames. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkLandingHistorySource
  InkMovingBackwardSource InkLandingExecution InkBackwardSource InkCopyCaller
  InkBackwardExecution InkFloorResetExecution InkControllerSource InkControllerEdge
  InkMarioInputFlag ContactConsumerExecution ObjectContactNecessity
  EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ilh_timer_load m mb mo :=
  Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26))).
Definition ilh_next_timer before := Int.zero_ext 16 (Int.add before Int.one).

Lemma ilh_frames_field : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IMB._LandingAction IMB._numFrames 0 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IMB._LandingAction IMB._numFrames 0 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Lemma ilh_increment_expression_value : forall ge e le m before answer,
  le ! IMB._t'15 = Some (Vint before) ->
  eval_expr ge e le m ilh_increment_value answer ->
  answer = Vint (ilh_next_timer before).
Proof.
  intros ge e le m before answer Hbefore Hr. unfold ilh_increment_value in Hr.
  inversion Hr; subst.
  - match goal with H : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion H; subst; clear H end.
    + match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
        assert (v = Vint before) by (eapply ocn_temp_value; eauto); subst v end.
      match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
      match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
      match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
      reflexivity.
    + match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
  - match goal with H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
Qed.

Theorem ilh_actual_increment_stores_compared_timer :
  forall version e le m mb mo before t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> ilh_timer_load m mb mo = Some (Vint before) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_increment version) t le' m' out ->
  Mem.store Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26)))
    (Vint (ilh_next_timer before)) = Some m' /\
  le' = PTree.set IMB._t'6 (Vint (ilh_next_timer before))
    (PTree.set IMB._t'15 (Vint before) le) /\
  t = E0 /\ out = Out_normal /\
  ilh_timer_load m' mb mo = Some (Vint (ilh_next_timer before)).
Proof.
  intros version e le m mb mo before t le' m' out Hm Htimer Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  all: match goal with H : eval_expr _ _ _ _ imb_timer ?v |- _ =>
    assert (v = Vint before) by (eapply imb_ushort_field_read;
      [exact Hm|exact (proj1 (imb_control_fields version))|exact Htimer|exact H]); subst v end.
  all: match goal with H : eval_expr ?ge ?env ?temps ?memory ilh_increment_value ?v |- _ =>
    assert (v = Vint (ilh_next_timer before)) by
      (eapply (ilh_increment_expression_value ge env temps memory before); [apply PTree.gss|exact H]); subst v end.
  all: match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  all: try contradiction.
  lazymatch goal with Hl : eval_lvalue _ ?env ?temps ?memory imb_timer _ _ _ |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as Hnow
      by (repeat rewrite PTree.gso by discriminate; exact Hm);
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) env temps memory
      IMB._m IMB._MarioState IMB._actionTimer tushort mb mo 26 _ _ _
      Hnow (proj1 (imb_control_fields version)) Hl) as (-> & -> & ->) end.
  match goal with H : eval_expr _ _ _ _ (Etempvar IMB._t'6 _) ?v |- _ =>
    assert (v = Vint (ilh_next_timer before)) by (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst v end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
  lazymatch goal with Hstore : Mem.storev _ ?memory (Vptr ?b ?ofs) _ = Some ?final |- _ =>
    change (Mem.store Mint16unsigned memory b (Ptrofs.unsigned ofs)
      (Vint (Int.zero_ext 16 (ilh_next_timer before))) = Some final) in Hstore;
    unfold ilh_next_timer in Hstore; rewrite Int.zero_ext_idem in Hstore by lia;
    fold (ilh_next_timer before) in Hstore;
    split; [exact Hstore|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    unfold ilh_timer_load; rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore);
    change (Some (Vint (Int.zero_ext 16 (ilh_next_timer before))) =
      Some (Vint (ilh_next_timer before))); unfold ilh_next_timer;
    rewrite Int.zero_ext_idem by lia; reflexivity end.
Qed.

Lemma ilh_duration_return_not_normal : forall version ge e le m t le' m',
  ~ ocn_exec ge e le m (ilh_duration_yes version) t le' m' Out_normal.
Proof.
  intros version ge e le m t le' m' Hrun.
  destruct (ilh_duration_return_shape version) as [Hshape Hnormal]. rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suf & Htrace & Hbefore & Hreturn).
  inversion Hreturn.
Qed.

Lemma ilh_duration_comparison_value : forall ge e le m timer frames answer,
  le ! IMB._t'6 = Some (Vint timer) -> le ! IMB._t'13 = Some (Vint frames) ->
  eval_expr ge e le m ilh_duration_test answer ->
  answer = Val.of_bool (negb (Int.lt timer frames)).
Proof.
  intros ge e le m timer frames answer Htimer Hframes Hr.
  unfold ilh_duration_test in Hr. inversion Hr; subst.
  - match goal with H : eval_expr _ _ _ _ (Etempvar IMB._t'6 _) ?v |- _ =>
      assert (v = Vint timer) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Etempvar IMB._t'13 _) ?v |- _ =>
      assert (v = Vint frames) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some answer |- _ =>
      change (Some (Val.of_bool (negb (Int.lt timer frames))) = Some answer) in H;
      inversion H; reflexivity end.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma ilh_duration_fallthrough_bound :
  forall version e le m db dofs timer frames t le' m',
  le ! IMB._landingAction = Some (Vptr db dofs) ->
  le ! IMB._t'6 = Some (Vint timer) ->
  Mem.load Mint16signed m db (Ptrofs.unsigned dofs) = Some (Vint frames) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_duration_guard version) t le' m' Out_normal ->
  Int.signed timer < Int.signed frames /\ t = E0 /\ m' = m /\
  le' = PTree.set IMB._t'13 (Vint frames) le.
Proof.
  intros version e le m db dofs timer frames t le' m' Hdescriptor Htimer Hframes Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IMB._t'13 ilh_frames) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hbranch).
  inversion Hread; subst.
  match goal with H : eval_expr _ _ _ _ ilh_frames ?v |- _ =>
    assert (v = Vint frames) by (eapply ice_field_read with
      (ge := Clight.globalenv (selected_clight_target version)) (ty := tshort);
      [exact Hdescriptor|exact (ilh_frames_field version)|reflexivity
      |rewrite Ptrofs.add_zero; exact Hframes|exact H]); subst v end.
  inversion Hbranch; subst.
  match goal with H : eval_expr ?ge ?env ?temps ?memory ilh_duration_test ?v |- _ =>
    assert (v = Val.of_bool (negb (Int.lt timer frames))) by
      (eapply (ilh_duration_comparison_value ge env temps memory timer frames);
        [rewrite PTree.gso by discriminate; exact Htimer|apply PTree.gss|exact H]); subst v end.
  destruct b.
  - exfalso. eapply ilh_duration_return_not_normal; eassumption.
  - match goal with H : bool_val (Val.of_bool (negb (Int.lt timer frames))) _ _ = Some false |- _ =>
      destruct (Int.lt timer frames) eqn:Hlt; cbn in H; try discriminate end.
    match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H; subst end.
    split.
    + unfold Int.lt in Hlt. destruct (zlt (Int.signed timer) (Int.signed frames)); congruence.
    + repeat split; reflexivity.
Qed.

Lemma ilh_next_timer_signed_unsigned : forall before,
  Int.signed (ilh_next_timer before) = Int.unsigned (ilh_next_timer before).
Proof.
  intros before. unfold ilh_next_timer.
  apply Int.signed_eq_unsigned.
  pose proof (Int.zero_ext_range 16 (Int.add before Int.one) ltac:(change (0 <= 16 < 32); lia)) as Hrange.
  change (0 <= Int.unsigned (Int.zero_ext 16 (Int.add before Int.one)) < 65536) in Hrange.
  change (Int.unsigned (Int.zero_ext 16 (Int.add before Int.one)) <= 2147483647).
  lia.
Qed.

Definition InkActualLandingDurationGate : Prop :=
  forall version e le m mb mo db dofs before frames t le' m',
  le ! IMB._m = Some (Vptr mb mo) ->
  le ! IMB._landingAction = Some (Vptr db dofs) -> mb <> db ->
  ilh_timer_load m mb mo = Some (Vint before) ->
  Mem.load Mint16signed m db (Ptrofs.unsigned dofs) = Some (Vint frames) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_gate version) t le' m' Out_normal ->
  Mem.store Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26)))
    (Vint (ilh_next_timer before)) = Some m' /\
  ilh_timer_load m' mb mo = Some (Vint (ilh_next_timer before)) /\
  Int.unsigned (ilh_next_timer before) < Int.signed frames /\
  le' ! IMB._m = Some (Vptr mb mo) /\
  le' ! IMB._landingAction = Some (Vptr db dofs) /\ t = E0.

Theorem ilh_actual_duration_gate_bounds_its_stored_timer : InkActualLandingDurationGate.
Proof.
  unfold InkActualLandingDurationGate.
  intros version e le m mb mo db dofs before frames t le' m'
    Hm Hdescriptor Hseparate Htimer Hframes Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & _ & Hshape & _). rewrite Hshape in Hrun.
  assert (ibk_normal (ilh_increment version) = true) as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suf & Htrace & Hincrement & Hguard).
  destruct (ilh_actual_increment_stores_compared_timer _ _ _ _ _ _ _ _ _ _ _ Hm Htimer Hincrement)
    as (Hstore & Htemps & Hpre & _ & Hstored). subst middle.
  assert (Mem.load Mint16signed memory db (Ptrofs.unsigned dofs) = Some (Vint frames)) as HdescriptorFrame.
  { rewrite <- Hframes. eapply Mem.load_store_other; [exact Hstore|left; congruence]. }
  destruct (ilh_duration_fallthrough_bound version e
    (PTree.set IMB._t'6 (Vint (ilh_next_timer before)) (PTree.set IMB._t'15 (Vint before) le))
    memory db dofs (ilh_next_timer before) frames suf le' m'
    ltac:(repeat rewrite PTree.gso by discriminate; exact Hdescriptor)
    ltac:(apply PTree.gss) HdescriptorFrame Hguard)
    as (Hbound & Hsuf & Hmemory & Htemps). subst m' le'.
  split; [exact Hstore|]. split; [exact Hstored|].
  split; [rewrite <- ilh_next_timer_signed_unsigned; exact Hbound|].
  split; [repeat rewrite PTree.gso by discriminate; exact Hm|].
  split; [repeat rewrite PTree.gso by discriminate; exact Hdescriptor|].
  rewrite Htrace, Hpre, Hsuf. reflexivity.
Qed.
