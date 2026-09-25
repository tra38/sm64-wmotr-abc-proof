(** Recover the actual duration read, rather than assuming the descriptor's
    contents before the gate.  The real increment can precede this read. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkLandingHistorySource
  InkLandingHistoryGate InkMovingBackwardSource InkLandingExecution
  InkBackwardSource InkCopyCaller InkBackwardExecution InkFloorResetExecution
  InkControllerSource InkControllerEdge InkMarioInputFlag ContactConsumerExecution
  ObjectContactNecessity EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Opaque selected_clight_target.

Lemma ild_field_read_is_load : forall (ge : genv) e le m id tag field ty b ofs delta chunk answer,
  le ! id = Some (Vptr b ofs) -> ibcc_field_ok ge tag field delta = true ->
  access_mode ty = By_value chunk ->
  eval_expr ge e le m (ics_field id tag field ty) answer ->
  Mem.load chunk m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some answer.
Proof.
  intros ge e le m id tag field ty b ofs delta chunk answer Htemp Hfield Hmode Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ice_field_location _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htemp Hfield Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst end.
  all: match goal with Haccess : access_mode (typeof (ics_field _ _ _ _)) = ?mode |- _ =>
    change (access_mode ty = mode) in Haccess;
    rewrite Hmode in Haccess; try discriminate; inversion Haccess; subst end.
  assumption.
Qed.

Lemma ild_increment_expression_requires_integer : forall ge e le m input answer,
  le ! IMB._t'15 = Some input ->
  eval_expr ge e le m ilh_increment_value answer ->
  exists before, input = Vint before.
Proof.
  intros ge e le m input answer Hinput Hread. unfold ilh_increment_value in Hread.
  inversion Hread; subst.
  - match goal with H : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion H; subst; clear H end.
    all: try solve [match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end].
    match goal with H : eval_expr _ _ _ _ (Etempvar IMB._t'15 _) ?v |- _ =>
      assert (v = input) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
    destruct input; try solve [eexists; reflexivity].
    all: match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some ?v |- _ =>
      change (None = Some v) in H; discriminate end.
  - match goal with H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma ild_executed_increment_has_integer_input : forall version e le m mb mo t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_increment version) t le' m' out ->
  exists before, ilh_timer_load m mb mo = Some (Vint before).
Proof.
  intros version e le m mb mo t le' m' out Hm Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  all: match goal with Hread : eval_expr ?ge ?env ?temps ?mem imb_timer ?input,
    Hexpr : eval_expr ?ge ?env ?next ?mem ilh_increment_value ?answer |- _ =>
    destruct (ild_increment_expression_requires_integer ge env next mem input answer
      ltac:(apply PTree.gss) Hexpr) as (before & Hvalue);
    subst input; exists before;
    exact (ild_field_read_is_load ge env temps mem IMB._m IMB._MarioState IMB._actionTimer
      tushort mb mo 26 Mint16unsigned (Vint before) Hm (proj1 (imb_control_fields version)) eq_refl Hread)
  end.
Qed.

Lemma ild_duration_false_reads_integer : forall ge e le m timer answer,
  le ! IMB._t'6 = Some (Vint timer) ->
  eval_expr ge e le m ilh_duration_test answer ->
  bool_val answer tint m = Some false ->
  exists frames, le ! IMB._t'13 = Some (Vint frames) /\ Int.signed timer < Int.signed frames.
Proof.
  intros ge e le m timer answer Htimer Hread Hfalse.
  unfold ilh_duration_test in Hread. inversion Hread; subst.
  - match goal with H : eval_expr _ _ _ _ (Etempvar IMB._t'6 _) ?v |- _ =>
      assert (v = Vint timer) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Etempvar IMB._t'13 _) _ |- _ =>
      inversion H; subst; clear H end.
    all: try solve [match goal with H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end].
    match goal with H : sem_binary_operation _ _ _ _ ?v _ _ = Some _ |- _ => destruct v end.
    all: try solve [match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      first [change (None = Some answer) in H; discriminate
      |change (Some Vundef = Some answer) in H; inversion H; subst; discriminate Hfalse] end].
    match goal with Htemp : le ! IMB._t'13 = Some (Vint ?frames),
      Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      change (Some (Val.of_bool (negb (Int.lt timer frames))) = Some answer) in Hsem;
      inversion Hsem; subst answer;
      exists frames; split; [exact Htemp|];
      destruct (Int.lt timer frames) eqn:Hlt; cbn in Hfalse; try discriminate;
      unfold Int.lt in Hlt; destruct (zlt (Int.signed timer) (Int.signed frames)); congruence end.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Theorem ild_normal_duration_guard_reads_its_live_bound :
  forall version e le m db dofs timer t le' m',
  le ! IMB._landingAction = Some (Vptr db dofs) ->
  le ! IMB._t'6 = Some (Vint timer) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_duration_guard version) t le' m' Out_normal ->
  exists frames,
    Mem.load Mint16signed m db (Ptrofs.unsigned dofs) = Some (Vint frames) /\
    Int.signed timer < Int.signed frames /\ t = E0 /\ m' = m /\
    le' = PTree.set IMB._t'13 (Vint frames) le.
Proof.
  intros version e le m db dofs timer t le' m' Hd Htimer Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IMB._t'13 ilh_frames) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hbranch).
  inversion Hread; subst.
  match goal with H : eval_expr ?ge ?env ?temps ?mem ilh_frames ?v |- _ =>
    assert (Mem.load Mint16signed mem db (Ptrofs.unsigned dofs) = Some v) as Hload by
      (pose proof (ild_field_read_is_load (Clight.globalenv (selected_clight_target version))
        env temps mem IMB._landingAction IMB._LandingAction IMB._numFrames tshort db dofs 0
        Mint16signed v Hd (ilh_frames_field version) eq_refl H) as Hr;
       rewrite Ptrofs.add_zero in Hr; exact Hr) end.
  inversion Hbranch; subst. destruct b.
  - exfalso. eapply ilh_duration_return_not_normal; eassumption.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : eval_expr ?ge ?env ?temps ?mem ilh_duration_test ?answer,
      Hb : bool_val ?answer _ _ = Some false |- _ =>
      destruct (ild_duration_false_reads_integer ge env temps mem timer answer
        ltac:(rewrite PTree.gso by discriminate; exact Htimer) H Hb)
        as (frames & Htemp & Hbound) end.
    rewrite PTree.gss in Htemp. inversion Htemp; subst.
    exists frames. repeat split; assumption || reflexivity.
Qed.

Theorem ild_executed_gate_returns_timer_below_live_duration :
  forall version e le m mb mo db dofs before t le' m',
  le ! IMB._m = Some (Vptr mb mo) ->
  le ! IMB._landingAction = Some (Vptr db dofs) ->
  ilh_timer_load m mb mo = Some (Vint before) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_gate version) t le' m' Out_normal ->
  exists frames,
    ilh_timer_load m' mb mo = Some (Vint (ilh_next_timer before)) /\
    Mem.load Mint16signed m' db (Ptrofs.unsigned dofs) = Some (Vint frames) /\
    Int.unsigned (ilh_next_timer before) < Int.signed frames /\ t = E0.
Proof.
  intros version e le m mb mo db dofs before t le' m' Hm Hd Htimer Hrun.
  destruct (ilh_source_cuts version) as (_ & _ & _ & Hshape & _). rewrite Hshape in Hrun.
  assert (ibk_normal (ilh_increment version) = true) as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suf & Htrace & Hincrement & Hguard).
  destruct (ilh_actual_increment_stores_compared_timer version e le m mb mo before
    pre middle memory Out_normal Hm Htimer Hincrement)
    as (Hstore & Htemps & Hpre & _ & Hstored). subst middle.
  destruct (ild_normal_duration_guard_reads_its_live_bound version e
    (PTree.set IMB._t'6 (Vint (ilh_next_timer before)) (PTree.set IMB._t'15 (Vint before) le))
    memory db dofs (ilh_next_timer before) suf le' m'
    ltac:(repeat rewrite PTree.gso by discriminate; exact Hd)
    ltac:(apply PTree.gss) Hguard)
    as (frames & Hframes & Hbound & Hsuf & Hmemory & Htemps). subst m'.
  exists frames. split; [exact Hstored|]. split; [exact Hframes|].
  split; [rewrite <- ilh_next_timer_signed_unsigned; exact Hbound|].
  rewrite Htrace, Hpre, Hsuf. reflexivity.
Qed.

Theorem ild_executed_gate_reads_and_bounds_timer :
  forall version e le m mb mo db dofs t le' m',
  le ! IMB._m = Some (Vptr mb mo) ->
  le ! IMB._landingAction = Some (Vptr db dofs) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_gate version) t le' m' Out_normal ->
  exists before frames,
    ilh_timer_load m mb mo = Some (Vint before) /\
    ilh_timer_load m' mb mo = Some (Vint (ilh_next_timer before)) /\
    Mem.load Mint16signed m' db (Ptrofs.unsigned dofs) = Some (Vint frames) /\
    Int.unsigned (ilh_next_timer before) < Int.signed frames.
Proof.
  intros version e le m mb mo db dofs t le' m' Hm Hd Hrun.
  pose proof Hrun as Hparts.
  destruct (ilh_source_cuts version) as (_ & _ & _ & Hshape & _). rewrite Hshape in Hparts.
  assert (ibk_normal (ilh_increment version) = true) as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hparts)
    as (middle & memory & pre & suf & Htrace & Hincrement & Hguard).
  destruct (ild_executed_increment_has_integer_input version e le m mb mo pre middle memory
    Out_normal Hm Hincrement) as (before & Htimer).
  destruct (ild_executed_gate_returns_timer_below_live_duration version e le m mb mo db dofs before
    t le' m' Hm Hd Htimer Hrun) as (frames & Hstored & Hframes & Hbound & _).
  exists before, frames. repeat split; assumption.
Qed.
