(** Complete the actual callback's particle tail when its reached mask is 0.

    No particle-table value, terminator length or allocation frame is granted.
    A completed defined execution supplies its actual reads and loop exit.
    Its spawn branch cannot run because the actual mask test is false. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkMarioRawCopyCall
  InkScheduledActionSource InkMarioCallbackHistory InkRawCopySource
  InkRawCopyCompletion Area1Rank18CopyRead InkBackwardSource
  InkBackwardExecution ObjectContactNecessity ContactConsumerExecution
  OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition imzp_guard := Ebinop Oand (Etempvar ISC._particleFlags tuint)
  (Etempvar ISC._t'2 tuint) tuint.
Definition imzp_named_temp id expression := match expression with
| Etempvar found actual => Pos.eqb found id && (if type_eq actual tuint then true else false)
| _ => false end.
Definition imzp_is_guard expression := match expression with
| Ebinop Oand lhs rhs actual => imzp_named_temp ISC._particleFlags lhs &&
    imzp_named_temp ISC._t'2 rhs && (if type_eq actual tuint then true else false)
| _ => false end.

Lemma imzp_named_temp_exact : forall id expression,
  imzp_named_temp id expression = true -> expression = Etempvar id tuint.
Proof.
  intros id expression. destruct expression; try discriminate.
  cbn [imzp_named_temp]. intro H. apply andb_true_iff in H as [Hid Hty].
  apply Pos.eqb_eq in Hid. destruct (type_eq t tuint); try discriminate.
  subst; reflexivity.
Qed.

Lemma imzp_guard_exact : forall expression,
  imzp_is_guard expression = true -> expression = imzp_guard.
Proof.
  intros expression H. destruct expression; try discriminate.
  match goal with operation : binary_operation |- _ => destruct operation end;
    try discriminate.
  cbn [imzp_is_guard] in H. apply andb_true_iff in H as [Htemps Hty].
  apply andb_true_iff in Htemps as [Hleft Hright].
  apply imzp_named_temp_exact in Hleft. apply imzp_named_temp_exact in Hright.
  destruct (type_eq t tuint); try discriminate. subst; reflexivity.
Qed.

Lemma imzp_zero_mask_evaluates_false : forall ge e le m value b,
  le ! ISC._particleFlags = Some (Vint Int.zero) ->
  eval_expr ge e le m imzp_guard value ->
  bool_val value tuint m = Some b -> b = false.
Proof.
  intros ge e le m value b Hzero Hread Hbool.
  unfold imzp_guard in Hread. inversion Hread; subst.
  - match goal with Hl : eval_expr _ _ _ _ (Etempvar ISC._particleFlags _) ?v |- _ =>
      assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hsem : sem_binary_operation _ _ _ _ ?right _ _ = Some _ |- _ =>
      destruct right; cbn in Hsem; try discriminate end.
    match goal with Hsem : sem_and (Vint Int.zero) tuint (Vint ?right) tuint m = Some value |- _ =>
      change (Some (Vint (Int.and Int.zero right)) = Some value) in Hsem;
      rewrite Int.and_commut, Int.and_zero in Hsem;
      inversion Hsem; subst end.
    cbn in Hbool. inversion Hbool; reflexivity.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ =>
      inversion Hbad end.
Qed.

(** A structural certificate for this exact zero-mask tail.  Calls and
    assignments are rejected; only the actual disabled spawn arm is omitted. *)
Fixpoint imzp_readonly (s : statement) : bool := match s with
| Sskip | Sbreak | Scontinue | Sreturn _ => true
| Sset id _ => negb (Pos.eqb id ISC._particleFlags)
| Ssequence first rest | Sloop first rest => imzp_readonly first && imzp_readonly rest
| Sifthenelse guard yes no =>
    if imzp_is_guard guard then imzp_readonly no
    else imzp_readonly yes && imzp_readonly no
| _ => false end.

Lemma imzp_zero_tail_frame : forall ge e le m s t le' after out,
  ocn_exec ge e le m s t le' after out ->
  imzp_readonly s = true -> le ! ISC._particleFlags = Some (Vint Int.zero) ->
  t = E0 /\ after = m /\ le' ! ISC._particleFlags = Some (Vint Int.zero).
Proof.
  intros ge e le m s t le' after out Hrun.
  induction Hrun; cbn [imzp_readonly]; intros Hshape Hzero; try discriminate;
    try (repeat split; try reflexivity; assumption).
  - apply negb_true_iff in Hshape. apply Pos.eqb_neq in Hshape.
    repeat split; try reflexivity. rewrite PTree.gso by congruence. exact Hzero.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Ha Hzero) as (-> & -> & Hfirst).
    destruct (IHHrun2 Hb Hfirst) as (-> & -> & Hsecond).
    repeat split; try reflexivity; assumption.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - destruct (imzp_is_guard a) eqn:Hguard.
    + apply imzp_guard_exact in Hguard. subst a.
      assert (b = false) by (eapply imzp_zero_mask_evaluates_false; eauto).
      subst b. auto.
    + apply andb_true_iff in Hshape as [Ha Hb]. destruct b; auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Ha Hzero) as (-> & -> & Hfirst).
    destruct (IHHrun2 Hb Hfirst) as (-> & -> & Hsecond).
    repeat split; try reflexivity; assumption.
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Ha Hzero) as (-> & -> & Hfirst).
    destruct (IHHrun2 Hb Hfirst) as (-> & -> & Hsecond).
    destruct (IHHrun3 (andb_true_intro (conj Ha Hb)) Hsecond) as (-> & -> & Hthird).
    repeat split; try reflexivity; assumption.
Qed.

Lemma imzp_generated_tail_certificate : forall version,
  imzp_readonly (imrc_tail version) = true.
Proof. intros []; reflexivity. Qed.

Definition InkMarioZeroParticleTailFrame : Prop :=
  forall version ge e le m t le' after out,
  ocn_exec ge e le m (imrc_tail version) t le' after out ->
  le ! ISC._particleFlags = Some (Vint Int.zero) ->
  t = E0 /\ after = m /\ le' ! ISC._particleFlags = Some (Vint Int.zero).

Theorem imzp_actual_zero_particle_tail_preserves_memory : InkMarioZeroParticleTailFrame.
Proof.
  intros version ge e le m t le' after out Hrun Hzero.
  eapply imzp_zero_tail_frame; eauto using imzp_generated_tail_certificate.
Qed.

Definition InkMarioZeroParticleCallbackReturn : Prop :=
  forall version m t returned result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (imrc_body version))
    [] t returned result ->
  exists cut_le cut_m copy_trace copy_m copy_result,
    ClightBigstep.Clight2.eval_funcall ge cut_m
      (Internal (rank18_copy_body version)) [] copy_trace copy_m copy_result /\
    (cut_le ! ISC._particleFlags = Some (Vint Int.zero) ->
      returned = copy_m /\
      forall cb gb mb ob slot height,
        (slot < object_pool_capacity)%nat ->
        Genv.find_symbol ge IRC._gCurrentObject = Some cb ->
        Genv.find_symbol ge IRC._gMarioObject = Some gb ->
        Genv.find_symbol ge IRC._gMarioStates = Some mb ->
        Genv.find_symbol ge IRC._gObjectPool = Some ob ->
        Mem.load Mint32 cut_m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
        Mem.load Mint32 cut_m gb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
        Mem.load Mfloat32 cut_m mb 64 = Some (Vsingle height) ->
        Mem.load Mfloat32 returned ob (object_slot_offset slot + 164) = Some (Vsingle height) /\
        Mem.load Mfloat32 returned mb 64 = Some (Vsingle height) /\
        Mem.load Mfloat32 returned ob (object_slot_offset slot + 36) =
          Mem.load Mfloat32 cut_m ob (object_slot_offset slot + 36)).

Theorem imzp_zero_particle_callback_returns_matching_raw_height : InkMarioZeroParticleCallbackReturn.
Proof.
  unfold InkMarioZeroParticleCallbackReturn. cbn zeta.
  intros version m t returned result Hcall.
  destruct (imrc_completed_callback_reaches_matching_raw_copy version m t returned result Hcall)
    as (e & entry_le & entry_m & cut_le & cut_m & copy_le & copy_m & last_le & last_m &
      pre & copy_trace & suffix & out & copy_result & Htrace & Hentry & Hempty & HentryM &
      Hprefix & Hcopy & HrealCopy & Htemps & Htail & Hresult & Hfree & Hheights).
  exists cut_le, cut_m, copy_trace, copy_m, copy_result. split; [exact HrealCopy|].
  intro Hzero. assert (copy_le ! ISC._particleFlags = Some (Vint Int.zero)) as HcopyZero
    by (rewrite Htemps; exact Hzero).
  destruct (imzp_actual_zero_particle_tail_preserves_memory version _ _ _ _ _ _ _ _ Htail HcopyZero)
    as (_ & HtailMemory & _).
  subst e. change (Some last_m = Some returned) in Hfree.
  assert (returned = copy_m) by congruence. split; [assumption|].
  rewrite H. exact Hheights.
Qed.

Definition InkMarioZeroParticleBoundary : Prop :=
  InkMarioZeroParticleTailFrame /\ InkMarioZeroParticleCallbackReturn.

Theorem imzp_zero_particle_boundary_checked : InkMarioZeroParticleBoundary.
Proof.
  split; [exact imzp_actual_zero_particle_tail_preserves_memory|].
  exact imzp_zero_particle_callback_returns_matching_raw_height.
Qed.
