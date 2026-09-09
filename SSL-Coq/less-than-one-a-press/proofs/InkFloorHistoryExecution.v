(** Real quarter-step execution distinguishes the high-gap ceiling block
    from accepted grounded movement. No earlier query/callee effect is framed
    away: the complete-call cut retains its actual prefix memory. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkFloorHistorySource
  InkBackwardSource InkBackwardExecution InkCopyCaller InkCopyEntry
  InkFloorResetSource InkFloorResetExecution ObjectContactNecessity
  ContactConsumerExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ifh_returned n := Out_return (Some (Vint (Int.repr n), tint)).

Lemma ifh_return_exec : forall ge e le m n t le' m' out,
  ocn_exec ge e le m (ifh_return n) t le' m' out ->
  t = E0 /\ le' = le /\ m' = m /\ out = ifh_returned n.
Proof.
  intros ge e le m n t le' m' out Hrun. inversion Hrun; subst.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  repeat split; reflexivity.
Qed.

(** Inversion of an actual early-return gate keeps the non-taken continuation
    at the same memory and locals; a taken gate has no hidden memory effect. *)
Lemma ifh_return_gate : forall ge e le m cond n rest t le' m' out,
  ocn_exec ge e le m
    (Ssequence (Sifthenelse cond (ifh_return n) Sskip) rest) t le' m' out ->
  (ocn_test_value ge e le m cond true /\ t = E0 /\
    le' = le /\ m' = m /\ out = ifh_returned n) \/
  (ocn_test_value ge e le m cond false /\
    ocn_exec ge e le m rest t le' m' out).
Proof.
  intros ge e le m cond n rest t le' m' out Hrun.
  inversion Hrun; subst.
  - match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
      inversion Hg; subst; clear Hg end.
    destruct b.
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (ifh_return _) _ _ _ _ |- _ =>
        destruct (ifh_return_exec _ _ _ _ _ _ _ _ _ Hr) as (_ & _ & _ & Hbad) end.
      discriminate.
    + match goal with Hs : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
        inversion Hs; subst end.
      right. split; [unfold ocn_test_value; eauto|assumption].
  - match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
      inversion Hg; subst; clear Hg end.
    destruct b.
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (ifh_return _) _ _ _ _ |- _ =>
        destruct (ifh_return_exec _ _ _ _ _ _ _ _ _ Hr) as (-> & -> & -> & ->) end.
      left. repeat split; try reflexivity. unfold ocn_test_value; eauto.
    + match goal with Hs : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
        inversion Hs; subst end. contradiction.
Qed.

Lemma ifh_sequence_reassociate : forall ge e le m first second rest t le' m' out,
  ocn_exec ge e le m (Ssequence (Ssequence first second) rest) t le' m' out ->
  ocn_exec ge e le m (Ssequence first (Ssequence second rest)) t le' m' out.
Proof.
  intros ge e le m first second rest t le' m' out Hrun.
  inversion Hrun; subst.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence first second) _ _ _ _ |- _ =>
      inversion Hr; subst; clear Hr end.
    + unfold Eapp. rewrite <- app_assoc. eapply exec_Sseq_1; [eassumption|].
      eapply exec_Sseq_1; eassumption.
    + contradiction.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence first second) _ _ _ _ |- _ =>
      inversion Hr; subst; clear Hr end.
    + eapply exec_Sseq_1; [eassumption|]. eapply exec_Sseq_2; eassumption.
    + eapply exec_Sseq_2; eassumption.
Qed.

Lemma ifh_next_height_read : forall ge e le m nb no y answer,
  le ! IFH._nextPos = Some (Vptr nb no) ->
  Mem.load Mfloat32 m nb (Ptrofs.unsigned (Ptrofs.add no (Ptrofs.repr 4))) = Some (Vsingle y) ->
  eval_expr ge e le m (ifh_next 1) answer -> answer = Vsingle y.
Proof.
  intros ge e le m nb no y answer Hnext Hload Hread.
  pose proof (ibc_float_read _ _ _ _ IFH._nextPos 1 _ _ _ Hnext Hread) as Hactual.
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1)))
    with (Ptrofs.repr 4) in Hactual. congruence.
Qed.

Definition ifh_100 := Float32.of_bits (Int.repr 1120403456).
Definition ifh_160 := Float32.of_bits (Int.repr 1126170624).

Lemma ifh_leave_test : forall ge e le m y floor choice,
  le ! IFH._t'16 = Some (Vsingle y) ->
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  ocn_test_value ge e le m ifh_leave_guard choice ->
  choice = Float32.cmp Cgt y (Float32.add floor ifh_100).
Proof.
  intros ge e le m y floor choice Hy Hfloor [answer [Hread Hbool]].
  unfold ifh_leave_guard in Hread.
  repeat match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hr; subst; clear Hr end.
  all: try solve [match goal with Hb : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hb end].
  all: repeat match goal with
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._t'16 _) ?v |- _ =>
      assert (v = Vsingle y) by (eapply ocn_temp_value; eauto); subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._floorHeight _) ?v |- _ =>
      assert (v = Vsingle floor) by (eapply ocn_temp_value; eauto); subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ => inversion Hr; subst; clear Hr
  end.
  all: try solve [match goal with Hb : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion Hb end].
  all: repeat match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    progress (cbn in Hsem; inversion Hsem; subst; clear Hsem) end.
  change (bool_val (Val.of_bool (Float32.cmp Cgt y (Float32.add floor ifh_100)))
    tint m = Some choice) in Hbool.
  unfold ifh_100 in Hbool |- *. destruct (Float32.cmp Cgt y
    (Float32.add floor (Float32.of_bits (Int.repr 1120403456)))).
  - change (Some true = Some choice) in Hbool. congruence.
  - change (Some false = Some choice) in Hbool. congruence.
Qed.

Lemma ifh_y_ceil_test : forall ge e le m y ceiling choice,
  le ! IFH._t'18 = Some (Vsingle y) ->
  le ! IFH._ceilHeight = Some (Vsingle ceiling) ->
  ocn_test_value ge e le m ifh_y_ceil_guard choice ->
  choice = Float32.cmp Cge (Float32.add y ifh_160) ceiling.
Proof.
  intros ge e le m y ceiling choice Hy Hceiling [answer [Hread Hbool]].
  unfold ifh_y_ceil_guard in Hread.
  repeat match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hr; subst; clear Hr end.
  all: try solve [match goal with Hb : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hb end].
  all: repeat match goal with
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._t'18 _) ?v |- _ =>
      assert (v = Vsingle y) by (eapply ocn_temp_value; eauto); subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._ceilHeight _) ?v |- _ =>
      assert (v = Vsingle ceiling) by (eapply ocn_temp_value; eauto); subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ => inversion Hr; subst; clear Hr
  end.
  all: try solve [match goal with Hb : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion Hb end].
  all: repeat match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    progress (cbn in Hsem; inversion Hsem; subst; clear Hsem) end.
  change (bool_val (Val.of_bool (Float32.cmp Cge (Float32.add y ifh_160) ceiling))
    tint m = Some choice) in Hbool.
  unfold ifh_160 in Hbool |- *. destruct (Float32.cmp Cge
    (Float32.add y (Float32.of_bits (Int.repr 1126170624))) ceiling).
  - change (Some true = Some choice) in Hbool. congruence.
  - change (Some false = Some choice) in Hbool. congruence.
Qed.

Lemma ifh_leave_commit_returns_left_ground : forall version ge e le m t le' m' out,
  ocn_exec ge e le m (ifh_leave_commit version) t le' m' out ->
  out = ifh_returned 0.
Proof.
  intros version ge e le m t le' m' out Hrun.
  assert (ifh_leave_commit version =
    ocn_prepend (ocn_prefix_items 3 (ifh_leave_commit version)) (ifh_return 0)) as Hshape
    by (destruct version; reflexivity).
  assert (forallb ibk_normal (ocn_prefix_items 3 (ifh_leave_commit version)) = true)
    as Hnormal by (destruct version; reflexivity).
  rewrite Hshape in Hrun.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (rl & rm & pre & rest & Htrace & Hprefix & Hreturn).
  exact (proj2 (proj2 (proj2 (ifh_return_exec _ _ _ _ _ _ _ _ _ Hreturn)))).
Qed.

Lemma ifh_leave_ceiling_or_commit :
  forall version ge e le m nb no y ceiling t le' m' out,
  le ! IFH._nextPos = Some (Vptr nb no) ->
  le ! IFH._ceilHeight = Some (Vsingle ceiling) ->
  Mem.load Mfloat32 m nb (Ptrofs.unsigned (Ptrofs.add no (Ptrofs.repr 4))) = Some (Vsingle y) ->
  ocn_exec ge e le m (ifh_leave version) t le' m' out ->
  (Float32.cmp Cge (Float32.add y ifh_160) ceiling = true /\
    t = E0 /\ m' = m /\ out = ifh_returned 2) \/
  (Float32.cmp Cge (Float32.add y ifh_160) ceiling = false /\
    out = ifh_returned 0 /\
    ocn_exec ge e (PTree.set IFH._t'18 (Vsingle y) le) m
      (ifh_leave_commit version) t le' m' out).
Proof.
  intros version ge e le m nb no y ceiling t le' m' out Hnext Hceiling Hload Hrun.
  destruct (ifh_quarter_source_cuts version)
    as (_ & _ & _ & _ & _ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. apply ifh_sequence_reassociate in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IFH._t'18 (ifh_next 1))
    _ _ _ _ _ eq_refl Hrun) as (middle & memory & pre & rest & Htrace & Hset & Hrest).
  inversion Hset; subst; clear Hset.
  match goal with Hr : eval_expr _ _ _ _ (ifh_next 1) ?v |- _ =>
    assert (v = Vsingle y) by (eapply ifh_next_height_read; eauto); subst v; clear Hr end.
  destruct (ifh_return_gate _ _ _ _ _ _ _ _ _ _ _ Hrest) as [Hblocked|Hcommit].
  - destruct Hblocked as (Htest & -> & -> & -> & ->).
    pose proof (ifh_y_ceil_test _ _ _ _ y ceiling true (PTree.gss _ _ _)
      ltac:(rewrite PTree.gso by discriminate; exact Hceiling) Htest) as Hcmp.
    left. repeat apply conj; try reflexivity; congruence.
  - destruct Hcommit as [Htest Hcommit].
    pose proof (ifh_y_ceil_test _ _ _ _ y ceiling false (PTree.gss _ _ _)
      ltac:(rewrite PTree.gso by discriminate; exact Hceiling) Htest) as Hcmp.
    pose proof (ifh_leave_commit_returns_left_ground _ _ _ _ _ _ _ _ _ Hcommit) as Hout.
    right. repeat apply conj; try congruence; exact Hcommit.
Qed.

Definition InkHighFloorGapQuarterCut : Prop :=
  forall version e le m nb no y floor ceiling t le' m' out,
  le ! IFH._nextPos = Some (Vptr nb no) ->
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  le ! IFH._ceilHeight = Some (Vsingle ceiling) ->
  Mem.load Mfloat32 m nb (Ptrofs.unsigned (Ptrofs.add no (Ptrofs.repr 4))) = Some (Vsingle y) ->
  Float32.cmp Cgt y (Float32.add floor ifh_100) = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_post_water version) t le' m' out ->
  (Float32.cmp Cge (Float32.add y ifh_160) ceiling = true /\
    t = E0 /\ m' = m /\ out = ifh_returned 2) \/
  (Float32.cmp Cge (Float32.add y ifh_160) ceiling = false /\
    out = ifh_returned 0 /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IFH._t'18 (Vsingle y) (PTree.set IFH._t'16 (Vsingle y) le)) m
      (ifh_leave_commit version) t le' m' out).

(** The proof exposes the two actual loads of nextPos[Y]. Both occur before
    any write in this tail, so the high-gap test and ceiling test see the same
    Float32 value. A high gap never reaches the lower floor+160 test here. *)
Theorem ifh_high_gap_requires_ceiling_block_or_leaves_ground : InkHighFloorGapQuarterCut.
Proof.
  unfold InkHighFloorGapQuarterCut.
  intros version e le m nb no y floor ceiling t le' m' out
    Hnext Hfloor Hceiling Hload Hhigh Hrun.
  assert (ifh_post_water version = Ssequence (ifh_vertical version)
    (Ssequence (ifh_floor_ceil version) (ifh_accept version))) as Hpost
    by (destruct version; reflexivity).
  destruct (ifh_quarter_source_cuts version)
    as (_ & _ & _ & _ & _ & _ & _ & Hvertical & Hleave & _).
  rewrite Hpost, Hvertical in Hrun.
  apply ifh_sequence_reassociate in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IFH._t'16 (ifh_next 1))
    _ _ _ _ _ eq_refl Hrun) as (middle & memory & pre & rest & Htrace & Hset & Hrest).
  inversion Hset; subst; clear Hset.
  match goal with Hr : eval_expr _ _ _ _ (ifh_next 1) ?v |- _ =>
    assert (v = Vsingle y) by (eapply ifh_next_height_read; eauto); subst v; clear Hr end.
  inversion Hrest; subst.
  all: match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
    inversion Hg; subst; clear Hg end.
  all: assert (b = true) as Hb by
    (assert (b = Float32.cmp Cgt y (Float32.add floor ifh_100)) as Htest by
      (eapply ifh_leave_test;
        [apply PTree.gss|rewrite PTree.gso by discriminate; exact Hfloor|
         unfold ocn_test_value; eauto]); congruence).
  all: subst b.
  all: lazymatch goal with Hl : ClightBigstep.exec_stmt ?entry ?ge ?env ?temps ?mem
      (ifh_leave ?ver) ?tr ?last ?final ?o |- _ =>
    pose proof (ifh_leave_ceiling_or_commit ver ge env temps mem nb no y ceiling tr last final o
      ltac:(rewrite PTree.gso by discriminate; exact Hnext)
      ltac:(rewrite PTree.gso by discriminate; exact Hceiling)
      ltac:(eassumption) Hl) as Hclass end.
  - destruct Hclass as [(_ & _ & _ & Hbad)|(_ & Hbad & _)]; discriminate.
  - exact Hclass.
Qed.
