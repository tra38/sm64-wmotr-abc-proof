(** Connect the real US/JP quicksand-jump subtraction and immediate clamp
    to the safe-writer classification. The checkpoint precedes all later
    sound, animation and movement calls; their effects are not assumed away. *)
From Coq Require Import Bool Lia List Reals ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkLandingExecution InkBackwardSource InkBackwardExecution InkCopyCaller
  InkQuicksandSource InkQuicksandExpressions InkFloorResetExecution
  InkLandingHistoryGate InkMarioInputFlag InkControllerEdge ObjectContactNecessity
  ContactConsumerExecution Area2Rank12BContact JPBinary32DepthWrites
  InkStockSeedConditional SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ijc_body version := imb_body version IMBJumpClamp.
Definition ijc_yes version := match ibk_head (fn_body (ijc_body version)) with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Definition ijc_raw version := ibk_head (ijc_yes version).
Definition ijc_clamp version := ibk_head (rank12b_drop_sequences 1 (ijc_yes version)).
Definition ijc_calls version := rank12b_drop_sequences 2 (ijc_yes version).
Definition ijc_pair version := Ssequence (ijc_raw version) (ijc_clamp version).
Definition ijc_expression := Ebinop Osub (Etempvar IMB._t'6 tfloat)
  (Ebinop Omul (Ebinop Osub (Econst_int (Int.repr 7) tint)
    (Etempvar IMB._t'7 tushort) tint)
    (Econst_single (Float32.of_bits (Int.repr 1061997773)) tfloat) tfloat) tfloat.
Definition ijc_raw_value depth timer := Float32.sub depth
  (Float32.mul (Float32.of_int (Int.sub (Int.repr 7) timer)) jp_b32_eight_tenths).
Definition ijc_clamped raw := if Float32.cmp Clt raw jp_b32_one
  then jp_b32_one_point_one else raw.
Definition ijc_test := Ebinop Olt (Etempvar IMB._t'5 tfloat)
  (Econst_single (Float32.of_bits (Int.repr 1065353216)) tfloat) tint.

Lemma ijc_source : forall version,
  ijc_yes version = Ssequence (ijc_raw version)
    (Ssequence (ijc_clamp version) (ijc_calls version)) /\
  ijc_raw version = Ssequence (Sset IMB._t'6 iq_depth)
    (Ssequence (Sset IMB._t'7 imb_timer) (Sassign iq_depth ijc_expression)) /\
  ijc_clamp version = Ssequence (Sset IMB._t'5 iq_depth)
    (Sifthenelse ijc_test (Sassign iq_depth
      (Econst_single (Float32.of_bits (Int.repr 1066192077)) tfloat)) Sskip) /\
  ibk_normal (ijc_pair version) = true /\
  cce_keeps_temp IMB._m (ijc_pair version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ijc_expression_value : forall ge e le m depth timer answer,
  le ! IMB._t'6 = Some (Vsingle depth) -> le ! IMB._t'7 = Some (Vint timer) ->
  eval_expr ge e le m ijc_expression answer ->
  answer = Vsingle (ijc_raw_value depth timer).
Proof.
  intros ge e le m depth timer answer Hd Htimer Hread.
  unfold ijc_expression in Hread.
  repeat match goal with H : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion H; subst; clear H end.
  all: try solve [match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end].
  all: repeat match goal with
  | H : eval_expr _ _ _ _ (Etempvar IMB._t'6 _) ?v |- _ =>
      assert (v = Vsingle depth) by (eapply ocn_temp_value; eauto); subst v; clear H
  | H : eval_expr _ _ _ _ (Etempvar IMB._t'7 _) ?v |- _ =>
      assert (v = Vint timer) by (eapply ocn_temp_value; eauto); subst v; clear H
  | H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst
  | H : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ => inversion H; subst; clear H
  end.
  all: try solve [match goal with H : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion H end].
  all: repeat match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    progress (cbn in H; inversion H; subst; clear H) end.
  reflexivity.
Qed.

Lemma ijc_raw_store : forall version e le m mb mo depth timer t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  ilh_timer_load m mb mo = Some (Vint timer) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_raw version) t le' m' out ->
  Mem.store Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192)))
    (Vsingle (ijc_raw_value depth timer)) = Some m' /\
  t = E0 /\ out = Out_normal /\ le' ! IMB._m = Some (Vptr mb mo).
Proof.
  intros version e le m mb mo depth timer t le' m' out Hm Hd Htimer Hrun.
  destruct (ijc_source version) as (_ & Hshape & _).
  rewrite Hshape in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with H : eval_expr _ _ _ _ iq_depth ?v |- _ =>
    assert (v = Vsingle depth) by (eapply iq_depth_read; eauto); subst v end.
  all: match goal with H : eval_expr _ _ ?temps _ imb_timer ?v |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as Hnow
      by (rewrite PTree.gso by discriminate; exact Hm);
    assert (v = Vint timer) by (eapply imb_ushort_field_read;
      [exact Hnow|exact (proj1 (imb_control_fields version))|exact Htimer|exact H]); subst v end.
  all: match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  all: try contradiction.
  lazymatch goal with H : eval_lvalue _ _ ?temps _ iq_depth _ _ _ |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as HmStore
      by (repeat rewrite PTree.gso by discriminate; exact Hm);
    destruct (imb_depth_location _ _ _ _ _ _ _ _ _ HmStore H) as (-> & -> & ->) end.
  match goal with H : eval_expr ?ge ?env ?temps ?memory ijc_expression ?v |- _ =>
    assert (v = Vsingle (ijc_raw_value depth timer)) by
      (eapply (ijc_expression_value ge env temps memory depth timer);
       [rewrite PTree.gso by discriminate; apply PTree.gss|apply PTree.gss|exact H]); subst v end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
  split; [assumption|]. split; [reflexivity|]. split; [reflexivity|].
  repeat rewrite PTree.gso by discriminate. exact Hm.
Qed.

Lemma ijc_test_value : forall ge e le m raw answer,
  le ! IMB._t'5 = Some (Vsingle raw) ->
  eval_expr ge e le m ijc_test answer ->
  answer = Val.of_bool (Float32.cmp Clt raw jp_b32_one).
Proof.
  intros ge e le m raw answer Hraw Hread. unfold ijc_test in Hread.
  inversion Hread; subst.
  - match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vsingle raw) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ => inversion H; subst; clear H end.
    + match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some answer |- _ =>
        cbn in H; inversion H; reflexivity end.
    + match goal with H : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion H end.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma ijc_clamp_exact : forall version e le m mb mo raw t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle raw) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_clamp version) t le' m' out ->
  Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) =
    Some (Vsingle (ijc_clamped raw)) /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m mb mo raw t le' m' out Hm Hd Hrun.
  destruct (ijc_source version) as (_ & _ & Hshape & _). rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IMB._t'5 iq_depth) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hbranch).
  inversion Hread; subst.
  match goal with H : eval_expr _ _ _ _ iq_depth ?v |- _ =>
    assert (v = Vsingle raw) by (eapply iq_depth_read; eauto); subst v end.
  inversion Hbranch; subst.
  match goal with H : eval_expr ?ge ?env ?temps ?memory ijc_test ?v |- _ =>
    assert (v = Val.of_bool (Float32.cmp Clt raw jp_b32_one)) by
      (eapply (ijc_test_value ge env temps memory raw); [apply PTree.gss|exact H]); subst v end.
  lazymatch goal with H : bool_val (Val.of_bool _) _ _ = Some ?b |- _ =>
    assert (b = Float32.cmp Clt raw jp_b32_one) by
      (destruct (Float32.cmp Clt raw jp_b32_one);
       [change (Some true = Some b) in H|change (Some false = Some b) in H];
       congruence); subst b end.
  destruct (Float32.cmp Clt raw jp_b32_one) eqn:Hcmp.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
      inversion H; subst; clear H end.
    lazymatch goal with H : eval_lvalue _ _ ?temps _ iq_depth _ _ _ |- _ =>
      assert (temps ! IMB._m = Some (Vptr mb mo)) as HclampM
        by (rewrite PTree.gso by discriminate; exact Hm);
      destruct (imb_depth_location _ _ _ _ mb mo _ _ _ HclampM H) as (-> & -> & ->) end.
    match goal with H : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ => inversion H; subst; clear H end.
    all: try solve [match goal with H : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion H end].
    match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
    match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
    match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
    split.
    + unfold ijc_clamped. rewrite Hcmp.
      erewrite Mem.load_store_same by eassumption. reflexivity.
    + split; reflexivity.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H; subst end.
    unfold ijc_clamped. rewrite Hcmp. repeat split; assumption || reflexivity.
Qed.

Theorem ijc_pair_exact : forall version e le m mb mo depth timer t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  ilh_timer_load m mb mo = Some (Vint timer) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_pair version) t le' m' out ->
  Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) =
    Some (Vsingle (jp_b32_quicksand_jump_outcome depth (Int.unsigned timer))) /\
  t = E0 /\ out = Out_normal.
Proof.
  intros version e le m mb mo depth timer t le' m' out Hm Hd Htimer Hrun.
  unfold ijc_pair in Hrun.
  assert (ibk_normal (ijc_raw version) = true) as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suf & Htrace & Hraw & Hclamp).
  destruct (ijc_raw_store _ _ _ _ _ _ _ _ _ _ _ _ Hm Hd Htimer Hraw)
    as (Hstore & Hpre & _ & Hmiddle).
  destruct (ijc_clamp_exact _ _ _ _ _ _ _ _ _ _ _ Hmiddle
    (Mem.load_store_same _ _ _ _ _ _ Hstore) Hclamp) as (Hload & Hsuf & Hout).
  assert (ijc_clamped (ijc_raw_value depth timer) =
    jp_b32_quicksand_jump_outcome depth (Int.unsigned timer)) as Heq.
  { unfold ijc_clamped, ijc_raw_value, jp_b32_quicksand_jump_outcome, jp_b32_quicksand_jump_raw.
    unfold Int.sub. rewrite Int.unsigned_repr by (change (0 <= 7 <= 4294967295); lia).
    reflexivity. }
  rewrite <- Heq. split; [exact Hload|]. subst. split; reflexivity.
Qed.

Definition InkJumpClampSafeWriter : Prop :=
  forall version e le m mb mo depth timer t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  ilh_timer_load m mb mo = Some (Vint timer) ->
  1 <= Int.unsigned timer <= 6 ->
  is_finite 24 128 (jp_b32_quicksand_jump_raw depth (Int.unsigned timer)) = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_pair version) t le' m' out ->
  exists after,
    Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) /\
    JPBinary32SafeDepthWriterOutcome depth after /\
    JPBinary32FiniteNonnegative after /\ t = E0 /\ out = Out_normal.

Theorem ijc_actual_pair_enters_safe_writer_classification : InkJumpClampSafeWriter.
Proof.
  intros version e le m mb mo depth timer t le' m' out Hm Hd Htimer Hrange Hfinite Hrun.
  destruct (ijc_pair_exact _ _ _ _ _ _ _ _ _ _ _ _ Hm Hd Htimer Hrun) as (Hload & Htrace & Hout).
  exists (jp_b32_quicksand_jump_outcome depth (Int.unsigned timer)).
  split; [exact Hload|]. split.
  - apply JPB32DepthQuicksandJumpClamp; assumption.
  - split; [apply jp_binary32_quicksand_jump_outcome_is_safe; exact Hfinite|]. auto.
Qed.

(** This is the actual taken branch, including its remaining helper calls.
    Its safe checkpoint is obtained before those calls, not imposed at the
    final return or at an unrelated execution. *)
Definition InkJumpClampBeforeHelpers : Prop :=
  forall version e le m mb mo depth timer t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  ilh_timer_load m mb mo = Some (Vint timer) ->
  1 <= Int.unsigned timer <= 6 ->
  is_finite 24 128 (jp_b32_quicksand_jump_raw depth (Int.unsigned timer)) = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_yes version) t le' m' out ->
  exists cut_le cut_m after,
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ijc_pair version) E0 cut_le cut_m Out_normal /\
    Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) /\
    JPBinary32SafeDepthWriterOutcome depth after /\ JPBinary32FiniteNonnegative after /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e cut_le cut_m
      (ijc_calls version) t le' m' out.

Theorem ijc_taken_branch_clamps_before_helpers : InkJumpClampBeforeHelpers.
Proof.
  intros version e le m mb mo depth timer t le' m' out Hm Hd Htimer Hrange Hfinite Hrun.
  rewrite (proj1 (ijc_source version)) in Hrun.
  assert (ibk_normal (ijc_raw version) = true) as Hr by (destruct version; reflexivity).
  assert (ibk_normal (ijc_clamp version) = true) as Hc by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hr Hrun)
    as (raw_le & raw_m & raw_t & rest_t & Htrace & Hraw & Hrest).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hc Hrest)
    as (cut_le & cut_m & clamp_t & calls_t & Hresttrace & Hclamp & Hcalls).
  assert (ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_pair version) (raw_t ++ clamp_t) cut_le cut_m Out_normal) as Hpair
    by (unfold ijc_pair; eapply exec_Sseq_1; eauto).
  destruct (ijc_actual_pair_enters_safe_writer_classification _ _ _ _ _ _ _ _ _ _ _ _
    Hm Hd Htimer Hrange Hfinite Hpair) as (after & Hload & Hsafe & Hnonnegative & Hempty & _).
  exists cut_le, cut_m, after.
  rewrite Hempty in Hpair. split; [exact Hpair|]. split; [exact Hload|].
  split; [exact Hsafe|]. split; [exact Hnonnegative|].
  rewrite Htrace, Hresttrace, app_assoc, Hempty. exact Hcalls.
Qed.

Corollary ijc_pair_extends_classified_history : forall inputs version e le m mb mo
    depth timer t le' m' out after final,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  ilh_timer_load m mb mo = Some (Vint timer) ->
  1 <= Int.unsigned timer <= 6 ->
  is_finite 24 128 (jp_b32_quicksand_jump_raw depth (Int.unsigned timer)) = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_pair version) t le' m' out ->
  Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) ->
  InkClassifiedDepthHistory inputs after final -> InkClassifiedDepthHistory inputs depth final.
Proof.
  intros inputs version e le m mb mo depth timer t le' m' out after final Hm Hd Htimer
    Hrange Hfinite Hrun Hafter Hrest.
  destruct (ijc_actual_pair_enters_safe_writer_classification _ _ _ _ _ _ _ _ _ _ _ _
    Hm Hd Htimer Hrange Hfinite Hrun) as (found & Hload & Hsafe & _).
  assert (after = found) by congruence. subst after. eapply ISCSafe; eauto.
Qed.

Definition ijc_increment version := match ibk_head (fn_body (ijc_body version)) with
| Ssequence first _ => first | _ => Sskip end.
Definition ijc_no version := match ibk_head (fn_body (ijc_body version)) with
| Ssequence _ (Sifthenelse _ _ no) => no | _ => Sskip end.
Definition ijc_enter version := ibk_head (fn_body (ijc_body version)).
Definition ijc_tail version := rank12b_drop_sequences 1 (fn_body (ijc_body version)).
Definition ijc_early_test := Ebinop Olt (Etempvar IMB._t'2 tushort)
  (Econst_int (Int.repr 6) tint) tint.
Lemma ijc_entry_source : forall version,
  fn_body (ijc_body version) = Ssequence (ijc_enter version) (ijc_tail version) /\
  ijc_enter version = Ssequence (ijc_increment version)
    (Sifthenelse ijc_early_test (ijc_yes version) (ijc_no version)) /\
  ijc_increment version = Ssequence (Sset IMB._t'2 imb_timer)
    (Sassign imb_timer (Ebinop Oadd (Etempvar IMB._t'2 tushort)
      (Econst_int Int.one tint) tint)) /\
  ibk_normal (ijc_increment version) = true /\ ibk_normal (ijc_yes version) = true /\
  fn_vars (ijc_body version) = [] /\
  fn_params (ijc_body version) =
    [(IMB._m, tptr (Tstruct IMB._MarioState noattr)); (IMB._animation1, tint);
     (IMB._animation2, tint); (IMB._endAction, tuint); (IMB._airAction, tuint)].
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ijc_early_values : forall before,
  Int.unsigned before < 6 ->
  Int.lt before (Int.repr 6) = true /\ 1 <= Int.unsigned (ilh_next_timer before) <= 6.
Proof.
  intros before Hsmall. pose proof (Int.unsigned_range before).
  assert (Int.unsigned before = 0 \/ Int.unsigned before = 1 \/
    Int.unsigned before = 2 \/ Int.unsigned before = 3 \/
    Int.unsigned before = 4 \/ Int.unsigned before = 5) as Hcases by lia.
  rewrite <- (Int.repr_unsigned before).
  destruct Hcases as [Hc | [Hc | [Hc | [Hc | [Hc | Hc]]]]];
    rewrite Hc; vm_compute; intuition congruence.
Qed.

Lemma ijc_increment_exact : forall version e le m mb mo before t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> ilh_timer_load m mb mo = Some (Vint before) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_increment version) t le' m' out ->
  Mem.store Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26)))
    (Vint (ilh_next_timer before)) = Some m' /\
  ilh_timer_load m' mb mo = Some (Vint (ilh_next_timer before)) /\
  le' = PTree.set IMB._t'2 (Vint before) le /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m mb mo before t le' m' out Hm Htimer Hrun.
  destruct (ijc_entry_source version) as (_ & _ & Hshape & _). rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IMB._t'2 imb_timer) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hstore).
  inversion Hread; subst.
  match goal with H : eval_expr _ _ _ _ imb_timer ?v |- _ =>
    assert (v = Vint before) by (eapply imb_ushort_field_read;
      [exact Hm|exact (proj1 (imb_control_fields version))|exact Htimer|exact H]); subst v end.
  inversion Hstore; subst; clear Hstore.
  lazymatch goal with H : eval_lvalue _ _ ?temps _ imb_timer _ _ _ |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as HtimerM
      by (rewrite PTree.gso by discriminate; exact Hm);
    destruct (ice_field_location _ _ _ _ IMB._m IMB._MarioState IMB._actionTimer
      tushort mb mo 26 _ _ _ HtimerM
      (proj1 (imb_control_fields version)) H) as (-> & -> & ->) end.
  match goal with H : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion H; subst; clear H end.
  2: match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
  match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vint before) by (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst v end.
  match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
  match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
  lazymatch goal with H : Mem.storev _ ?memory (Vptr ?b ?ofs) _ = Some ?final |- _ =>
    change (Mem.store Mint16unsigned memory b (Ptrofs.unsigned ofs)
      (Vint (ilh_next_timer before)) = Some final) in H;
    split; [exact H|]; split;
    [unfold ilh_timer_load; rewrite (Mem.load_store_same _ _ _ _ _ _ H);
     change (Some (Vint (Int.zero_ext 16 (ilh_next_timer before))) = Some (Vint (ilh_next_timer before)));
     unfold ilh_next_timer; rewrite Int.zero_ext_idem by lia; reflexivity|]
  end.
  repeat split; reflexivity.
Qed.

Lemma ijc_early_test_value : forall ge e le m before answer,
  le ! IMB._t'2 = Some (Vint before) ->
  eval_expr ge e le m ijc_early_test answer ->
  answer = Val.of_bool (Int.lt before (Int.repr 6)).
Proof.
  intros ge e le m before answer Hbefore Hread. unfold ijc_early_test in Hread.
  inversion Hread; subst.
  - match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vint before) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
    lazymatch goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some answer |- _ =>
      change (Some (Val.of_bool (Int.lt before (Int.repr 6))) = Some answer) in H;
      inversion H; reflexivity end.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma ijc_early_entry_reaches_branch : forall version e le m mb mo before t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> ilh_timer_load m mb mo = Some (Vint before) ->
  Int.unsigned before < 6 ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ijc_enter version) t le' m' out ->
  exists after_increment,
    Mem.store Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26)))
      (Vint (ilh_next_timer before)) = Some after_increment /\
    ilh_timer_load after_increment mb mo = Some (Vint (ilh_next_timer before)) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IMB._t'2 (Vint before) le) after_increment (ijc_yes version) t le' m' out /\
    out = Out_normal.
Proof.
  intros version e le m mb mo before t le' m' out Hm Htimer Hsmall Hrun.
  destruct (ijc_entry_source version) as (_ & Hshape & _ & Hnormal & Hyes & _).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suf & Htrace & Hinc & Hbranch).
  destruct (ijc_increment_exact _ _ _ _ _ _ _ _ _ _ _ Hm Htimer Hinc)
    as (Hstore & Hload & -> & -> & _).
  cbn in Htrace. subst t.
  inversion Hbranch; subst.
  match goal with H : eval_expr ?ge ?env ?temps ?memory ijc_early_test ?v |- _ =>
    assert (v = Val.of_bool (Int.lt before (Int.repr 6))) by
      (eapply (ijc_early_test_value ge env temps memory before); [apply PTree.gss|exact H]); subst v end.
  rewrite (proj1 (ijc_early_values before Hsmall)) in *.
  match goal with H : bool_val _ _ _ = Some ?b |- _ =>
    change (Some true = Some b) in H; inversion H; subst b end.
  exists memory. split; [exact Hstore|]. split; [exact Hload|].
  split; [assumption|]. eapply ibk_normal_outcome; eauto.
Qed.

Lemma ijc_split_early_body : forall version e le m mb mo before t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) -> ilh_timer_load m mb mo = Some (Vint before) ->
  Int.unsigned before < 6 ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ijc_body version)) t le' m' out ->
  exists middle memory pre suf,
    t = pre ++ suf /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ijc_enter version) pre middle memory Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e middle memory
      (ijc_tail version) suf le' m' out.
Proof.
  intros version e le m mb mo before t le' m' out Hm Htimer Hsmall Hrun.
  rewrite (proj1 (ijc_entry_source version)) in Hrun.
  inversion Hrun; subst.
  - do 4 eexists. repeat split; eauto.
  - exfalso.
    match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (ijc_enter _) _ _ _ _ |- _ =>
      destruct (ijc_early_entry_reaches_branch _ _ _ _ _ _ _ _ _ _ _
        Hm Htimer Hsmall H) as (? & ? & ? & ? & Hnormal); contradiction end.
Qed.

(** Start at the actual function call, before the timer is incremented.
    The witness retains the helper and movement suffixes of that call. *)
Definition InkCompletedJumpClamp : Prop := forall version m mb mo depth before
    animation1 animation2 endAction airAction t m' result,
  imf_room mo ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  ilh_timer_load m mb mo = Some (Vint before) -> Int.unsigned before < 6 ->
  is_finite 24 128 (jp_b32_quicksand_jump_raw depth
    (Int.unsigned (ilh_next_timer before))) = true ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ijc_body version))
    [Vptr mb mo; animation1; animation2; endAction; airAction] t m' result ->
  exists e le after_increment cut_le cut_m after helper_le helper_m last_le last_m out helpers tail,
    function_entry2 (Clight.globalenv (selected_clight_target version))
      (ijc_body version) [Vptr mb mo; animation1; animation2; endAction; airAction] m e le m /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ijc_increment version) E0 (PTree.set IMB._t'2 (Vint before) le) after_increment Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IMB._t'2 (Vint before) le) after_increment
      (ijc_pair version) E0 cut_le cut_m Out_normal /\
    Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) /\
    JPBinary32SafeDepthWriterOutcome depth after /\ JPBinary32FiniteNonnegative after /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e cut_le cut_m
      (ijc_calls version) helpers helper_le helper_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e helper_le helper_m
      (ijc_tail version) tail last_le last_m out /\
    Mem.free_list last_m (blocks_of_env (Clight.globalenv (selected_clight_target version)) e) = Some m' /\
    outcome_result_value out (fn_return (ijc_body version)) result last_m /\
    t = helpers ++ tail.

Theorem ijc_completed_early_call_clamps_before_helpers : InkCompletedJumpClamp.
Proof.
  intros version m mb mo depth before animation1 animation2 endAction airAction t m' result
    Hroom Hd Htimer Hsmall Hfinite Hcall.
  destruct (ijc_entry_source version) as (_ & Henter & _ & HincNormal & _ & Hvars & Hparams).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    pose proof He as Hentry; inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as Hm by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss)
  end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (ijc_split_early_body _ _ _ _ _ _ _ _ _ _ _ Hm Htimer Hsmall Hrun)
      as (helper_le & helper_m & helpers & tail & Htrace & Hfirst & Htail)
  end.
  rewrite Henter in Hfirst.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HincNormal Hfirst)
    as (inc_le & inc_m & inc_t & branch_t & HfirstTrace & Hinc & Hchoice).
  destruct (ijc_increment_exact _ _ _ _ _ _ _ _ _ _ _ Hm Htimer Hinc)
    as (Hstore & HtimerNow & Htemps & Hempty & _).
  subst inc_le inc_t. cbn in HfirstTrace. subst helpers.
  assert (Mem.load Mfloat32 inc_m mb
    (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth)) as HdNow.
  { rewrite <- Hd. eapply Mem.load_store_other; [exact Hstore|]. right. right.
    rewrite !imf_address by (assumption || lia). cbn. lia. }
  inversion Hchoice; subst.
  match goal with H : eval_expr ?ge ?env ?temps ?memory ijc_early_test ?v |- _ =>
    assert (v = Val.of_bool (Int.lt before (Int.repr 6))) by
      (eapply (ijc_early_test_value ge env temps memory before); [apply PTree.gss|exact H]); subst v end.
  rewrite (proj1 (ijc_early_values before Hsmall)) in *.
  match goal with H : bool_val _ _ _ = Some ?b |- _ =>
    change (Some true = Some b) in H; inversion H; subst b end.
  cbn beta iota in *.
  lazymatch goal with Hyes : ClightBigstep.exec_stmt _ _ ?env ?temps ?memory
      (ijc_yes version) ?tr ?lastle ?lastm Out_normal |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as HbranchM
      by (rewrite PTree.gso by discriminate; exact Hm);
    destruct (ijc_taken_branch_clamps_before_helpers version env temps memory mb mo
      depth (ilh_next_timer before) tr lastle lastm Out_normal
      HbranchM HdNow HtimerNow
      (proj2 (ijc_early_values before Hsmall)) Hfinite Hyes)
      as (cut_le & cut_m & after & Hpair & Hload & Hsafe & Hnonnegative & Hcalls)
  end.
  do 13 eexists.
  repeat first [eassumption | split].
Qed.

Definition InkJumpClampBoundary : Prop :=
  InkJumpClampSafeWriter /\ InkJumpClampBeforeHelpers /\ InkCompletedJumpClamp.
Theorem ijc_jump_clamp_boundary_checked : InkJumpClampBoundary.
Proof.
  split; [exact ijc_actual_pair_enters_safe_writer_classification|].
  split; [exact ijc_taken_branch_clamps_before_helpers|exact ijc_completed_early_call_clamps_before_helpers].
Qed.
