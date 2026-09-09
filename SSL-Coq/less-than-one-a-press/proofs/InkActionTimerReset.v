(** A completed real action-setting call ends with timer zero, regardless of
    the earlier initializer's memory effects.  No outside-call frame is used. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkLandingHistoryReturn
  InkLandingHistoryGate InkLandingExecution InkMovingBackwardSource
  InkBackwardSource InkBackwardExecution InkFloorResetExecution
  InkControllerEdge ObjectContactNecessity ContactConsumerExecution
  Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

(** This classifier concerns only the enclosing statement's outcome. Calls
    retain every real effect. It is instantiated with the finite switch below. *)
Fixpoint iar_normal_or_break (s : statement) : bool := match s with
| Sskip | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbreak => true
| Ssequence a b | Sifthenelse _ a b =>
    iar_normal_or_break a && iar_normal_or_break b
| _ => false end.

Lemma iar_normal_or_break_sound : forall ge e le m s t le' m' out,
  ocn_exec ge e le m s t le' m' out -> iar_normal_or_break s = true ->
  out = Out_normal \/ out = Out_break.
Proof.
  intros ge e le m s t le' m' out Hrun.
  induction Hrun; cbn; intro Hshape; try discriminate; try (left; reflexivity);
    try (right; reflexivity).
  - apply andb_true_iff in Hshape as [Ha Hb]. exact (IHHrun2 Hb).
  - apply andb_true_iff in Hshape as [Ha Hb]. exact (IHHrun Ha).
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b;
      [exact (IHHrun Ha)|exact (IHHrun Hb)].
Qed.

Lemma iar_switch_normal : forall ge e le m expr cases t le' m' out,
  (forall n, iar_normal_or_break
    (seq_of_labeled_statement (select_switch n cases)) = true) ->
  ocn_exec ge e le m (Sswitch expr cases) t le' m' out -> out = Out_normal.
Proof.
  intros ge e le m expr cases t le' m' out Hshape Hrun. inversion Hrun; subst.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
    (seq_of_labeled_statement (select_switch ?n cases)) _ _ _ _ |- _ =>
    destruct (iar_normal_or_break_sound _ _ _ _ _ _ _ _ _ Hr (Hshape n)) as [-> | ->]
  end; reflexivity.
Qed.

Lemma iar_switch_keeps_temp : forall ge e le m expr cases t le' m' out keep,
  (forall n, cce_keeps_temp keep
    (seq_of_labeled_statement (select_switch n cases)) = true) ->
  ocn_exec ge e le m (Sswitch expr cases) t le' m' out ->
  le' ! keep = le ! keep.
Proof.
  intros ge e le m expr cases t le' m' out keep Hshape Hrun.
  inversion Hrun; subst.
  eapply cce_argument_temporary_is_preserved; eauto.
Qed.

Definition iar_initializer version := ibk_head (fn_body (ilh_set_action_body version)).
Definition iar_before_reset version := ocn_prefix_items 6
  (rank12b_drop_sequences 1 (fn_body (ilh_set_action_body version))).
Definition iar_reset_tail version := rank12b_drop_sequences 7
  (fn_body (ilh_set_action_body version)).
Definition iar_zero_timer := Sassign imb_timer (Econst_int Int.zero tint).

Theorem iar_source_cuts : forall version,
  fn_vars (ilh_set_action_body version) = [] /\
  fn_params (ilh_set_action_body version) =
    [(IMB._m, tptr (Tstruct IMB._MarioState noattr));
     (IMB._action, tuint); (IMB._actionArg, tuint)] /\
  fn_body (ilh_set_action_body version) = Ssequence (iar_initializer version)
    (ocn_prepend (iar_before_reset version) (iar_reset_tail version)) /\
  forallb ibk_normal (iar_before_reset version) = true /\
  ifr_keeps_temp IMB._m (ocn_prepend (iar_before_reset version) Sskip) = true /\
  iar_reset_tail version = Ssequence iar_zero_timer
    (Sreturn (Some (Econst_int Int.one tint))).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma iar_initializer_finishes_normally : forall version ge e le m t le' m' out,
  ocn_exec ge e le m (iar_initializer version) t le' m' out -> out = Out_normal.
Proof.
  intros version ge e le m t le' m' out Hrun.
  destruct version; cbn [iar_initializer ilh_set_action_body ibk_head fn_body] in Hrun.
  all: eapply iar_switch_normal; [|exact Hrun].
  all: intro selector;
    cbv [select_switch select_switch_case select_switch_default
      seq_of_labeled_statement iar_normal_or_break];
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    reflexivity.
Qed.

Lemma iar_initializer_keeps_m : forall version ge e le m t le' m' out,
  ocn_exec ge e le m (iar_initializer version) t le' m' out ->
  le' ! IMB._m = le ! IMB._m.
Proof.
  intros version ge e le m t le' m' out Hrun.
  destruct version; cbn [iar_initializer ilh_set_action_body ibk_head fn_body] in Hrun.
  all: eapply iar_switch_keeps_temp; [|exact Hrun].
  all: intro selector;
    cbv [select_switch select_switch_case select_switch_default
      seq_of_labeled_statement cce_keeps_temp];
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    reflexivity.
Qed.

Lemma iar_split_initializer : forall version ge e le m rest t le' m' out,
  ocn_exec ge e le m (Ssequence (iar_initializer version) rest) t le' m' out ->
  exists middle memory pre suffix, t = pre ++ suffix /\
    ocn_exec ge e le m (iar_initializer version) pre middle memory Out_normal /\
    ocn_exec ge e middle memory rest suffix le' m' out.
Proof.
  intros version ge e le m rest t le' m' out Hrun. inversion Hrun; subst.
  - eauto 8.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
      (iar_initializer version) _ _ _ _ |- _ =>
      pose proof (iar_initializer_finishes_normally _ _ _ _ _ _ _ _ _ Hr)
    end. contradiction.
Qed.

Lemma iar_zero_timer_store : forall version e le m mb mo t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    iar_zero_timer t le' m' out ->
  Mem.store Mint16unsigned m mb
    (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26))) (Vint Int.zero) = Some m' /\
  t = E0 /\ le' = le /\ out = Out_normal.
Proof.
  intros version e le m mb mo t le' m' out Hm Hrun.
  unfold iar_zero_timer in Hrun. inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue ?ge ?env ?temps ?memory _ _ _ _ |- _ =>
    destruct (ice_field_location ge env temps memory
      IMB._m IMB._MarioState IMB._actionTimer tushort mb mo 26 _ _ _
      Hm (proj1 (imb_control_fields version)) Hl) as (-> & -> & ->)
  end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  repeat split; assumption || reflexivity.
Qed.

Lemma iar_reset_tail_leaves_zero : forall version e le m mb mo t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iar_reset_tail version) t le' m' out ->
  ilh_timer_load m' mb mo = Some (Vint Int.zero) /\
  out = Out_return (Some (Vint Int.one, tint)).
Proof.
  intros version e le m mb mo t le' m' out Hm Hrun.
  destruct (iar_source_cuts version) as (_ & _ & _ & _ & _ & Htail).
  rewrite Htail in Hrun.
  destruct (ibk_split_sequence _ _ _ _ iar_zero_timer _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hstore & Hreturn).
  destruct (iar_zero_timer_store _ _ _ _ _ _ _ _ _ _ Hm Hstore)
    as (Hwritten & _ & -> & _).
  inversion Hreturn; subst.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  split; [unfold ilh_timer_load; rewrite (Mem.load_store_same _ _ _ _ _ _ Hwritten)|];
    reflexivity.
Qed.

Definition InkCompletedActionTimerReset : Prop :=
  forall version m mb mo action arg t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ilh_set_action_body version)) [Vptr mb mo; action; arg] t m' result ->
  ilh_timer_load m' mb mo = Some (Vint Int.zero) /\ result = Vint Int.one.

Theorem iar_completed_set_action_resets_original_timer : InkCompletedActionTimerReset.
Proof.
  unfold InkCompletedActionTimerReset.
  intros version m mb mo action arg t m' result Hcall.
  pose proof (ilh_completed_set_action_call_returns_one _ _ _ _ _ _ Hcall) as Hresult.
  split; [|exact Hresult].
  destruct (iar_source_cuts version)
    as (Hvars & Hparams & Hbody & Hnormal & HkeepRest & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as Hm by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss)
  end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (iar_split_initializer _ _ _ _ _ _ _ _ _ _ Hr)
      as (first_le & first_m & first_t & rest_t & Htrace & Hfirst & Hrest)
  end.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (reset_le & reset_m & pre & suf & HrestTrace & Hprefix & Htail).
  pose proof (iar_initializer_keeps_m _ _ _ _ _ _ _ _ _ Hfirst) as HfirstM.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepRest) as HresetM.
  assert (reset_le ! IMB._m = Some (Vptr mb mo)) as HresetArgument
    by (rewrite HresetM, HfirstM; exact Hm).
  exact (proj1 (iar_reset_tail_leaves_zero version empty_env reset_le reset_m mb mo
    _ _ _ _ HresetArgument Htail)).
Qed.
