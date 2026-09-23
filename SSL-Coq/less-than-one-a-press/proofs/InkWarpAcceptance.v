(** The selected accepted-warp checkpoint, before act_disappeared runs.
    Open the real US/JP action setter and its cutscene initializer. The
    accepted tail preserves positions; the earlier handler calls are NOT
    assigned an assumed frame. This is a local backward cut, not a proof
    that the useful pre-existing split is controller-reachable. *)
From Coq Require Import Bool List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_interaction jp_interaction.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank9AStarSource
  Area2SlideKickInitializer Area2Rank11LivePoleExit Area2Rank12BContact
  InkActionTimerReset InkLandingHistoryReturn InkBackwardSource
  InkBackwardExecution InkCopyCompletion InkRetryCompletion
  ObjectContactNecessity ObjectContactReadback ContactConsumerExecution SecretContactExecution
  OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IWA := us_mario.
Module IWAI := us_interaction.

Definition iwa_action := Vint (Int.repr 4864).
Definition iwa_argument := Vint (Int.repr 262146).

Lemma iwa_cutscene_body_source : forall version,
  fn_vars (rank9a_body version R9Initialize) = [] /\
  fn_params (rank9a_body version R9Initialize) =
    [(IWA._m, tptr (Tstruct IWA._MarioState noattr));
     (IWA._action, tuint); (IWA._actionArg, tuint)] /\
  fn_body (rank9a_body version R9Initialize) =
    Ssequence (Sswitch (Etempvar IWA._action tuint) (rank9a_initializer_cases version))
      (Sreturn (Some (Etempvar IWA._action tuint))) /\
  select_switch 4864 (rank9a_initializer_cases version) = LSnil.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma iwa_cutscene_switch_identity : forall version ge e le m t le' m' out,
  le ! IWA._action = Some iwa_action ->
  ocn_exec ge e le m
    (Sswitch (Etempvar IWA._action tuint) (rank9a_initializer_cases version))
    t le' m' out -> t = E0 /\ le' = le /\ m' = m /\ out = Out_normal.
Proof.
  intros version ge e le m t le' m' out Ha Hrun. inversion Hrun; subst.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IWA._action _) ?v |- _ =>
    assert (v = iwa_action) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : sem_switch_arg _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst end.
  replace (Int.unsigned (Int.repr 4864)) with 4864 in * by reflexivity.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
      (seq_of_labeled_statement (select_switch _ _)) _ _ _ _ |- _ =>
    rewrite (proj2 (proj2 (proj2 (iwa_cutscene_body_source version)))) in Hr;
    cbn [seq_of_labeled_statement] in Hr; inversion Hr; subst end.
  repeat split; reflexivity.
Qed.

Lemma iwa_cutscene_call_identity : forall version m mario arg t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (rank9a_body version R9Initialize))
    [Vptr mario Ptrofs.zero; iwa_action; arg] t m' result ->
  t = E0 /\ m' = m /\ result = iwa_action.
Proof.
  intros version m mario arg t m' result Hcall.
  destruct (iwa_cutscene_body_source version) as (Hvars & Hparams & Hsource & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IWA._action = Some iwa_action) as Ha by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb;
       rewrite PTree.gso by discriminate; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hsource in Hr; inversion Hr; subst; clear Hr end.
  all: match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Sswitch _ _) _ _ _ _ |- _ =>
    destruct (iwa_cutscene_switch_identity _ _ _ _ _ _ _ _ _ Ha Hr)
      as (-> & -> & -> & Hout); try contradiction end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn _) _ _ _ _ |- _ =>
    inversion Hr; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IWA._action _) ?v |- _ =>
    assert (v = iwa_action) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hresult : outcome_result_value _ _ _ _ |- _ =>
    assert (fn_return (rank9a_body version R9Initialize) = tuint) as Hreturn
      by (destruct version; reflexivity);
    rewrite Hreturn in Hresult;
    cbn in Hresult; destruct Hresult as [_ Hcast]; inversion Hcast; subst end.
  repeat split; reflexivity.
Qed.

Definition iwa_initializer_call := Scall (Some IWA._t'4)
  (Evar IWA._set_mario_action_cutscene ilh_set_action_type)
  [Etempvar IWA._m (tptr (Tstruct IWA._MarioState noattr));
   Etempvar IWA._action tuint; Etempvar IWA._actionArg tuint].

Lemma iwa_initializer_call_identity : forall version le m mario t le' m' out,
  le ! IWA._m = Some (Vptr mario Ptrofs.zero) ->
  le ! IWA._action = Some iwa_action ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    iwa_initializer_call t le' m' out ->
  t = E0 /\ m' = m /\ le' = PTree.set IWA._t'4 iwa_action le.
Proof.
  intros version le m mario t le' m' out Hm Ha Hrun.
  destruct (rank9a_selected_body_resolves version R9Initialize) as (fb & Hsymbol & Hfun).
  unfold iwa_initializer_call, ilh_set_action_type in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory IWA._set_mario_action_cutscene
        [tptr (Tstruct IWA._MarioState noattr); tuint; tuint] tuint cc_default fb v
        eq_refl Hsymbol Hr));
    subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hargs : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Hargs; subst; clear Hargs end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IWA._m _) ?v |- _ =>
    assert (v = Vptr mario Ptrofs.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IWA._action _) ?v |- _ =>
    assert (v = iwa_action) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast (Vptr _ _) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hcast : sem_cast iwa_action _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ _ |- _ =>
    destruct (iwa_cutscene_call_identity _ _ _ _ _ _ _ Hcall) as (-> & -> & ->) end.
  repeat split; reflexivity.
Qed.

Definition iwa_initializer_cases version := match iar_initializer version with
| Sswitch _ cases => cases | _ => LSnil end.
Lemma iwa_initializer_source : forall version,
  iar_initializer version = Sswitch
    (Ebinop Oand (Etempvar IWA._action tuint) (Econst_int (Int.repr 448) tint) tuint)
    (iwa_initializer_cases version) /\
  seq_of_labeled_statement (select_switch 256 (iwa_initializer_cases version)) =
    Ssequence (Ssequence (Ssequence iwa_initializer_call
      (Sset IWA._action (Etempvar IWA._t'4 tuint))) Sbreak) Sskip.
Proof. intros []; split; reflexivity. Qed.

Lemma iwa_initializer_identity : forall version le m mario t le' m' out,
  le ! IWA._m = Some (Vptr mario Ptrofs.zero) ->
  le ! IWA._action = Some iwa_action ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (iar_initializer version) t le' m' out -> m' = m.
Proof.
  intros version le m mario t le' m' out Hm Ha Hrun.
  rewrite (proj1 (iwa_initializer_source version)) in Hrun. inversion Hrun; subst.
  match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hr; subst; clear Hr end.
  2: match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IWA._action _) ?v |- _ =>
    assert (v = iwa_action) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  lazymatch goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some ?value |- _ =>
    change (Some (Vint (Int.repr 256)) = Some value) in Hsem;
    inversion Hsem; subst end.
  match goal with Hsem : sem_switch_arg _ _ = Some _ |- _ =>
    cbn in Hsem; inversion Hsem; subst end.
  replace (Int.unsigned (Int.repr 256)) with 256 in * by reflexivity.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
      (seq_of_labeled_statement (select_switch _ _)) _ _ _ _ |- _ =>
    rewrite (proj2 (iwa_initializer_source version)) in Hr end.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in *.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  all: match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ iwa_initializer_call _ _ _ _ |- _ =>
    destruct (iwa_initializer_call_identity _ _ _ _ _ _ _ _ Hm Ha Hr)
      as (-> & -> & ->); reflexivity end.
Qed.

Definition InkDisappearedSetterFrame : Prop :=
  forall version m mario arg t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ilh_set_action_body version))
    [Vptr mario Ptrofs.zero; iwa_action; arg] t m' result ->
  result = Vint Int.one /\
  forall chunk b offset, ski_after_control mario chunk b offset ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset.

Theorem iwa_disappeared_setter_preserves_positions : InkDisappearedSetterFrame.
Proof.
  intros version m mario arg t m' result Hcall.
  split; [eapply ilh_completed_set_action_call_returns_one; eauto|].
  destruct (iar_source_cuts version) as (Hvars & Hparams & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IWA._m = Some (Vptr mario Ptrofs.zero)) as Hm by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (temps ! IWA._action = Some iwa_action) as Ha by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb;
       rewrite PTree.gso by discriminate; apply PTree.gss) end.
  assert (Hsource : fn_body (ilh_set_action_body version) =
    Ssequence (iar_initializer version) (ski_setter_tail version))
    by (destruct version; reflexivity).
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hsource in Hr;
    destruct (iar_split_initializer _ _ _ _ _ _ _ _ _ _ Hr)
      as (middle & memory & pre & suf & Htrace & Hfirst & Htail) end.
  pose proof (iar_initializer_keeps_m _ _ _ _ _ _ _ _ _ Hfirst) as Hkeep.
  pose proof (iwa_initializer_identity _ _ _ _ _ _ _ _ Hm Ha Hfirst) as ->.
  exact (proj2 (ski_tail_statement_frames _ (ski_setter_tail_is_classified version)
    _ _ _ _ _ _ _ _ (eq_trans Hkeep Hm) Htail)).
Qed.

(** Extract the actual nonfading, non-pipe branch and its final call/return.
    Entry to this tail is AFTER segmented_to_virtual, play_sound and
    mario_stop_riding_object. Those earlier effects are not erased. *)
Definition iwa_handler version := match version with
| VersionUS => us_interaction.f_interact_warp
| VersionJP => jp_interaction.f_interact_warp end.
Definition iwa_success_branch version := match fn_body (iwa_handler version) with
| Ssequence (Ssequence _ (Sifthenelse _ _
    (Ssequence _ (Sifthenelse _ yes _)))) _ => yes
| _ => Sskip end.
Definition iwa_success_tail version := rank12b_drop_sequences 5 (iwa_success_branch version).
Definition iwa_arg_expr := Ebinop Oadd
  (Ebinop Oshl (Econst_int (Int.repr 4) tint) (Econst_int (Int.repr 16) tint) tint)
  (Econst_int (Int.repr 2) tint) tint.
Definition iwa_accept_call := Scall (Some IWAI._t'7)
  (Evar IWAI._set_mario_action ilh_set_action_type)
  [Etempvar IWAI._m (tptr (Tstruct IWAI._MarioState noattr));
   Econst_int (Int.repr 4864) tint; iwa_arg_expr].
Lemma iwa_tail_is_generated : forall version,
  fn_vars (iwa_handler version) = [] /\
  iwa_success_tail version = Ssequence iwa_accept_call
    (Sreturn (Some (Etempvar IWAI._t'7 tuint))).
Proof. intros []; split; reflexivity. Qed.

Lemma iwa_accept_call_frame : forall version le m mario t le' m' out,
  le ! IWAI._m = Some (Vptr mario Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    iwa_accept_call t le' m' out ->
  le' = PTree.set IWAI._t'7 (Vint Int.one) le /\
  forall chunk b offset, ski_after_control mario chunk b offset ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset.
Proof.
  intros version le m mario t le' m' out Hm Hrun.
  destruct (ilh_selected_set_action_resolves version) as (fb & Hsymbol & Hfun).
  unfold iwa_accept_call, ilh_set_action_type in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory IWAI._set_mario_action
        [tptr (Tstruct IWAI._MarioState noattr); tuint; tuint] tuint cc_default fb v
        eq_refl Hsymbol Hr)); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hargs : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Hargs; subst; clear Hargs end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IWAI._m _) ?v |- _ =>
    assert (v = Vptr mario Ptrofs.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  match goal with Hr : eval_expr _ _ _ _ iwa_arg_expr ?v |- _ =>
    assert (v = iwa_argument) by
      (eapply ocr_expr_unique; [exact Hr|]; unfold iwa_arg_expr;
       eapply eval_Ebinop;
       [eapply eval_Ebinop; [constructor|constructor|reflexivity]|constructor|reflexivity]);
    subst v end.
  match goal with Hcast : sem_cast (Vptr _ _) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hcast : sem_cast (Vint (Int.repr 4864)) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hcast : sem_cast iwa_argument _ _ _ = Some ?v |- _ =>
    change (Some iwa_argument = Some v) in Hcast; inversion Hcast; subst end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ _ |- _ =>
    destruct (iwa_disappeared_setter_preserves_positions _ _ _ _ _ _ _ Hcall)
      as (-> & Hframe) end.
  split; [reflexivity|exact Hframe].
Qed.

Definition InkAcceptedWarpTailFrame : Prop :=
  forall version le m mario t le' m' out,
  le ! IWAI._m = Some (Vptr mario Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (iwa_success_tail version) t le' m' out ->
  out = Out_return (Some (Vint Int.one, tuint)) /\
  forall chunk b offset, ski_after_control mario chunk b offset ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset.

Theorem iwa_accepted_warp_tail_keeps_positions : InkAcceptedWarpTailFrame.
Proof.
  intros version le m mario t le' m' out Hm Hrun.
  rewrite (proj2 (iwa_tail_is_generated version)) in Hrun.
  destruct (ibk_split_sequence _ _ _ _ iwa_accept_call _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hcall & Hreturn).
  destruct (iwa_accept_call_frame _ _ _ _ _ _ _ _ Hm Hcall) as (-> & Hframe).
  inversion Hreturn; subst.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IWAI._t'7 _) ?v |- _ =>
    assert (v = Vint Int.one) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]);
    subst v end.
  split; [reflexivity|exact Hframe].
Qed.

(** The nine position cells use the selected layouts checked by Ink's copy
    and platform proofs. Separate MarioState and Object-pool blocks suffice;
    no position value, controller history or helpful gap is assumed. *)
Definition iwa_state_position m mario :=
  map (fun offset => Mem.load Mfloat32 m mario offset) [60; 64; 68].
Definition iwa_object_position m object base (display : bool) :=
  map (fun offset => Mem.load Mfloat32 m object (base + offset))
    (if display then [32; 36; 40] else [160; 164; 168]).
Definition iwa_split m mario object base :=
  iwa_state_position m mario <> iwa_object_position m object base false \/
  iwa_state_position m mario <> iwa_object_position m object base true.

Definition InkAcceptedWarpSplitBackward : Prop :=
  forall version le m mario object base t le' m' out,
  mario <> object ->
  le ! IWAI._m = Some (Vptr mario Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (iwa_success_tail version) t le' m' out ->
  (iwa_split m' mario object base <-> iwa_split m mario object base).

Theorem iwa_acceptance_tail_neither_creates_nor_erases_split : InkAcceptedWarpSplitBackward.
Proof.
  intros version le m mario object base t le' m' out Hseparate Hm Hrun.
  destruct (iwa_accepted_warp_tail_keeps_positions _ _ _ _ _ _ _ _ Hm Hrun)
    as [_ Hframe].
  assert (Hstate : iwa_state_position m' mario = iwa_state_position m mario).
  { unfold iwa_state_position. apply map_ext_in. intros offset Hin.
    apply Hframe. unfold ski_after_control. right; right.
    cbn in Hin. intuition lia. }
  assert (Hobject : forall display,
    iwa_object_position m' object base display = iwa_object_position m object base display).
  { intro display. unfold iwa_object_position. apply map_ext. intro offset.
    apply Hframe. unfold ski_after_control. left; congruence. }
  unfold iwa_split. rewrite Hstate, !Hobject. reflexivity.
Qed.

Definition InkWarpAcceptanceBoundary : Prop :=
  InkDisappearedSetterFrame /\ InkAcceptedWarpTailFrame /\ InkAcceptedWarpSplitBackward.
Theorem iwa_warp_acceptance_boundary_checked : InkWarpAcceptanceBoundary.
Proof.
  split; [exact iwa_disappeared_setter_preserves_positions|].
  split; [exact iwa_accepted_warp_tail_keeps_positions|].
  exact iwa_acceptance_tail_neither_creates_nor_erases_split.
Qed.
