(** A preserved rollout action selects the real rollout callback, and a
    completed rollout callback returns false. The ending's memory frame is
    proved in Area2RolloutActionGate. Scheduling a later dispatch with that
    memory, and every earlier interaction or support change, remain separate. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area2RolloutSource
  Area2RolloutActionGate InkGroundCallBackward InkActionPassStart InkCopyCaller
  InkBackwardExecution InkControllerEdge ObjectContactNecessity ContactConsumerExecution
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

(** This class only constrains a function's return value. Stores and calls
    retain all actual effects; their preservation is not a premise. *)
Inductive rgr_returns_zero : statement -> Prop :=
| rgr_nonreturn : forall s, igb_no_return s = true -> rgr_returns_zero s
| rgr_return : rgr_returns_zero (Sreturn (Some (Econst_int Int.zero tint)))
| rgr_sequence : forall first rest, rgr_returns_zero first -> rgr_returns_zero rest ->
    rgr_returns_zero (Ssequence first rest)
| rgr_switch : forall expr cases,
    (forall n, rgr_returns_zero (seq_of_labeled_statement (select_switch n cases))) ->
    rgr_returns_zero (Sswitch expr cases).
Lemma rgr_returns_zero_sound : forall s, rgr_returns_zero s ->
  forall ge e le m t last after value ty,
  ocn_exec ge e le m s t last after (Out_return (Some (value, ty))) ->
  value = Vint Int.zero /\ ty = tint.
Proof.
  intros s Hshape. induction Hshape; intros ge e le m t last after value ty Hrun.
  - pose proof (igb_no_return_outcome _ _ _ _ _ _ _ _ _ Hrun H) as Hbad.
    exact (False_ind _ Hbad).
  - inversion Hrun; subst.
    match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in H; subst end. split; reflexivity.
  - inversion Hrun; subst; [eapply IHHshape2|eapply IHHshape1]; eauto.
  - inversion Hrun; subst.
    match goal with Hout : outcome_switch ?out = Out_return _ |- _ =>
      destruct out; cbn in Hout; try discriminate; inversion Hout; subst end.
    eauto.
Qed.
Lemma rgr_generated_rollouts_return_zero : forall version direction,
  rgr_returns_zero (fn_body (rag_body version (RGRollout direction))).
Proof.
  intros [] []; cbn [rag_body fn_body].
  all: repeat first [apply rgr_return | apply rgr_nonreturn; reflexivity
    |apply rgr_sequence | apply rgr_switch; intro selector; apply rgr_nonreturn;
      cbv [select_switch select_switch_case select_switch_default
        seq_of_labeled_statement igb_no_return];
      repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      reflexivity].
Qed.
Theorem rgr_completed_rollout_returns_false : forall version direction m args t after result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (rag_body version (RGRollout direction))) args t after result ->
  result = Vint Int.zero.
Proof.
  intros version direction m args t after result Hcall. inversion Hcall; subst.
  match goal with Hresult : outcome_result_value ?out _ _ _ |- _ =>
    assert (fn_return (rag_body version (RGRollout direction)) = tint) as Hreturn
      by (destruct version, direction; reflexivity);
    rewrite Hreturn in Hresult; destruct out; cbn in Hresult; try contradiction;
    match goal with o : option (val * type) |- _ =>
      destruct o as [[value ty]|]; cbn in Hresult; try contradiction end
  end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (rgr_returns_zero_sound _ (rgr_generated_rollouts_return_zero version direction)
      _ _ _ _ _ _ _ _ _ Hbody) as [-> ->] end.
  match goal with H : _ /\ sem_cast _ _ _ _ = Some _ |- _ =>
    destruct H as [_ Hcast]; cbn in Hcast; inversion Hcast; reflexivity end.
Qed.

Definition rgr_case_temp direction := match direction with
| RolloutForward => RGA._t'27 | RolloutBackward => RGA._t'33 end.
Definition rgr_callback direction := Scall (Some (rgr_case_temp direction))
  (Evar (rag_ident (RGRollout direction))
    (Tfunction [tptr (Tstruct RGA._MarioState noattr)] tint cc_default))
  [Etempvar RGA._m (tptr (Tstruct RGA._MarioState noattr))].
Definition rgr_case direction := Ssequence
  (Ssequence (rgr_callback direction)
    (Sset RGA._cancel (Etempvar (rgr_case_temp direction) tint))) Sbreak.
Lemma rgr_selected_case : forall version direction,
  exists rest, seq_of_labeled_statement
    (select_switch (rag_action_code direction) (rag_cases version)) =
    Ssequence (rgr_case direction) rest.
Proof. intros [] []; eexists; reflexivity. Qed.

Theorem rgr_stored_action_dispatches_real_rollout :
  forall version direction le m mb k,
  le ! RGA._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 12 = Some (Vint (Int.repr (rag_action_code direction))) ->
  exists call_cont,
  @Smallstep.star _ _ Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (rag_body version RGDispatch) (rag_dispatch version) k empty_env le m) E0
    (Callstate (Internal (rag_body version (RGRollout direction)))
      [Vptr mb Ptrofs.zero] call_cont m).
Proof.
  intros version direction le m mb k Hm Haction.
  destruct (rag_source version direction) as (_ & _ & _ & Hdispatch).
  destruct (rgr_selected_case version direction) as [rest Hcase].
  destruct (rag_selected_bodies_resolve version (RGRollout direction))
    as (fb & Hsymbol & Hfunction).
  eexists. rewrite Hdispatch.
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left.
  - apply step_set. eapply ias_field_read with (chunk := Mint32) (offset := 12);
      [exact (proj2 (rag_layout version))|reflexivity|exact Hm|exact Haction].
  - eapply star_left; [apply step_skip_seq| |reflexivity].
    eapply star_left.
    + eapply step_switch with (v := Vint (Int.repr (rag_action_code direction)))
        (n := rag_action_code direction).
      * apply eval_Etempvar. apply PTree.gss.
      * destruct direction; reflexivity.
    + rewrite Hcase. eapply star_left; [apply step_seq| |reflexivity].
      unfold rgr_case. eapply star_left; [apply step_seq| |reflexivity].
      eapply star_left; [apply step_seq| |reflexivity].
      unfold rgr_callback. eapply star_left.
      * eapply step_call with (vf := Vptr fb Ptrofs.zero)
          (vargs := [Vptr mb Ptrofs.zero])
          (fd := Internal (rag_body version (RGRollout direction))).
        -- reflexivity.
        -- eapply eval_Elvalue.
           ++ apply eval_Evar_global; [reflexivity|exact Hsymbol].
           ++ apply deref_loc_reference. reflexivity.
        -- econstructor.
           ++ apply eval_Etempvar. rewrite PTree.gso by discriminate. exact Hm.
           ++ reflexivity.
           ++ constructor.
        -- exact Hfunction.
        -- destruct version, direction; reflexivity.
      * apply star_refl.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(** This is the missing local connection: run the real ending, then use
    exactly its output memory for the real action read and call dispatch.
    It does not assert that the next scheduled frame preserves that memory. *)
Definition RolloutFinishDispatchGate : Prop :=
  forall version direction le m mb t last after out dispatch_le k,
  le ! RGA._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 12 = Some (Vint (Int.repr (rag_action_code direction))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (rag_finish version direction) t last after out ->
  dispatch_le ! RGA._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 after mb 12 = Some (Vint (Int.repr (rag_action_code direction))) /\
  out = Out_return (Some (Vint Int.zero, tint)) /\
  exists call_cont,
  @Smallstep.star _ _ Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (rag_body version RGDispatch) (rag_dispatch version) k empty_env dispatch_le after) E0
    (Callstate (Internal (rag_body version (RGRollout direction)))
      [Vptr mb Ptrofs.zero] call_cont after).
Theorem rgr_animation_finish_cannot_supply_ground_pound : RolloutFinishDispatchGate.
Proof.
  unfold RolloutFinishDispatchGate.
  intros version direction le m mb t last after out dispatch_le k Hm Haction Hrun Hdispatch.
  destruct (rag_rollout_finish_preserves_action_and_position
    version direction le m mb t last after out Hm Hrun) as (_ & Hout & Htemp & Hframe).
  assert (Mem.load Mint32 after mb 12 = Some (Vint (Int.repr (rag_action_code direction))))
    as Hretained.
  { rewrite Hframe; [exact Haction|right; left; cbn; lia]. }
  split; [exact Hretained|]. split; [exact Hout|].
  eapply rgr_stored_action_dispatches_real_rollout; [exact Hdispatch|exact Hretained].
Qed.

(** Necessity as well as a constructed dispatch: every successful read of
    the actual selector in the ending's memory still reads the rollout code. *)
Definition RolloutFinishReadExclusion : Prop :=
  forall version direction le m mb t last after out dispatch_le value,
  le ! RGA._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 12 = Some (Vint (Int.repr (rag_action_code direction))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (rag_finish version direction) t last after out ->
  dispatch_le ! RGA._m = Some (Vptr mb Ptrofs.zero) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) empty_env dispatch_le after
    rag_action value ->
  value = Vint (Int.repr (rag_action_code direction)) /\
  value <> Vint (Int.repr 16779404) /\ value <> Vint (Int.repr 8390825).
Theorem rgr_finished_rollout_cannot_read_freefall_or_ground_pound : RolloutFinishReadExclusion.
Proof.
  unfold RolloutFinishReadExclusion.
  intros version direction le m mb t last after out dispatch_le value Hm Haction Hrun Hd Hr.
  destruct (rag_rollout_finish_preserves_action_and_position
    version direction le m mb t last after out Hm Hrun) as (_ & _ & _ & Hframe).
  assert (Mem.load Mint32 after mb 12 = Some (Vint (Int.repr (rag_action_code direction))))
    as Hretained by (rewrite Hframe; [exact Haction|right; left; cbn; lia]).
  assert (value = Vint (Int.repr (rag_action_code direction))) as Hvalue.
  { eapply ice_field_read with (delta := 12) (chunk := Mint32) (ty := tuint);
      [exact Hd|exact (proj2 (rag_layout version))|reflexivity|exact Hretained|exact Hr]. }
  split; [exact Hvalue|]. rewrite Hvalue. destruct direction; split; discriminate.
Qed.

Definition RolloutExcludedDispatchCases : Prop := forall version,
  exists freefall_tail ground_pound_tail,
  seq_of_labeled_statement (select_switch 16779404 (rag_cases version)) =
    Ssequence
      (Ssequence (Ssequence
        (Scall (Some RGA._t'4) (Evar RGA._act_freefall
          (Tfunction [tptr (Tstruct RGA._MarioState noattr)] tint cc_default))
          [Etempvar RGA._m (tptr (Tstruct RGA._MarioState noattr))])
        (Sset RGA._cancel (Etempvar RGA._t'4 tint))) Sbreak) freefall_tail /\
  seq_of_labeled_statement (select_switch 8390825 (rag_cases version)) =
    Ssequence
      (Ssequence (Ssequence
        (Scall (Some RGA._t'36) (Evar RGA._act_ground_pound
          (Tfunction [tptr (Tstruct RGA._MarioState noattr)] tint cc_default))
          [Etempvar RGA._m (tptr (Tstruct RGA._MarioState noattr))])
        (Sset RGA._cancel (Etempvar RGA._t'36 tint))) Sbreak) ground_pound_tail.
Theorem rgr_excluded_codes_are_real_dispatch_cases : RolloutExcludedDispatchCases.
Proof. intros []; do 2 eexists; split; reflexivity. Qed.

Definition RolloutActionGateBoundary : Prop := RolloutFinishDispatchGate /\
  RolloutFinishReadExclusion /\ RolloutExcludedDispatchCases /\
  (forall version direction m args t after result,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (rag_body version (RGRollout direction))) args t after result ->
    result = Vint Int.zero).
Theorem rgr_rollout_action_gate_checked : RolloutActionGateBoundary.
Proof.
  split; [exact rgr_animation_finish_cannot_supply_ground_pound|].
  split; [exact rgr_finished_rollout_cannot_read_freefall_or_ground_pound|].
  split; [exact rgr_excluded_codes_are_real_dispatch_cases|
    exact rgr_completed_rollout_returns_false].
Qed.
