(** Complete cancellation calls: real rejection returns and the live duration read. *)
From Coq Require Import Bool List Lia ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts ActionDepthAliasCensus
  ZeroAQuicksandEntryBoundary InkLandingHistorySource InkLandingHistory
  InkLandingHistoryReturn InkMovingBackwardSource InkBackwardSource
  InkBackwardExecution InkFloorResetExecution ObjectContactNecessity
  ContactConsumerExecution SecretContactExecution
  Area2Rank12BContact UpperElevatorQueryResolution ContactConsumerSource
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

From LessThanOneAPress.Proofs Require Import InkLandingCallerSource.

From LessThanOneAPress.Generated Require Import us_mario jp_mario us_mario_step jp_mario_step.
From LessThanOneAPress.Proofs Require Import InkLandingCallerGate InkLandingHistoryGate.
Local Open Scope Z_scope.

From LessThanOneAPress.Proofs Require Import InkLandingCancellationSource.

Theorem icz_completed_helper_returns_one : forall version kind m args t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (icz_body version kind)) args t m' result -> result = Vint Int.one.
Proof.
  intros version kind m args t m' result Hcall.
  assert (fn_vars (icz_body version kind) = []) as Hvars by (destruct version, kind; reflexivity).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct version, kind; cbv [icz_body fn_body us_mario_step.f_mario_push_off_steep_floor jp_mario_step.f_mario_push_off_steep_floor us_mario.f_set_jumping_action jp_mario.f_set_jumping_action us_mario_actions_moving.f_set_triple_jump_action jp_mario_actions_moving.f_set_triple_jump_action] in Hbody;
    cce_unroll_loop_free_exec end.
  all: repeat match goal with
  | H : ClightBigstep.exec_stmt _ (Clight.globalenv (selected_clight_target ?ver))
      empty_env ?temps ?memory (Scall (Some ?id) (Evar ?callee ?ty) ?values)
      ?tr ?next_le ?next_m ?out |- _ =>
      let Hsame := constr:(eq_refl : callee = IMB._set_mario_action) in
      destruct (ilh_actual_set_action_statement_returns_one ver empty_env temps memory id values
        tr next_le next_m out eq_refl H) as [Htemps Hout]; subst; clear H
  end.
  all: try solve [match goal with Hbad : ?out <> Out_normal,
    Hr : ClightBigstep.exec_stmt _ _ _ _ _ ?stmt _ _ _ ?out |- _ =>
    exfalso; apply Hbad; eapply (ibk_normal_outcome _ _ _ _ stmt); [reflexivity|exact Hr] end].
  all: repeat match goal with
  | H : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ (Out_return _) |- _ => inversion H
  | H : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ (Out_return _) |- _ => inversion H
  | H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst
  | H : eval_expr _ _ (PTree.set ?id (Vint Int.one) _) _ (Etempvar ?id _) ?v |- _ =>
      assert (v = Vint Int.one) by (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst v; clear H
  end.
  all: try solve [match goal with H : outcome_result_value _ _ _ _ |- _ =>
    cbn [icz_body fn_return us_mario_step.f_mario_push_off_steep_floor jp_mario_step.f_mario_push_off_steep_floor us_mario.f_set_jumping_action jp_mario.f_set_jumping_action us_mario_actions_moving.f_set_triple_jump_action jp_mario_actions_moving.f_set_triple_jump_action outcome_result_value] in H;
    try contradiction; destruct H as [_ Hcast]; cbn in Hcast; inversion Hcast; reflexivity end].
Qed.
