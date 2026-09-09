(** One actual input-preparation execution: reset, metadata, the selected
    button callee, then the real remaining joystick/geometry continuation.
    The later continuation is retained, not silently declared harmless. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackward
  InkControllerSource InkControllerEdge InkMarioInputFlag InkMarioInputReset
  InkBackwardSource InkBackwardExecution InkFloorResetExecution
  ObjectContactNecessity ContactConsumerExecution SecretContactExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma icb_actual_button_call_no_a :
  forall version m mb mo cb co pressed t m' result,
  imf_room mo -> imf_input_load m mb mo = Some (Vint Int.zero) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 156))) = Some (Vptr cb co) ->
  Mem.load Mint16unsigned m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))) = Some (Vint pressed) ->
  Int.testbit pressed 15 = false ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Ctypes.Internal (ics_body version ICButtons)) [Vptr mb mo] t m' result ->
  exists flags, imf_input_load m' mb mo = Some (Vint flags) /\
    Int.and flags (Int.repr 2) = Int.zero /\ t = E0.
Proof.
  intros version m mb mo cb co pressed t m' result Hroom Hzero Hcontroller Hpressed Hclear Hcall.
  assert (fn_vars (ics_body version ICButtons) = []) as Hvars by (destruct version; reflexivity).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ => inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IBM._m = Some (Vptr mb mo)) as Hm
      by (destruct version; cbn in Hbind; inversion Hbind; reflexivity) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ ?env ?temps ?memory _ ?tr ?final_le ?final_m ?out |- _ =>
    destruct (imf_complete_button_body_no_new_a version env temps memory mb mo cb co pressed Int.zero
      tr final_le final_m out Hroom Hm Hcontroller Hpressed Hclear Hzero Hr)
      as (flags & Hflags & Hbit & Htrace & _) end.
  exists flags. split; [exact Hflags|]. split; [|exact Htrace].
  apply (imf_single_bit_mask_clear flags 1); [lia|]. rewrite Hbit. apply Int.bits_zero.
Qed.

Lemma icb_call_resolves_selected_buttons : forall version e le m mb mo t le' m' out,
  e ! IBM._update_mario_button_inputs = None -> le ! IBM._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (imr_button_call version) t le' m' out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Ctypes.Internal (ics_body version ICButtons)) [Vptr mb mo] t m' result.
Proof.
  intros version e le m mb mo t le' m' out Hlocal Hm Hrun.
  destruct (imr_source version) as (_ & Hcall & _). rewrite Hcall in Hrun.
  destruct (ics_selected_bodies_resolve version ICButtons) as (b & Hsymbol & Hfunction).
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hr : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Hr; subst; clear Hr end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  eauto.
Qed.

Definition InkContinuousInputPreparationCut : Prop :=
  forall version e le m mb mo t le' m' out,
  e ! IBM._update_mario_button_inputs = None -> imf_room mo -> le ! IBM._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ics_body version ICInputs)) t le' m' out ->
  exists button_m ready_le ready_m pre call_trace suf result,
    t = pre ++ (call_trace ++ suf) /\
    imf_input_load button_m mb mo = Some (Vint Int.zero) /\
    ready_le ! IBM._m = Some (Vptr mb mo) /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) button_m
      (Ctypes.Internal (ics_body version ICButtons)) [Vptr mb mo] call_trace ready_m result /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e ready_le ready_m
      (imr_after_buttons version) suf le' m' out /\
    (forall cb co pressed,
      Mem.load Mint32 button_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 156))) = Some (Vptr cb co) ->
      Mem.load Mint16unsigned button_m cb (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr 18))) = Some (Vint pressed) ->
      Int.testbit pressed 15 = false ->
      exists flags, imf_input_load ready_m mb mo = Some (Vint flags) /\
        Int.and flags (Int.repr 2) = Int.zero /\ call_trace = E0).

Theorem icb_actual_reset_and_buttons_share_one_execution : InkContinuousInputPreparationCut.
Proof.
  unfold InkContinuousInputPreparationCut.
  intros version e le m mb mo t le' m' out Hlocal Hroom Hm Hrun.
  destruct (imr_actual_input_body_reaches_buttons_with_zero_input _ _ _ _ _ _ _ _ _ _ Hroom Hm Hrun)
    as (button_le & button_m & pre & rest & Htrace & HbuttonM & Hzero & Hrest).
  assert (ibk_normal (imr_button_call version) = true) as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (ready_le & ready_m & call_trace & suf & Htrace2 & Hcall & Hsuffix).
  destruct (icb_call_resolves_selected_buttons _ _ _ _ _ _ _ _ _ _ Hlocal HbuttonM Hcall)
    as (result & Hselected).
  assert (ifr_keeps_temp IBM._m (imr_button_call version) = true) as Hkeeps by (destruct version; reflexivity).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hcall Hkeeps) as HsameM.
  exists button_m, ready_le, ready_m, pre, call_trace, suf, result.
  split; [rewrite Htrace, Htrace2; reflexivity|].
  split; [exact Hzero|]. split; [congruence|].
  split; [exact Hselected|]. split; [exact Hsuffix|].
  intros cb co pressed Hcontroller Hpressed Hclear.
  eapply icb_actual_button_call_no_a; eauto.
Qed.

Definition InkControllerCheckedBoundary : Prop :=
  InkMovingCheckedBoundary /\
  (forall version kind, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ics_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Ctypes.Internal (ics_body version kind))) /\
  InkControllerEdgeCut /\ InkMarioButtonNoEdgeCut /\ InkInputResetToButtonCut /\
  InkContinuousInputPreparationCut.

Theorem icb_controller_backward_checked : InkControllerCheckedBoundary.
Proof.
  split; [exact imb_moving_backward_checked|].
  split; [exact ics_selected_bodies_resolve|].
  split; [exact ice_actual_pressed_bit_is_sample_edge|].
  split; [exact imf_complete_button_body_no_new_a|].
  split; [exact imr_actual_input_body_reaches_buttons_with_zero_input|].
  exact icb_actual_reset_and_buttons_share_one_execution.
Qed.
