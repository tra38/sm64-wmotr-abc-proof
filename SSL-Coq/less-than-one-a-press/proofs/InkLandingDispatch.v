(** The landing routine's actual left-ground dispatch calls the actual action
    setter on its original Mario argument and receives the checked timer reset. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkActionTimerReset
  InkLandingContinuationSource InkLandingHistoryReturn InkLandingHistoryGate
  InkMovingBackwardSource InkBackwardSource InkBackwardExecution
  InkFloorResetExecution ObjectContactNecessity ContactConsumerExecution
  SecretContactExecution Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Lemma ilc_dispatch_normal : forall version ge e le m t le' m' out,
  ocn_exec ge e le m (ilc_dispatch version) t le' m' out -> out = Out_normal.
Proof.
  intros version ge e le m t le' m' out Hrun.
  destruct (ilc_source_cuts version) as (_ & _ & _ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. eapply iar_switch_normal; [|exact Hrun].
  intros selector. destruct version;
    cbv [ilc_cases ilc_dispatch ilc_after_ground imb_body ibk_head
      rank12b_drop_sequences fn_body IMB.f_common_landing_action
      jp_mario_actions_moving.f_common_landing_action
      select_switch select_switch_case select_switch_default
      seq_of_labeled_statement iar_normal_or_break];
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    reflexivity.
Qed.

Lemma ilc_dispatch_keeps_arguments : forall version ge e le m t le' m' out,
  ocn_exec ge e le m (ilc_dispatch version) t le' m' out ->
  le' ! IMB._m = le ! IMB._m /\ le' ! IMB._stepResult = le ! IMB._stepResult.
Proof.
  intros version ge e le m t le' m' out Hrun.
  destruct (ilc_source_cuts version) as (_ & _ & _ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. split; eapply iar_switch_keeps_temp; try exact Hrun.
  all: intros selector; destruct version;
    cbv [ilc_cases ilc_dispatch ilc_after_ground imb_body ibk_head
      rank12b_drop_sequences fn_body IMB.f_common_landing_action
      jp_mario_actions_moving.f_common_landing_action
      select_switch select_switch_case select_switch_default
      seq_of_labeled_statement cce_keeps_temp];
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    reflexivity.
Qed.

Lemma ilc_split_dispatch : forall version ge e le m rest t le' m' out,
  ocn_exec ge e le m (Ssequence (ilc_dispatch version) rest) t le' m' out ->
  exists middle memory pre suffix, t = pre ++ suffix /\
    ocn_exec ge e le m (ilc_dispatch version) pre middle memory Out_normal /\
    ocn_exec ge e middle memory rest suffix le' m' out.
Proof.
  intros version ge e le m rest t le' m' out Hrun. inversion Hrun; subst.
  - eauto 8.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
      (ilc_dispatch version) _ _ _ _ |- _ =>
      pose proof (ilc_dispatch_normal _ _ _ _ _ _ _ _ _ Hr) end. contradiction.
Qed.

Lemma ilc_actual_action_call_resets_timer : forall version e le m mb mo t le' m' out,
  e ! IMB._set_mario_action = None -> le ! IMB._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ilc_action_call t le' m' out ->
  ilh_timer_load m' mb mo = Some (Vint Int.zero).
Proof.
  intros version e le m mb mo t le' m' out Hlocal Hm Hrun.
  unfold ilc_action_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (ilh_selected_set_action_resolves version) as (fb & Hsymbol & Hfunction).
  lazymatch goal with Hr : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hr : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Hr; subst; clear Hr end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IMB._m _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast (Vptr mb mo) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _
    (Internal (ilh_set_action_body version)) _ _ _ _ |- _ =>
    exact (proj1 (iar_completed_set_action_resets_original_timer version _ mb mo
      _ _ _ _ _ Hcall)) end.
Qed.

Theorem ilc_left_ground_dispatch_resets_timer :
  forall version e le m mb mo t le' m' out,
  e ! IMB._set_mario_action = None -> le ! IMB._m = Some (Vptr mb mo) ->
  le ! IMB._stepResult = Some (Vint Int.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilc_dispatch version) t le' m' out ->
  ilh_timer_load m' mb mo = Some (Vint Int.zero).
Proof.
  intros version e le m mb mo t le' m' out Hlocal Hm Hzero Hrun.
  destruct (ilc_source_cuts version) as (_ & _ & _ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. inversion Hrun; subst.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IMB._stepResult _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
  lazymatch goal with Hswitch : sem_switch_arg _ _ = Some ?n |- _ =>
    change (Some 0%Z = Some n) in Hswitch; inversion Hswitch; subst end.
  destruct (ilc_zero_case_starts_with_real_action_call version) as [unused Hcase].
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
    (seq_of_labeled_statement (select_switch 0 _)) _ _ _ _ |- _ =>
    rewrite Hcase in Hr end.
  cce_unroll_loop_free_exec.
  all: match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _ ilc_action_call _ _ _ _ |- _ =>
    eapply ilc_actual_action_call_resets_timer; [exact Hlocal|exact Hm|exact Hcall] end.
Qed.

(** One complete selected invocation reaches the ground-result checkpoint.
    Both its acceleration choice and its ground call retain their real effects. *)
Definition InkLandingCallGroundResultCut : Prop :=
  forall version m mb mo animation airAction t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (imb_body version IMBLanding))
    [Vptr mb mo; animation; airAction] t m' result ->
  exists entry_le ground_le ground_m final_le prefix suffix out,
    t = prefix ++ suffix /\
    function_entry2 ge (imb_body version IMBLanding)
      [Vptr mb mo; animation; airAction] m empty_env entry_le m /\
    ocn_exec ge empty_env entry_le m (ocn_prepend (ilc_prefix version) Sskip)
      prefix ground_le ground_m Out_normal /\
    ground_le ! IMB._m = Some (Vptr mb mo) /\
    ocn_exec ge empty_env ground_le ground_m (ilc_after_ground version)
      suffix final_le m' out /\
    outcome_result_value out (fn_return (imb_body version IMBLanding)) result m'.

Theorem ilc_completed_landing_call_reaches_ground_result : InkLandingCallGroundResultCut.
Proof.
  unfold InkLandingCallGroundResultCut.
  intros version m mb mo animation airAction t m' result Hcall.
  destruct (ilc_source_cuts version) as (Hvars & Hparams & Hbody & Hnormal & Hkeep & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    pose proof He as Hentry; inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as Hm by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (ground_le & ground_m & prefix & suffix & Htrace & Hprefix & Hsuffix) end.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix Hkeep) as HgroundM.
  match type of Hentry with function_entry2 _ _ _ _ _ ?el _ =>
    match type of Hsuffix with ocn_exec _ _ _ _ _ _ ?last _ ?out =>
      exists el, ground_le, ground_m, last, prefix, suffix, out end end.
  repeat apply conj; assumption || congruence.
Qed.
