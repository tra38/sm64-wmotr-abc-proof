(** Splice the constructed command/callback/action prefix onto an existing
    ImportedClightRun, at its exact final state and memory.  This is not an
    assertion that fresh initialization has already reached that state. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes ClightRefinement
  InkScheduledActionSource InkMarioCallbackHistory InkNativeActionHistory
  InkActionPassStart InkActionPassHistory InkBackwardSource InkBodyResetHistory
  InkSharedReadings ObjectContactNecessity OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

(** Explicit readings at ONE reached memory, not a summary assumption that
    all earlier calls are safe.  Initialization/scheduling must establish
    these readings; unsuccessful readings/conversions stay outside this
    case until the coverage proof handles them. *)
Record InkNativeEntryReadings version m a command_cell command ofs callback
    current_cell argument state_cell action : Prop := {
  ine_command_symbol : Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISN._gCurBhvCommand = Some command_cell;
  ine_command_pointer : Mem.load Mint32 m command_cell 0 = Some (Vptr command ofs);
  ine_callback_operand : Mem.load Mint32 m command
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vptr callback Ptrofs.zero);
  ine_callback_symbol : Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISC._bhv_mario_update = Some callback;
  ine_current_symbol : Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISC._gCurrentObject = Some current_cell;
  ine_current_read : Mem.load Mint32 m current_cell 0 = Some argument;
  ine_argument_cast : sem_cast argument isc_object_type isc_object_type m = Some argument;
  ine_state_symbol : Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IBM._gMarioState = Some state_cell;
  ine_state_pointer : Mem.load Mint32 m state_cell 0 =
    Some (Vptr (area1_state_storage_block a) Ptrofs.zero);
  ine_action_read : Mem.load Mint32 m (area1_state_storage_block a) 12 = Some action;
  ine_action_branch : bool_val action tuint m = Some true;
  ine_object_read : Mem.load Mint32 m (area1_state_storage_block a) 136 =
    Some (object_slot_pointer a (area1_mario_slot a))
}.

Lemma ish_append_actual_run : forall version (prefix : ImportedClightRun) checkpoint t last,
  run_program prefix = selected_clight_target version ->
  run_final prefix = checkpoint ->
  star Clight.step2 (Clight.globalenv (selected_clight_target version)) checkpoint t last ->
  exists joined : ImportedClightRun,
    run_program joined = selected_clight_target version /\
    run_start joined = run_start prefix /\
    run_trace joined = run_trace prefix ++ t /\ run_final joined = last /\
    exists cut : InkRunCut joined,
      ink_cut_state joined cut = run_final prefix /\
      ink_cut_before joined cut = run_trace prefix /\ ink_cut_after joined cut = t.
Proof.
  intros version prefix checkpoint t last Hprogram Hfinal Hextension.
  pose proof (run_steps prefix) as Hprefix. rewrite Hprogram in Hprefix.
  assert (star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (run_start prefix) (run_trace prefix ++ t) last) as Hwhole.
  { eapply star_trans; [exact Hprefix|rewrite Hfinal; exact Hextension|reflexivity]. }
  set (joined := {| run_program := selected_clight_target version; run_start := run_start prefix;
    run_trace := run_trace prefix ++ t; run_final := last; run_steps := Hwhole |}).
  exists joined.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  assert (star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (run_final prefix) t last) as Hsuffix by (rewrite Hfinal; exact Hextension).
  eexists (@Build_InkRunCut joined (run_final prefix) (run_trace prefix) t
    eq_refl Hprefix Hsuffix).
  repeat split; reflexivity.
Qed.

Definition InkNativeSharedHistoryExtension : Prop :=
  forall version (prefix : ImportedClightRun) m a k
    command_cell command ofs callback current_cell argument state_cell action,
  run_program prefix = selected_clight_target version ->
  run_final prefix = Callstate (Internal (isn_body version)) [] k m ->
  InkNativeEntryReadings version m a command_cell command ofs callback
    current_cell argument state_cell action ->
  exists (arrived : ImportedClightRun) ready,
    run_program arrived = selected_clight_target version /\
    run_start arrived = run_start prefix /\ run_trace arrived = run_trace prefix /\
    run_final arrived = State (iap_body version) (ias_flag_frontier version)
      (Kseq (ias_after_visibility version) (Kseq (ias_return version)
        (isn_action_cont version command ofs callback argument k))) empty_env ready m /\
    (exists cut : InkRunCut arrived,
      ink_cut_state arrived cut = run_final prefix /\
      ink_cut_before arrived cut = run_trace prefix /\ ink_cut_after arrived cut = E0) /\
    forall body bo t1 le1 m1 t2 le2 m2,
    area1_entry_slots_valid a ->
    area1_state_storage_block a <> area1_object_pool_block a ->
    state_cell <> area1_object_pool_block a ->
    body <> area1_state_storage_block a -> body <> area1_object_pool_block a ->
    Mem.load Mint32 m (area1_state_storage_block a) 152 = Some (Vptr body bo) ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env ready m
      (ias_flag_frontier version) t1 le1 m1 Out_normal ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le1 m1
      (ibr_call_stage version) t2 le2 m2 Out_normal ->
    exists joined : ImportedClightRun,
      run_program joined = selected_clight_target version /\
      run_start joined = run_start prefix /\
      run_trace joined = run_trace prefix ++ (t1 ++ t2) /\
      run_final joined = State (iap_body version) (ibr_after_reset version)
        (Kseq (ias_return version) (isn_action_cont version command ofs callback argument k))
        empty_env le2 m2 /\
      InkSameReadings a m m2 /\
      (InkInitialProducerReadings m a -> InkInitialProducerReadings m2 a) /\
      exists cut : InkRunCut joined,
        ink_cut_state joined cut = run_final prefix /\
        ink_cut_before joined cut = run_trace prefix /\ ink_cut_after joined cut = t1 ++ t2.

Theorem ish_native_prefix_and_reset_extend_one_history : InkNativeSharedHistoryExtension.
Proof.
  intros version prefix m a k command_cell command ofs callback current_cell argument
    state_cell action Hprogram Hfinal Hentry.
  destruct Hentry as [Hcommand_symbol Hcommand Hoperand Hcallback Hcurrent_symbol
    Hcurrent Hcast Hstate_symbol Hstate Haction Hactive Hobject].
  destruct (isn_native_constructs_action_prefix version m command_cell command ofs callback
    current_cell argument state_cell (area1_state_storage_block a)
    (object_slot_pointer a (area1_mario_slot a)) action k
    Hcommand_symbol Hcommand Hoperand Hcallback Hcurrent_symbol Hcurrent Hcast
    Hstate_symbol Hstate Haction Hactive Hobject) as (ready & Hnative & Ho1 & Ho2).
  destruct (ish_append_actual_run _ _ _ _ _ Hprogram Hfinal Hnative)
    as (arrived & Hap & Has & Hat & Haf & Hcut).
  exists arrived, ready.
  split; [exact Hap|]. split; [exact Has|].
  split; [rewrite Hat; apply app_nil_r|]. split; [exact Haf|]. split; [exact Hcut|].
  intros body bo t1 le1 m1 t2 le2 m2 Hslots Hstatepool Hglobalpool Hbodystate Hbodypool
    Hbody Hvisibility Hreset.
  destruct (ibr_visibility_then_reset_shared_extension version a state_cell body bo ready m
    t1 le1 m1 t2 le2 m2
    (Kseq (ias_return version) (isn_action_cont version command ofs callback argument k))
    Hslots Hstatepool Hglobalpool Hbodystate Hbodypool Hstate_symbol Hstate
    Hbody Ho1 Hvisibility Hreset) as [Hframe Hreset_steps].
  assert (star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (isn_body version)) [] k m) (t1 ++ t2)
    (State (iap_body version) (ibr_after_reset version)
      (Kseq (ias_return version) (isn_action_cont version command ofs callback argument k))
      empty_env le2 m2)) as Hextension.
  { eapply star_trans; [exact Hnative|exact Hreset_steps|reflexivity]. }
  destruct (ish_append_actual_run _ _ _ _ _ Hprogram Hfinal Hextension)
    as (joined & Hjp & Hjs & Hjt & Hjf & Hjcut).
  exists joined.
  split; [exact Hjp|]. split; [exact Hjs|]. split; [exact Hjt|]. split; [exact Hjf|].
  split; [exact Hframe|]. split; [|exact Hjcut].
  intro Hinitial. eapply ink_same_readings_keep_initial_producers; eauto.
Qed.
