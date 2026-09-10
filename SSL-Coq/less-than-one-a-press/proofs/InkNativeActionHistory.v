(** One continuous, memory-preserving execution from the native behavior
    command through Mario's callback to the action's first graphical store.
    The two command readings below remain explicit live-entry conditions;
    an initializer receipt alone does not establish either runtime reading. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Generated Require Import us_behavior_data jp_behavior_data.
From LessThanOneAPress.Proofs Require Import GameTypes InkScheduledActionSource
  InkMarioCallbackHistory InkActionPassStart InkActionPassHistory InkBackwardSource
  OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition isn_body version := ish_body version ISNativeCommand.
Definition isn_global := Evar ISN._gCurBhvCommand (tptr tuint).
Definition isn_operand := Ederef
  (Ebinop Oadd (Etempvar ISN._t'2 (tptr tuint))
    (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint.
Definition isn_cast := Ecast (Etempvar ISN._t'3 tuint) (tptr tvoid).
Definition isn_call := Scall None
  (Etempvar ISN._behaviorFunc (tptr (Tfunction [] tvoid cc_default))) [].
Definition isn_tail version := match fn_body (isn_body version) with
| Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition isn_initial_temps version := create_undef_temps (fn_temps (isn_body version)).
Definition isn_call_temps version command ofs callback :=
  PTree.set ISN._behaviorFunc (Vptr callback Ptrofs.zero)
    (PTree.set ISN._t'3 (Vptr callback Ptrofs.zero)
      (PTree.set ISN._t'2 (Vptr command ofs) (isn_initial_temps version))).
Definition isn_callback_cont version command ofs callback k :=
  Kcall None (isn_body version) empty_env (isn_call_temps version command ofs callback)
    (Kseq (isn_tail version) k).
Definition isn_action_cont version command ofs callback argument k :=
  isc_action_cont version argument (isn_callback_cont version command ofs callback k).

Lemma isn_generated_prefix : forall version,
  fn_body (isn_body version) = Ssequence
    (Ssequence (Sset ISN._t'2 isn_global)
      (Ssequence (Sset ISN._t'3 isn_operand) (Sset ISN._behaviorFunc isn_cast)))
    (Ssequence isn_call (isn_tail version)).
Proof. intros []; reflexivity. Qed.

(** Word 10 is the callback operand of the command at byte 36.  This is
    stock data, not permission to install or modify a command at runtime. *)
Lemma isn_stock_mario_callback_operand :
  nth_error (gvar_init us_behavior_data.v_bhvMario) 10 =
    Some (Init_addrof ISC._bhv_mario_update Ptrofs.zero) /\
  nth_error (gvar_init jp_behavior_data.v_bhvMario) 10 =
    Some (Init_addrof ISC._bhv_mario_update Ptrofs.zero).
Proof. split; reflexivity. Qed.

Lemma isn_command_read : forall (ge : genv) le m cell command ofs,
  Genv.find_symbol ge ISN._gCurBhvCommand = Some cell ->
  Mem.load Mint32 m cell 0 = Some (Vptr command ofs) ->
  eval_expr ge empty_env le m isn_global (Vptr command ofs).
Proof.
  intros ge le m cell command ofs Hsymbol Hload.
  eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
  - apply eval_Evar_global; [reflexivity|exact Hsymbol].
  - eapply deref_loc_value with (chunk := Mint32); [reflexivity|exact Hload].
Qed.

Lemma isn_operand_read : forall (ge : genv) le m command ofs callback,
  le ! ISN._t'2 = Some (Vptr command ofs) ->
  Mem.load Mint32 m command
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4))) =
    Some (Vptr callback Ptrofs.zero) ->
  eval_expr ge empty_env le m isn_operand (Vptr callback Ptrofs.zero).
Proof.
  intros ge le m command ofs callback Htemp Hload.
  unfold isn_operand. eapply eval_Elvalue with
    (ofs := Ptrofs.add ofs (Ptrofs.repr 4)) (bf := Full).
  - apply eval_Ederef. eapply eval_Ebinop.
    + apply eval_Etempvar. exact Htemp.
    + constructor.
    + reflexivity.
  - eapply deref_loc_value with (chunk := Mint32); [reflexivity|exact Hload].
Qed.

Lemma isn_native_reaches_callback : forall version m cell command ofs callback k,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISN._gCurBhvCommand = Some cell ->
  Mem.load Mint32 m cell 0 = Some (Vptr command ofs) ->
  Mem.load Mint32 m command (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4))) =
    Some (Vptr callback Ptrofs.zero) ->
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) callback =
    Some (Internal (isc_body version)) ->
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (isn_body version)) [] k m) E0
    (Callstate (Internal (isc_body version)) []
      (isn_callback_cont version command ofs callback k) m).
Proof.
  intros version m cell command ofs callback k Hsymbol Hcommand Hoperand Hcallback.
  eapply star_left; [apply step_internal_function; apply ish_empty_call_entry| |reflexivity].
  rewrite isn_generated_prefix.
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left; [apply step_set; eapply isn_command_read; eauto| |reflexivity].
  eapply star_left; [apply step_skip_seq| |reflexivity].
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left.
  - apply step_set. eapply isn_operand_read; [apply PTree.gss|exact Hoperand].
  - eapply star_left; [apply step_skip_seq| |reflexivity].
    eapply star_left.
    + apply step_set. unfold isn_cast. eapply eval_Ecast.
      * apply eval_Etempvar. apply PTree.gss.
      * reflexivity.
    + eapply star_left; [apply step_skip_seq| |reflexivity].
      eapply star_left; [apply step_seq| |reflexivity].
      apply star_one. unfold isn_call, isn_callback_cont, isn_call_temps, isn_initial_temps.
      eapply step_call with (vf := Vptr callback Ptrofs.zero).
      * reflexivity.
      * apply eval_Etempvar. apply PTree.gss.
      * constructor.
      * exact Hcallback.
      * destruct version; reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Theorem isn_native_constructs_action_prefix :
  forall version m command_cell command ofs callback current_cell argument
    state_cell mario object action k,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISN._gCurBhvCommand = Some command_cell ->
  Mem.load Mint32 m command_cell 0 = Some (Vptr command ofs) ->
  Mem.load Mint32 m command (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4))) =
    Some (Vptr callback Ptrofs.zero) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISC._bhv_mario_update = Some callback ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISC._gCurrentObject = Some current_cell ->
  Mem.load Mint32 m current_cell 0 = Some argument ->
  sem_cast argument isc_object_type isc_object_type m = Some argument ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IBM._gMarioState = Some state_cell ->
  Mem.load Mint32 m state_cell 0 = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mint32 m mario 12 = Some action ->
  bool_val action tuint m = Some true ->
  Mem.load Mint32 m mario 136 = Some object ->
  exists ready,
    star Clight.step2 (Clight.globalenv (selected_clight_target version))
      (Callstate (Internal (isn_body version)) [] k m) E0
      (State (iap_body version) (ias_flag_frontier version)
        (Kseq (ias_after_visibility version) (Kseq (ias_return version)
          (isn_action_cont version command ofs callback argument k)))
        empty_env ready m) /\
    ready ! (ias_o1 version) = Some object /\
    ready ! (ias_o2 version) = Some object.
Proof.
  intros version m command_cell command ofs callback current_cell argument
    state_cell mario object action k Hcs Hcommand Hoperand Hcallback Hcurrent_symbol
    Hcurrent Hcast Hss Hstate Haction Hactive Hobject.
  destruct (ish_selected_helpers_resolve version ISMarioCallback) as (fb & Hfs & Hff).
  change (Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISC._bhv_mario_update = Some fb) in Hfs.
  assert (fb = callback) by congruence. subst fb.
  destruct (isc_callback_constructs_action_prefix version m current_cell argument
    state_cell mario object action (isn_callback_cont version command ofs callback k)
    Hcurrent_symbol Hcurrent Hcast Hss Hstate Haction Hactive Hobject) as (ready & Hsteps & Ho1 & Ho2).
  exists ready. split; [|auto].
  eapply star_trans.
  - eapply isn_native_reaches_callback; eauto.
  - exact Hsteps.
  - reflexivity.
Qed.
