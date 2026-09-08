From Coq Require Import Lia List ZArith.
From compcert Require Import Archi AST Clight Clightdefs ClightBigstep Cop Ctypes
  Errors Events Floats Globalenvs Integers Maps Memory Values.
From Pedro.Generated Require Import us_mario_actions_moving jp_mario_actions_moving
  us_mario_step jp_mario_step.
From Pedro.Proofs Require Import GameTypes TTCCogExecution SlideKickDustExecution
  CogActionExecution CogDustClearing.
Import ListNotations.
Open Scope Z_scope.
Module MD := us_mario_actions_moving.

Lemma cog_dispatch_mptr_size : size_chunk Mptr = 4.
Proof. reflexivity. Qed.

(** These two cases select real action constants and real generated functions.
    They do not assert that either action is reachable at the cogs. *)
Inductive cog_moving_case := CogSlideCase | CogBackwardKBCase.
Definition cog_moving_action case : Z :=
  match case with CogSlideCase => 8389722 | CogBackwardKBCase => 132194 end.
Definition cog_moving_function version case : function :=
  match version, case with
  | VersionUS, CogSlideCase => MD.f_act_slide_kick_slide
  | VersionJP, CogSlideCase => jp_mario_actions_moving.f_act_slide_kick_slide
  | VersionUS, CogBackwardKBCase => MD.f_act_backward_ground_kb
  | VersionJP, CogBackwardKBCase => jp_mario_actions_moving.f_act_backward_ground_kb
  end.
Definition cog_cancel_function version : function :=
  match version with VersionUS => MD.f_check_common_moving_cancels
  | VersionJP => jp_mario_actions_moving.f_check_common_moving_cancels end.
Definition cog_quicksand_function version : function :=
  match version with VersionUS => us_mario_step.f_mario_update_quicksand
  | VersionJP => jp_mario_step.f_mario_update_quicksand end.
Definition cog_dispatch_function version : function :=
  match version with VersionUS => MD.f_mario_execute_moving_action
  | VersionJP => jp_mario_actions_moving.f_mario_execute_moving_action end.
Definition cog_moving_symbol case : ident :=
  match case with CogSlideCase => MD._act_slide_kick_slide
  | CogBackwardKBCase => MD._act_backward_ground_kb end.

Record cog_dispatch_layout (ge : Clight.genv) (caller : slide_caller_layout ge) : Type := {
  dispatch_health_offset : field_offset (genv_cenv ge) MD._health
    (co_members (slide_mario_co ge caller)) = OK (174, Full);
  dispatch_quicksand_offset : field_offset (genv_cenv ge) us_mario_step._quicksandDepth
    (co_members (slide_mario_co ge caller)) = OK (192, Full)
}.

Definition cog_dispatch_entry memory mario floor case : Prop :=
  Mem.load Mfloat32 memory mario 64 = Some (Vsingle (Float32.of_int (Int.repr (-2088)))) /\
  Mem.load Mint16signed memory mario 118 = Some (Vint (Int.repr (-11000))) /\
  Mem.load Mint16signed memory mario 174 = Some (Vint (Int.repr 2176)) /\
  Mem.load Mint16unsigned memory mario 2 = Some (Vint (Int.repr 4)) /\
  Mem.load Mint32 memory mario 12 = Some (Vint (Int.repr (cog_moving_action case))) /\
  Mem.load Mptr memory mario 104 = Some (Vptr floor Ptrofs.zero) /\
  Mem.load Mint16signed memory floor 0 = Some (Vint Int.zero) /\
  Mem.load Mfloat32 memory mario 192 = Some (Vsingle Float32.zero).

Definition cog_quicksand_stores before middle after mario : Prop :=
  Mem.store Mfloat32 before mario 192
    (Vsingle (Float32.of_bits (Int.repr 1066192077))) = Some middle /\
  Mem.store Mfloat32 middle mario 192 (Vsingle Float32.zero) = Some after.

Theorem generated_cog_moving_cancels_pass_us_jp :
  forall version case ge memory mario floor (caller : slide_caller_layout ge),
    cog_action_layout ge caller -> cog_dispatch_layout ge caller ->
    cog_dispatch_entry memory mario floor case ->
    eval_funcall function_entry2 ge memory (Internal (cog_cancel_function version))
      [Vptr mario Ptrofs.zero] E0 memory (Vint Int.zero).
Proof.
  intros version case ge memory mario floor caller Hlayout Hdispatch Himage.
  destruct Himage as (Hheight & Hw & Hhealth & Hinput & Hact & Hfloor & Htype & Hdepth).
  destruct Hlayout; destruct Hdispatch; destruct caller; cbn in *.
  destruct version, case; cbn [cog_cancel_function cog_moving_action] in *.
  all:
    eapply eval_funcall_internal;
    [action_entry | simpl fn_body; timeout 20 action_stmt |
     cbn; split; [discriminate | reflexivity] | cbn; reflexivity].
Qed.

Theorem generated_cog_quicksand_default_us_jp :
  forall version case ge before middle after mario floor (caller : slide_caller_layout ge),
    cog_action_layout ge caller -> cog_dispatch_layout ge caller ->
    floor <> mario -> cog_dispatch_entry before mario floor case ->
    cog_quicksand_stores before middle after mario ->
    eval_funcall function_entry2 ge before (Internal (cog_quicksand_function version))
      [Vptr mario Ptrofs.zero; Vsingle (Float32.of_bits (Int.repr 1048576000))]
      E0 after (Vint Int.zero).
Proof.
  intros version case ge before middle after mario floor caller Hlayout Hdispatch
    Hdistinct Himage [Hraise Hreset].
  destruct Himage as (Hheight & Hw & Hhealth & Hinput & Hact & Hfloor & Htype & Hdepth).
  assert (Hfloor_middle : Mem.load Mptr middle mario 104 = Some (Vptr floor Ptrofs.zero)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ Hraise) by
      (rewrite cog_dispatch_mptr_size; cbn; intuition lia).
    exact Hfloor. }
  assert (Htype_middle : Mem.load Mint16signed middle floor 0 = Some (Vint Int.zero)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ Hraise) by (left; congruence).
    exact Htype. }
  destruct Hlayout; destruct Hdispatch; destruct caller; cbn in *.
  destruct version, case; cbn [cog_quicksand_function cog_moving_action] in *.
  all:
    eapply eval_funcall_internal;
    [action_entry | simpl fn_body; timeout 20 action_stmt |
     cbn; split; [discriminate | reflexivity] | cbn; reflexivity].
Qed.

Lemma cog_quicksand_frame : forall before middle after mario,
  cog_quicksand_stores before middle after mario ->
  forall chunk b offset,
    b <> mario \/ offset + size_chunk chunk <= 192 \/ 196 <= offset ->
    Mem.load chunk after b offset = Mem.load chunk before b offset.
Proof.
  intros before middle after mario [Hraise Hreset] chunk b offset Hsafe.
  rewrite (Mem.load_store_other _ _ _ _ _ _ Hreset) by (cbn; intuition lia).
  rewrite (Mem.load_store_other _ _ _ _ _ _ Hraise) by (cbn; intuition lia).
  reflexivity.
Qed.

Lemma cog_quicksand_preserves_anchor : forall before middle after mario,
  cog_quicksand_stores before middle after mario ->
  slide_anchor after mario = slide_anchor before mario.
Proof.
  intros before middle after mario Hstores. unfold slide_anchor.
  repeat rewrite (cog_quicksand_frame _ _ _ _ Hstores) by
    (rewrite ?cog_dispatch_mptr_size; cbn; intuition lia).
  reflexivity.
Qed.

Theorem cog_quicksand_stores_exist : forall before mario,
  Mem.valid_access before Mfloat32 mario 192 Writable ->
  exists middle after, cog_quicksand_stores before middle after mario.
Proof.
  intros before mario Hwrite.
  destruct (Mem.valid_access_store before Mfloat32 mario 192
    (Vsingle (Float32.of_bits (Int.repr 1066192077))) Hwrite) as [middle Hraise].
  destruct (Mem.valid_access_store middle Mfloat32 mario 192 (Vsingle Float32.zero)
    ltac:(cog_memory_access)) as [after Hreset].
  exists middle, after. split; assumption.
Qed.

Definition cog_dispatch_bindings version case (ge : Clight.genv) cancel quicksand action : Prop :=
  Genv.find_symbol ge MD._check_common_moving_cancels = Some cancel /\
  Genv.find_funct_ptr ge cancel = Some (Internal (cog_cancel_function version)) /\
  Genv.find_symbol ge MD._mario_update_quicksand = Some quicksand /\
  Genv.find_funct_ptr ge quicksand = Some (Internal (cog_quicksand_function version)) /\
  Genv.find_symbol ge (cog_moving_symbol case) = Some action /\
  Genv.find_funct_ptr ge action = Some (Internal (cog_moving_function version case)).

(** The complete dispatcher, including both prefix callees and its real switch.
    Only the selected action's execution is a callee premise. The integrated
    slide theorem replaces that premise with the already checked slide body. *)
Theorem generated_cog_complete_moving_dispatcher_us_jp :
  forall version case ge before middle ready after mario floor cancel quicksand action
    (caller : slide_caller_layout ge),
    cog_action_layout ge caller -> cog_dispatch_layout ge caller ->
    floor <> mario -> cog_dispatch_entry before mario floor case ->
    cog_quicksand_stores before middle ready mario ->
    cog_dispatch_bindings version case ge cancel quicksand action ->
    eval_funcall function_entry2 ge ready (Internal (cog_moving_function version case))
      [Vptr mario Ptrofs.zero] E0 after (Vint Int.zero) ->
    Mem.load Mint16unsigned after mario 2 = Some (Vint (Int.repr 4)) ->
    eval_funcall function_entry2 ge before (Internal (cog_dispatch_function version))
      [Vptr mario Ptrofs.zero] E0 after (Vint Int.zero).
Proof.
  intros version case ge before middle ready after mario floor cancel quicksand action
    caller Hlayout Hdispatch Hdistinct Himage Hstores Hbindings Haction Hinput_after.
  pose proof (generated_cog_moving_cancels_pass_us_jp version case ge before mario floor
    caller Hlayout Hdispatch Himage) as Hcancel.
  pose proof (generated_cog_quicksand_default_us_jp version case ge before middle ready
    mario floor caller Hlayout Hdispatch Hdistinct Himage Hstores) as Hquicksand.
  destruct Hbindings as (Hcs & Hcc & Hqs & Hqc & Has & Hac).
  assert (Hact_ready : Mem.load Mint32 ready mario 12 =
    Some (Vint (Int.repr (cog_moving_action case)))).
  { rewrite (cog_quicksand_frame _ _ _ _ Hstores) by (cbn; intuition lia).
    destruct Himage as (_ & _ & _ & _ & Hact & _). exact Hact. }
  destruct Hlayout; destruct Hdispatch; destruct caller; cbn in *.
  destruct version, case;
    cbn [cog_dispatch_function cog_moving_function cog_moving_symbol cog_moving_action] in *.
  all:
    eapply eval_funcall_internal;
    [action_entry | simpl fn_body; timeout 30 action_stmt |
     cbn; split; [discriminate | reflexivity] | cbn; reflexivity].
Qed.

Definition cog_dispatch_layout_receipt : Prop :=
  forall version,
  let ce := prog_comp_env (match version with
    VersionUS => MD.prog | VersionJP => jp_mario_actions_moving.prog end) in
  match ce ! MD._MarioState with
  | Some co => map (fun field => field_offset ce field (co_members co))
      [MD._health; us_mario_step._quicksandDepth] = [OK (174, Full); OK (192, Full)]
  | None => False end.

Theorem cog_dispatch_layout_generated_us_jp : cog_dispatch_layout_receipt.
Proof. intros []; vm_compute; reflexivity. Qed.
