(** Concrete engine cases for the fresh triplet parent. The checked behavior
    has no movement flags; collision checks skip the intangible parent on
    either side, and the countdown does not turn -1 into zero. These local
    execution facts do not assume a frame for unexamined outside calls. *)
From Coq Require Import Bool Lia List ZArith Reals.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_behavior_data jp_behavior_data
  us_behavior_script jp_behavior_script us_object_collision jp_object_collision.
From LessThanOneAPress.Proofs Require Import ASTFacts GameTypes Area2TripletSpawner
  Area2TripletGraphics Area2TripletDistance Area2TripletDistanceUpdate
  Area2TripletCommand Area2Rank9ACoinFlight
  EyerokRank15LiveMovement ReadOnlyClightPaths SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module TC := us_object_collision.
Module TE := us_behavior_script.

Inductive TripletCollisionGate := ParentAsFirst | ParentAsSecond | IntangibleCountdown.
Definition te_gate_temp gate := match gate with
| ParentAsFirst => TC._t'3 | ParentAsSecond => TC._t'5
| IntangibleCountdown => TC._t'2 end.
Definition te_gate_receiver gate := match gate with
| ParentAsFirst => TC._a | ParentAsSecond => TC._b
| IntangibleCountdown => TC._sp4 end.
Definition te_gate_operator gate := match gate with
| IntangibleCountdown => Ogt | _ => Oeq end.
Definition te_gate_container version gate := fn_body (match version, gate with
| VersionUS, IntangibleCountdown => us_object_collision.f_clear_object_collision
| VersionJP, IntangibleCountdown => jp_object_collision.f_clear_object_collision
| VersionUS, _ => us_object_collision.f_check_collision_in_list
| VersionJP, _ => jp_object_collision.f_check_collision_in_list end).

Fixpoint te_find_gate temp s : option statement :=
  match s with
  | Ssequence (Sset id a) (Sifthenelse cond yes no) =>
      if Pos.eqb id temp then Some s else
        match te_find_gate temp yes with
        | Some found => Some found | None => te_find_gate temp no end
  | Ssequence first second | Sloop first second =>
      match te_find_gate temp first with
      | Some found => Some found | None => te_find_gate temp second end
  | Sifthenelse _ yes no => match te_find_gate temp yes with
      | Some found => Some found | None => te_find_gate temp no end
  | _ => None end.
Definition te_gate_statement version gate :=
  match te_find_gate (te_gate_temp gate) (te_gate_container version gate) with
  | Some s => s | None => Sskip end.

(** Successful extraction is part of the certificate: the fallback cannot
    turn a missing or changed source gate into a vacuous no-op proof. *)
Theorem te_generated_collision_gates : forall version gate, exists taken,
  te_find_gate (te_gate_temp gate) (te_gate_container version gate) =
    Some (te_gate_statement version gate) /\
  te_gate_statement version gate =
    Ssequence (Sset (te_gate_temp gate)
      (ts_raw_int version (te_gate_receiver gate) 5))
      (Sifthenelse (Ebinop (te_gate_operator gate)
        (Etempvar (te_gate_temp gate) tint) (Econst_int Int.zero tint) tint)
        taken Sskip).
Proof. intros [] []; eexists; split; reflexivity. Qed.

Theorem te_intangible_gate_is_readonly : forall version gate e le m ob oo,
  le ! (te_gate_receiver gate) = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 5))) =
    Some (Vint (Int.repr (-1))) ->
  exists final, readonly_path
    (Clight.globalenv (selected_clight_target version)) e m le
    (te_gate_statement version gate) final.
Proof.
  intros version gate e le m ob oo Hreceiver Hnegative.
  destruct (te_generated_collision_gates version gate) as (taken & Hfound & Hshape).
  rewrite Hshape. eexists. eapply ro_seq.
  - apply ro_set. eapply ts_raw_int_read; eauto.
  - eapply ro_if with (v := Vint Int.zero) (choice := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|constructor|].
      destruct gate; reflexivity.
    + reflexivity.
    + constructor.
Qed.

Definition TripletCollisionGatePreservation : Prop :=
  forall version gate e le m ob oo trace le' m' out,
  le ! (te_gate_receiver gate) = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 5))) =
    Some (Vint (Int.repr (-1))) ->
  ClightBigstep.Clight2.exec_stmt
    (Clight.globalenv (selected_clight_target version)) e le m
    (te_gate_statement version gate) trace le' m' out ->
  trace = E0 /\ m' = m /\ out = Out_normal.
Theorem te_intangible_collision_gates_preserve_memory : TripletCollisionGatePreservation.
Proof.
  intros version gate e le m ob oo trace le' m' out Hreceiver Hnegative Hrun.
  destruct (te_intangible_gate_is_readonly version gate e le m ob oo
    Hreceiver Hnegative) as [final Hpath].
  destruct (readonly_path_forces_every_execution _ _ _ _ _ _ Hpath
    _ _ _ _ Hrun) as (? & ? & ? & ?). auto.
Qed.

Definition te_script version := gvar_init (match version with
| VersionUS => us_behavior_data.v_bhvGoombaTripletSpawner
| VersionJP => jp_behavior_data.v_bhvGoombaTripletSpawner end).

Theorem te_exact_stock_script : forall version,
  te_script version =
    [Init_int32 (Int.repr 327680);       (* BEGIN PUSHABLE *)
     Init_int32 (Int.repr 285278273);    (* OR flags with 65 *)
     Init_int32 (Int.repr 503316480);    (* DROP_TO_FLOOR *)
     Init_int32 (Int.repr 134217728);    (* BEGIN_LOOP *)
     Init_int32 (Int.repr 201326592);    (* CALL_NATIVE *)
     Init_addrof TS._bhv_goomba_triplet_spawner_update Ptrofs.zero;
     Init_int32 (Int.repr 150994944)].   (* END_LOOP *)
Proof. intros []; reflexivity. Qed.

Definition te_flag_test bit := Ebinop Oand (Etempvar TE._objFlags tshort)
  (Ebinop Oshl (Econst_int Int.one tint) (Econst_int (Int.repr bit) tint) tint) tint.
Definition te_update version := match version with
| VersionUS => us_behavior_script.f_cur_obj_update
| VersionJP => jp_behavior_script.f_cur_obj_update end.

(** Find the exact flag branch in the generated body. The successful source
    checks below also require the named movement callee in its taken arm. *)
Fixpoint te_find_flag bit s : option statement := match s with
| Sifthenelse (Ebinop Oand (Etempvar id _)
    (Ebinop Oshl (Econst_int one _) (Econst_int shift _) _) _) yes Sskip =>
    if Pos.eqb id TE._objFlags && Int.eq one Int.one && Int.eq shift (Int.repr bit)
    then Some s else None
| Ssequence a b | Sloop a b => match te_find_flag bit a with
    | Some found => Some found | None => te_find_flag bit b end
| Sifthenelse _ a b => match te_find_flag bit a with
    | Some found => Some found | None => te_find_flag bit b end
| _ => None end.
Definition te_movement_bit which := match which with
| O => 1 | S O => 2 | _ => 9 end.
Definition te_movement_callee which := match which with
| O => TE._cur_obj_move_xz_using_fvel_and_yaw
| S O => TE._cur_obj_move_y_with_terminal_vel
| _ => TE._obj_build_transform_relative_to_parent end.
Definition te_movement_gate version which :=
  match te_find_flag (te_movement_bit which) (fn_body (te_update version)) with
  | Some s => s | None => Sskip end.

Theorem te_generated_movement_gates : forall version which, (which < 3)%nat ->
  exists taken,
  te_find_flag (te_movement_bit which) (fn_body (te_update version)) =
    Some (te_movement_gate version which) /\
  te_movement_gate version which =
    Sifthenelse (te_flag_test (te_movement_bit which)) taken Sskip /\
  calls_ident_s (te_movement_callee which) taken = true.
Proof.
  intros [] [|[|[|n]]] H; try lia; eexists; repeat split; reflexivity.
Qed.

Theorem te_stock_flags_skip_movement : forall version which e le m,
  (which < 3)%nat -> le ! TE._objFlags = Some (Vint (Int.repr 65)) ->
  readonly_path (Clight.globalenv (selected_clight_target version)) e m le
    (te_movement_gate version which) le.
Proof.
  intros version which e le m Hwhich Hflags.
  destruct (te_generated_movement_gates version which Hwhich)
    as (taken & Hfound & Hshape & Hcall).
  rewrite Hshape. eapply ro_if with (v := Vint Int.zero) (choice := false).
  - unfold te_flag_test. eapply eval_Ebinop.
    + apply eval_Etempvar. exact Hflags.
    + eapply eval_Ebinop; [constructor|constructor|].
      destruct which as [|[|n]]; reflexivity.
    + destruct which as [|[|n]]; reflexivity.
  - reflexivity.
  - constructor.
Qed.

(** The distance caller now resolves the real helper and exposes its exact
    sqrtf call and store. The complete CALL_NATIVE command also resolves
    and frames the spawner callback. The numerical sqrtf premise, loop
    return and intervening live-object updates are not discharged here. *)
Definition Area2TripletSpawnerBoundary : Prop :=
  TripletNativeCallPreservation /\ TripletGraphicsPreservation /\
  TripletLiveDistanceStore /\ TripletNativeCommandPreservation /\
  TripletCollisionGatePreservation /\
  (forall version which e le m,
    (which < 3)%nat -> le ! TE._objFlags = Some (Vint (Int.repr 65)) ->
    readonly_path (Clight.globalenv (selected_clight_target version)) e m le
      (te_movement_gate version which) le) /\
  TripletLiveElevatorDistanceRejection /\
  (forall version, te_script version = te_script VersionUS).

Theorem te_triplet_spawner_boundary_checked : Area2TripletSpawnerBoundary.
Proof.
  split; [exact ts_complete_native_call_preserves_existing_cells|].
  split; [exact tg_graphics_update_preserves_raw_fields|].
  split; [exact tdu_live_distance_reaches_field_store|].
  split; [exact tcn_native_command_preserves_parent_and_advances|].
  split; [exact te_intangible_collision_gates_preserve_memory|].
  split; [exact te_stock_flags_skip_movement|].
  split; [exact td_live_elevator_distance_rejects|].
  intros version. rewrite !te_exact_stock_script. reflexivity.
Qed.
