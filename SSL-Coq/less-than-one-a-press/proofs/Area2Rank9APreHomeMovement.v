(** Rank 9A: a final released hop, defeat, coin flight and ONE pre-home
    ground-pound update. This strengthens a granted producer, not a clean
    installation. Live projection, the raw-Object/State copy, scheduling,
    higher supports and renewed airborne jumps remain explicit obligations. *)
From Coq Require Import Bool Lia List ZArith Reals Lra.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_obj_behaviors_2 jp_obj_behaviors_2
  us_behavior_data jp_behavior_data us_object_list_processor jp_object_list_processor.
From LessThanOneAPress.Proofs Require Import ASTFacts GameTypes ClightFacts
  Area2Rank9ACoinFlight Area2Rank9ACoinLaunch Area2Rank10AGroundPound
  Area2Rank9StarTiming SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module PHG := us_obj_behaviors_2.
Module PHD := us_behavior_data.
Module PHL := us_object_list_processor.

Definition rank9ph_regular_jump := Float32.mul
  (Float32.div (rank9ac_f32 1112014848) (rank9ac_f32 1077936128))
  (rank9ac_f32 1069547520).
Definition rank9ph_jump_rhs := Ebinop Omul
  (Ebinop Odiv (Econst_single (rank9ac_f32 1112014848) tfloat)
    (Econst_single (rank9ac_f32 1077936128) tfloat) tfloat)
  (Etempvar PHG._t'3 tfloat) tfloat.

Theorem rank9ph_regular_jump_is_generated :
  rank9cf_velocity_rhs (fn_body PHG.f_goomba_begin_jump) = [rank9ph_jump_rhs] /\
  rank9cf_velocity_rhs (fn_body jp_obj_behaviors_2.f_goomba_begin_jump) = [rank9ph_jump_rhs] /\
  hd (Init_space 0) (gvar_init PHG.v_sGoombaProperties) =
    Init_float32 (rank9ac_f32 1069547520) /\
  hd (Init_space 0) (gvar_init jp_obj_behaviors_2.v_sGoombaProperties) =
    Init_float32 (rank9ac_f32 1069547520) /\
  rank9ph_regular_jump = rank9cf_integer 25.
Proof.
  repeat split; try reflexivity.
  apply rank9cf_bits_injective. vm_compute. reflexivity.
Qed.

(** The script has no DELAY before its first native loop. These receipts are
    initialized source data/call order, NOT a proof that the live list runs.
    In particular an already active time stop is not eliminated here. *)
Definition rank9ph_star_script : list init_data :=
  [Init_int32 (Int.repr 393216); Init_int32 (Int.repr 285278209);
   Init_int32 (Int.repr 754974720); Init_int32 (Int.repr 201326592);
   Init_addrof PHD._bhv_spawned_star_init Ptrofs.zero;
   Init_int32 (Int.repr 134217728); Init_int32 (Int.repr 201326592);
   Init_addrof PHD._bhv_spawned_star_loop Ptrofs.zero;
   Init_int32 (Int.repr 150994944)].
Definition Rank9APreHomeSourceOrder : Prop :=
  gvar_init PHD.v_bhvSpawnedStarNoLevelExit = rank9ph_star_script /\
  gvar_init jp_behavior_data.v_bhvSpawnedStarNoLevelExit = rank9ph_star_script /\
  gvar_init PHL.v_sObjectListUpdateOrder =
    map (fun z => Init_int8 (Int.repr z)) [11;9;10;0;5;4;2;6;8;12;-1] /\
  gvar_init jp_object_list_processor.v_sObjectListUpdateOrder =
    map (fun z => Init_int8 (Int.repr z)) [11;9;10;0;5;4;2;6;8;12;-1] /\
  firstn 2 (direct_callees_s (fn_body PHL.f_bhv_mario_update)) =
    [PHL._execute_mario_action; PHL._copy_mario_state_to_object] /\
  firstn 2 (direct_callees_s (fn_body jp_object_list_processor.f_bhv_mario_update)) =
    [PHL._execute_mario_action; PHL._copy_mario_state_to_object].
Theorem rank9ph_source_order_checked : Rank9APreHomeSourceOrder.
Proof. repeat split; reflexivity. Qed.

Theorem rank9ph_released_jump_enters_envelope : forall y,
  rank9cf_finite y -> (-32768 <= rank9cf_real y <= 2517)%R ->
  Rank9CFFlightReach 2517 7 (y, rank9ph_regular_jump).
Proof.
  intros y Fy Hy.
  destruct rank9ph_regular_jump_is_generated as (_ & _ & _ & _ & Hj).
  rewrite Hj. destruct (rank9cf_integer_exact 25 ltac:(lia)) as [Rv Fv].
  apply rank9cf_flight_start. unfold rank9cf_envelope.
  change (0 <= 0 <= 7 /\ rank9cf_finite y /\ rank9cf_finite (rank9cf_integer 25) /\
    (-32768 <= rank9cf_real y <= 2517)%R /\
    (-78 <= rank9cf_real (rank9cf_integer 25) <= 28)%R).
  repeat split; try tauto; try lia; rewrite ?Rv; lra.
Qed.

Theorem rank9ph_release_height_bound : forall released,
  Rank9CFFlightReach 2517 7 released ->
  (rank9cf_real (fst released) <= 2601)%R.
Proof.
  intros released H. exact (rank9cf_flight_height_bound 2517 7 released
    ltac:(lia) ltac:(lia) H).
Qed.

Theorem rank9ph_finish_after_release_enters_envelope : forall released velocity,
  Rank9CFFlightReach 2517 7 released ->
  rank9cf_finite velocity -> (0 <= rank9cf_real velocity <= 52)%R ->
  Rank9CFFlightReach 2601 13 (fst released, velocity).
Proof.
  intros released velocity Hr Fv Hv.
  destruct (rank9cf_flight_has_envelope 2517 7 released ltac:(lia) ltac:(lia) Hr)
    as [n (_ & Fy & _ & Hy & _)].
  pose proof (rank9ph_release_height_bound released Hr) as Htop.
  apply rank9cf_flight_start. unfold rank9cf_envelope.
  change (0 <= 0 <= 13 /\ rank9cf_finite (fst released) /\ rank9cf_finite velocity /\
    (-32768 <= rank9cf_real (fst released) <= 2601)%R /\
    (-78 <= rank9cf_real velocity <= 52)%R).
  repeat split; try tauto; try lia; lra.
Qed.

Theorem rank9ph_defeat_to_coin_start : forall enemy seed random,
  Rank9CFFlightReach 2601 13 enemy ->
  rank9cf_finite seed -> (-32768 <= rank9cf_real seed)%R ->
  (rank9cf_real seed <= rank9cf_real (fst enemy) + 78)%R ->
  rank9cf_finite random -> (0 <= rank9cf_real random <= 1)%R ->
  Rank9CFFlightReach 2991 15
    (seed, rank9ac_launch_velocity random (rank9cf_integer 20)).
Proof.
  intros enemy seed random He Fs Hlo Hseed Fr Hr.
  pose proof (rank9cf_defeat_to_coin_seed_bound 2601 enemy (rank9cf_real seed)
    ltac:(lia) He Hseed) as Hhi.
  apply rank9cf_normal_launch_enters_flight; auto.
Qed.

Theorem rank9ph_contact_after_release_bound : forall coin contact,
  Rank9CFFlightReach 2991 15 coin ->
  (contact <= rank9cf_coin_top coin)%R -> (contact <= 3475)%R.
Proof.
  intros coin contact Hc Hm.
  pose proof (rank9cf_coin_top_bound 2991 coin ltac:(lia) Hc) as Htop.
  change (rank9cf_coin_top coin <= 3475)%R in Htop. lra.
Qed.

Theorem rank9ph_one_gp_update_bound : forall coin y timer,
  Rank9CFFlightReach 2991 15 coin ->
  rank9cf_finite y -> (-32768 <= rank9cf_real y)%R ->
  (rank9cf_real y <= rank9cf_coin_top coin)%R -> 0 <= timer ->
  rank9cf_finite (Float32.add y (rank9cf_integer (rank10a_offset timer))) /\
  (rank9cf_real (Float32.add y (rank9cf_integer (rank10a_offset timer))) <= 3495)%R.
Proof.
  intros coin y timer Hc Fy Hlo Hcontact Htimer.
  pose proof (rank9ph_contact_after_release_bound coin (rank9cf_real y) Hc Hcontact) as Hy.
  destruct (rank10a_budget_step timer Htimer) as [Hoffset _].
  destruct (rank9cf_integer_exact (rank10a_offset timer) ltac:(lia)) as [Ro Fo].
  assert (Hor : (0 <= IZR (rank10a_offset timer) <= 20)%R)
    by (split; apply IZR_le; lia).
  destruct (rank9cf_add_range y (rank9cf_integer (rank10a_offset timer)) (-32768) 3495
    Fy Fo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Ro; lra)) as [F H].
  split; [exact F | exact (proj2 H)].
Qed.

(** Exact selected-Clight post-headroom write. The input load is at the GP
    body, not silently equated to an earlier raw-Object coin collision. That
    equality/no-intervening-lift remains a live projection premise. *)
Definition Rank9APreHomeStoreBound : Prop :=
  forall version environment locals memory mario coin y timer,
  Rank9CFFlightReach 2991 15 coin ->
  rank9cf_finite y -> (-32768 <= rank9cf_real y)%R ->
  (rank9cf_real y <= rank9cf_coin_top coin)%R -> 0 <= timer < 10 ->
  locals ! GP._m = Some (Vptr mario Ptrofs.zero) ->
  locals ! GP._yOffset = Some (Vsingle (rank9cf_integer (rank10a_offset timer))) ->
  Mem.load Mfloat32 memory mario 64 = Some (Vsingle y) ->
  Mem.valid_access memory Mfloat32 mario 64 Writable ->
  exists after,
    ClightBigstep.Clight2.exec_stmt
      (Clight.globalenv (selected_clight_target version)) environment locals memory
      rank10a_y_write E0 (PTree.set GP._t'25 (Vsingle y) locals) after Out_normal /\
    Mem.load Mfloat32 after mario 64 =
      Some (Vsingle (Float32.add y (rank9cf_integer (rank10a_offset timer)))) /\
    (rank9cf_real (Float32.add y (rank9cf_integer (rank10a_offset timer))) < 3505)%R.

Theorem rank9ph_gp_store_below_gate : Rank9APreHomeStoreBound.
Proof.
  unfold Rank9APreHomeStoreBound.
  intros version environment locals memory mario coin y timer Hcoin Fy Hlo Hcontact
    Htimer Hm Ho Hy Haccess.
  destruct (Mem.valid_access_store _ _ _ _
    (Vsingle (Float32.add y (rank9cf_integer (rank10a_offset timer)))) Haccess)
    as [after Hstore].
  exists after. split.
  - eapply rank10a_y_write_executes; eauto.
  - split.
    + erewrite Mem.load_store_same by exact Hstore. reflexivity.
    + pose proof (rank9ph_one_gp_update_bound coin y timer Hcoin Fy Hlo Hcontact ltac:(lia)). lra.
Qed.

Theorem rank9ph_sampled_home_bound : forall sample,
  rank9cf_finite sample -> (-32768 <= rank9cf_real sample <= 3495)%R ->
  (rank9cf_real (Float32.add sample rank9t_250) <= 3745)%R /\
  (rank9cf_real sample < 3505)%R.
Proof.
  intros sample Fs Hs.
  assert (H250 : rank9t_250 = rank9cf_integer 250)
    by (apply rank9cf_bits_injective; vm_compute; reflexivity).
  rewrite H250. destruct (rank9cf_integer_exact 250 ltac:(lia)) as [R250 F250].
  destruct (rank9cf_add_range sample (rank9cf_integer 250) (-32518) 3745
    Fs F250 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R250; lra)) as [_ H].
  split; lra.
Qed.

Definition Rank9APreHomeMovementBoundary : Prop :=
  Rank9APreHomeSourceOrder /\ Rank9APreHomeStoreBound /\ Rank9HomeYExecution /\
  (forall y, rank9cf_finite y -> (-32768 <= rank9cf_real y <= 2517)%R ->
    Rank9CFFlightReach 2517 7 (y, rank9ph_regular_jump)) /\
  (forall released velocity, Rank9CFFlightReach 2517 7 released ->
    rank9cf_finite velocity -> (0 <= rank9cf_real velocity <= 52)%R ->
    Rank9CFFlightReach 2601 13 (fst released, velocity)) /\
  (forall enemy seed random, Rank9CFFlightReach 2601 13 enemy ->
    rank9cf_finite seed -> (-32768 <= rank9cf_real seed)%R ->
    (rank9cf_real seed <= rank9cf_real (fst enemy) + 78)%R ->
    rank9cf_finite random -> (0 <= rank9cf_real random <= 1)%R ->
    Rank9CFFlightReach 2991 15 (seed, rank9ac_launch_velocity random (rank9cf_integer 20))) /\
  (forall coin contact, Rank9CFFlightReach 2991 15 coin ->
    (contact <= rank9cf_coin_top coin)%R -> (contact <= 3475)%R) /\
  (forall sample, rank9cf_finite sample -> (-32768 <= rank9cf_real sample <= 3495)%R ->
    (rank9cf_real (Float32.add sample rank9t_250) <= 3745)%R /\
    (rank9cf_real sample < 3505)%R).

Theorem rank9ph_prehome_boundary_checked : Rank9APreHomeMovementBoundary.
Proof.
  split; [exact rank9ph_source_order_checked |].
  split; [exact rank9ph_gp_store_below_gate |].
  split; [exact rank9t_home_y_executes |].
  split; [exact rank9ph_released_jump_enters_envelope |].
  split; [exact rank9ph_finish_after_release_enters_envelope |].
  split; [exact rank9ph_defeat_to_coin_start |].
  split; [exact rank9ph_contact_after_release_bound | exact rank9ph_sampled_home_bound].
Qed.
