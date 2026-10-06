(** Exact generated-source cuts for cached object contact and the graphical
    floor retry. The chronology claims are bilateral AST certificates; the
    later null-floor guard also has a bounded actual execution construction.
    In particular, no theorem here assumes or concludes that a live
    collided-object pointer survives every intervening call, that a writable
    handler table dispatches faithfully, or that a supplied split is reachable.

    Straight-line source order is kept separate from branch execution. The
    existing retry and action-prefix cuts are reused, while the null-floor
    return and the cached-list reader are exposed as composable exact bodies.
    A second null floor can request death before interactions and the later
    action return; accepting a cached warp handler is therefore not by itself
    proof of a successful delayed warp. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import
  us_mario jp_mario us_interaction jp_interaction
  us_object_list_processor jp_object_list_processor.
From LessThanOneAPress.Proofs Require Import
  GameTypes ASTFacts ObjectContactNecessity Area2Rank12BContact Area1QueryScheduleClosure
  Area1InteractionShortCircuitClosure InkBackwardSource InkActionPassHistory
  InkCopyCaller InkActionPassStart SelectedClightTarget EyerokRank15LiveMovement.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Module IFSOM := us_mario.
Module IFSOI := us_interaction.
Module IFSOO := us_object_list_processor.

Definition ifso_objects version := match version with
| VersionUS => us_object_list_processor.f_update_objects
| VersionJP => jp_object_list_processor.f_update_objects end.
Definition ifso_inputs version := match version with
| VersionUS => us_mario.f_update_mario_inputs
| VersionJP => jp_mario.f_update_mario_inputs end.
Definition ifso_lookup version := match version with
| VersionUS => us_interaction.f_mario_get_collided_object
| VersionJP => jp_interaction.f_mario_get_collided_object end.
Definition ifso_interactions version := match version with
| VersionUS => us_interaction.f_mario_process_interactions
| VersionJP => jp_interaction.f_mario_process_interactions end.

(** Unlike a branch-flattened callee census, this order traverses only actual
    top-level sequences. It still does not establish call completion. *)
Definition InkFallbackObjectSourceOrder : Prop := forall version,
  ident_subsequenceb
    [IFSOO._clear_dynamic_surfaces; IFSOO._update_terrain_objects;
     IFSOO._apply_mario_platform_displacement; IFSOO._detect_object_collisions;
     IFSOO._update_non_terrain_objects; IFSOO._unload_deactivated_objects;
     IFSOO._update_mario_platform]
    (straightline_callees_s (fn_body (ifso_objects version))) = true /\
  direct_call_count IFSOO._detect_object_collisions
    (fn_body (ifso_objects version)) = 1%nat.

Theorem ifso_collision_precedes_nonterrain_in_generated_sequence :
  InkFallbackObjectSourceOrder.
Proof. intros []; vm_compute; split; reflexivity. Qed.

Definition ifso_floor_check version := ibk_head (iap_after_preparation version).
Definition ifso_action_loop version :=
  ibk_head (rank12b_drop_sequences 1 (iap_after_preparation version)).
Definition ifso_after_action_loop version :=
  rank12b_drop_sequences 2 (iap_after_preparation version).
Definition ifso_action_loop_body version := match ifso_action_loop version with
| Sloop (Ssequence _ body) Sskip => body | _ => Sskip end.
Definition ifso_state_temp version := match version with
| VersionUS => us_mario._t'42 | VersionJP => jp_mario._t'38 end.
Definition ifso_floor_temp version := match version with
| VersionUS => us_mario._t'43 | VersionJP => jp_mario._t'39 end.
Definition ifso_state_field temp field ty := Efield
  (Ederef (Etempvar temp (tptr (Tstruct IFSOM._MarioState noattr)))
    (Tstruct IFSOM._MarioState noattr)) field ty.

(** The four named calls are exact actual State-pointer load/call stages.
    Their final interaction stage is followed by the floor test, and only
    after that test does the source contain the action loop. *)
Definition InkFallbackMarioSourceOrder : Prop := forall version,
  iap_enabled version = ocn_prepend (iap_stages version)
    (Ssequence (ifso_floor_check version)
      (Ssequence (ifso_action_loop version) (ifso_after_action_loop version))) /\
  map iap_call_name (skipn 1 (iap_stages version)) =
    [Some IFSOM._mario_reset_bodystate; Some IFSOM._update_mario_inputs;
     Some IFSOM._mario_handle_special_floors; Some IFSOM._mario_process_interactions] /\
  ifso_floor_check version = Ssequence
    (Sset (ifso_state_temp version)
      (Evar IFSOM._gMarioState (tptr (Tstruct IFSOM._MarioState noattr))))
    (Ssequence
      (Sset (ifso_floor_temp version)
        (ifso_state_field (ifso_state_temp version) IFSOM._floor
          (tptr (Tstruct IFSOM._Surface noattr))))
      (Sifthenelse
        (Ebinop Oeq (Etempvar (ifso_floor_temp version)
          (tptr (Tstruct IFSOM._Surface noattr)))
          (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint)
        (Sreturn (Some (Econst_int Int.zero tint))) Sskip)) /\
  ifso_action_loop version = Sloop
    (Ssequence (Sifthenelse (Etempvar IFSOM._inLoop tint) Sskip Sbreak)
      (ifso_action_loop_body version)) Sskip.

Theorem ifso_interactions_precede_exact_null_return_and_action_loop :
  InkFallbackMarioSourceOrder.
Proof. intros []; repeat split; reflexivity. Qed.

Definition ifso_input_prefix version := ocn_prefix_items 7 (fn_body (ifso_inputs version)).
Definition ifso_input_tail version := rank12b_drop_sequences 7 (fn_body (ifso_inputs version)).
Definition ifso_cached_mask_import := Ssequence
  (Sset IFSOM._t'15
    (ifso_state_field IFSOM._m IFSOM._marioObj
      (tptr (Tstruct IFSOM._Object noattr))))
  (Ssequence
    (Sset IFSOM._t'16
      (Efield (Ederef (Etempvar IFSOM._t'15
        (tptr (Tstruct IFSOM._Object noattr))) (Tstruct IFSOM._Object noattr))
        IFSOM._collidedObjInteractTypes tuint))
    (Sassign (ifso_state_field IFSOM._m IFSOM._collidedObjInteractTypes tuint)
      (Etempvar IFSOM._t'16 tuint))).

Definition InkFallbackInputSourceOrder : Prop := forall version,
  fn_body (ifso_inputs version) =
    ocn_prepend (ifso_input_prefix version) (ifso_input_tail version) /\
  nth_error (ifso_input_prefix version) 2 = Some ifso_cached_mask_import /\
  flat_map straightline_callees_s (ifso_input_prefix version) =
    [IFSOM._update_mario_button_inputs; IFSOM._update_mario_joystick_inputs;
     IFSOM._update_mario_geometry_inputs] /\
  nth_error (ifso_input_prefix version) 6 = Some
    (Scall None (Evar IFSOM._update_mario_geometry_inputs
      (Tfunction [tptr (Tstruct IFSOM._MarioState noattr)] tvoid cc_default))
      [Etempvar IFSOM._m (tptr (Tstruct IFSOM._MarioState noattr))]).

Theorem ifso_inputs_import_cached_mask_before_geometry : InkFallbackInputSourceOrder.
Proof. intros []; repeat split; reflexivity. Qed.

(** Reuse the exact null-guard/copy/retry decomposition. The first query is
    in the prefix, the graphical copy and second query are in the guarded
    branch, and the second-null death request is in the following suffix.
    Absence of a direct collision call is not transitive callee framing. *)
Definition InkFallbackGeometrySourceOrder : Prop := forall version,
  fn_body (ibk_geometry_body version) = ocn_prepend (ibk_before_retry version)
    (Ssequence (ibk_choice version) (ibk_after_retry version)) /\
  ibk_choice version = Ssequence (Sset IFSOM._t'41 ibk_floor_read)
    (Sifthenelse ibk_null_guard (ibk_retry version) Sskip) /\
  ibk_retry version = Ssequence (ibk_copy_prefix version) (ibk_second_query version) /\
  flat_map straightline_callees_s (ibk_before_retry version) =
    [IFSOM._f32_find_wall_collision; IFSOM._f32_find_wall_collision; IFSOM._find_floor] /\
  straightline_callees_s (ibk_retry version) = [IFSOM._vec3f_copy; IFSOM._find_floor] /\
  contains_guarded_floor_null_else_call_s
    IFSOM._m IFSOM._floor IFSOM._level_trigger_warp 18
    (ibk_after_retry version) = true /\
  direct_call_count IFSOO._detect_object_collisions
    (fn_body (ibk_geometry_body version)) = 0%nat.

Theorem ifso_first_floor_then_guarded_copy_retry_then_death_source :
  InkFallbackGeometrySourceOrder.
Proof.
  intro version.
  destruct (ibk_geometry_cuts_are_generated version) as (Hbody & Hguard & Hretry & _).
  split; [exact Hbody|]. split; [exact Hguard|]. split; [exact Hretry|].
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Definition ifso_lookup_loop version := match fn_body (ifso_lookup version) with
| Ssequence (Ssequence _ loop) _ => loop | _ => Sskip end.
Definition ifso_lookup_test version := match ifso_lookup_loop version with
| Sloop (Ssequence test _) _ => test | _ => Sskip end.
Definition ifso_lookup_rest version := match ifso_lookup_loop version with
| Sloop (Ssequence _ rest) _ => rest | _ => Sskip end.
Definition ifso_lookup_read version := ibk_head (ifso_lookup_rest version).
Definition ifso_lookup_match version := rank12b_drop_sequences 1 (ifso_lookup_rest version).
Definition ifso_lookup_type_read version := ibk_head (ifso_lookup_match version).
Definition ifso_object_field temp field ty := Efield
  (Ederef (Etempvar temp (tptr (Tstruct IFSOI._Object noattr)))
    (Tstruct IFSOI._Object noattr)) field ty.
Definition ifso_lookup_state_object := Efield
  (Ederef (Etempvar IFSOI._m (tptr (Tstruct IFSOI._MarioState noattr)))
    (Tstruct IFSOI._MarioState noattr)) IFSOI._marioObj
    (tptr (Tstruct IFSOI._Object noattr)).
Definition ifso_cached_list_read := Ssequence
  (Sset IFSOI._t'2 ifso_lookup_state_object)
  (Sset IFSOI._object (Ederef
    (Ebinop Oadd
      (ifso_object_field IFSOI._t'2 IFSOI._collidedObjs
        (tarray (tptr (Tstruct IFSOI._Object noattr)) 4))
      (Etempvar IFSOI._i tint) (tptr (tptr (Tstruct IFSOI._Object noattr))))
    (tptr (Tstruct IFSOI._Object noattr)))).

(** The whole getter is one counted cached-array scan, followed by a null
    return. It contains no call at all, hence no fresh hitbox query. The
    candidate matching test returns the exact pointer loaded from that array.
    Its reachability and the cached-array memory contents remain open. *)
Definition InkFallbackCachedLookupSource : Prop := forall version,
  fn_body (ifso_lookup version) = Ssequence
    (Ssequence (Sset IFSOI._i (Econst_int Int.zero tint))
      (Sloop (Ssequence (ifso_lookup_test version)
        (Ssequence (ifso_lookup_read version) (ifso_lookup_match version)))
        (Sset IFSOI._i (Ebinop Oadd (Etempvar IFSOI._i tint)
          (Econst_int Int.one tint) tint))))
    (Sreturn (Some (Ecast (Econst_int Int.zero tint) (tptr tvoid)))) /\
  ifso_lookup_test version = Ssequence
    (Sset IFSOI._t'3 ifso_lookup_state_object)
    (Ssequence
      (Sset IFSOI._t'4 (ifso_object_field IFSOI._t'3 IFSOI._numCollidedObjs tshort))
      (Sifthenelse (Ebinop Olt (Etempvar IFSOI._i tint)
        (Etempvar IFSOI._t'4 tshort) tint) Sskip Sbreak)) /\
  ifso_lookup_read version = ifso_cached_list_read /\
  ifso_lookup_match version = Ssequence (ifso_lookup_type_read version)
    (Sifthenelse (Ebinop Oeq (Etempvar IFSOI._t'1 tuint)
      (Etempvar IFSOI._interactType tuint) tint)
      (Sreturn (Some (Etempvar IFSOI._object
        (tptr (Tstruct IFSOI._Object noattr))))) Sskip) /\
  direct_callees_s (fn_body (ifso_lookup version)) = [].

Theorem ifso_whole_collided_getter_reads_and_returns_cached_pointer :
  InkFallbackCachedLookupSource.
Proof. intros []; repeat split; reflexivity. Qed.

(** Locate the exact caller's getter-result transfer, rather than recording
    only an occurrence of the getter name. *)
Definition ifso_cached_getter_call_pair (body : statement) : bool := match body with
| Ssequence
    (Scall (Some result) (Evar callee _)
      [Etempvar mario _; Etempvar interact_type _])
    (Sset object (Etempvar returned_result _)) =>
    Pos.eqb callee IFSOI._mario_get_collided_object &&
    Pos.eqb mario IFSOI._m && Pos.eqb interact_type IFSOI._interactType &&
    Pos.eqb object IFSOI._object && Pos.eqb result returned_result
| _ => false end.
Definition ifso_cached_handler_call_pair (body : statement) : bool :=
  is_table_handler_call_then_break_s IFSOI._sInteractionHandlers IFSOI._handler body &&
  match body with
  | Ssequence (Ssequence _
      (Scall _ _ [Etempvar mario _; Etempvar interact_type _; Etempvar object _])) _ =>
      Pos.eqb mario IFSOI._m && Pos.eqb interact_type IFSOI._interactType &&
      Pos.eqb object IFSOI._object
  | _ => false end.
Fixpoint ifso_contains_source_cut_s (test : statement -> bool) (body : statement) : bool :=
  test body || match body with
  | Ssequence a b | Sloop a b =>
      ifso_contains_source_cut_s test a || ifso_contains_source_cut_s test b
  | Sifthenelse _ a b =>
      ifso_contains_source_cut_s test a || ifso_contains_source_cut_s test b
  | Sswitch _ cases => ifso_contains_source_cut_ls test cases
  | Slabel _ body => ifso_contains_source_cut_s test body
  | _ => false end
with ifso_contains_source_cut_ls (test : statement -> bool) (cases : labeled_statements) : bool :=
  match cases with
  | LSnil => false
  | LScons _ body rest =>
      ifso_contains_source_cut_s test body || ifso_contains_source_cut_ls test rest
  end.

Definition InkFallbackInteractionSource : Prop :=
  nonfading_warp_return_source_claim /\ interaction_nonzero_break_source_claim /\
  set_mario_action_return_source_claim /\
  forall version,
    ifso_contains_source_cut_s ifso_cached_getter_call_pair
      (fn_body (ifso_interactions version)) = true /\
    ifso_contains_source_cut_s ifso_cached_handler_call_pair
      (fn_body (ifso_interactions version)) = true /\
    direct_call_count IFSOI._mario_get_collided_object
      (fn_body (ifso_interactions version)) = 1%nat /\
    direct_call_count IFSOO._detect_object_collisions
      (fn_body (ifso_interactions version)) = 0%nat /\
    direct_call_count IFSOM._find_floor
      (fn_body (ifso_interactions version)) = 0%nat.

Theorem ifso_cached_contact_consumption_and_nonfading_short_circuit_source :
  InkFallbackInteractionSource.
Proof.
  split; [exact nonfading_warp_return_source_checked|].
  split; [exact interaction_nonzero_break_source_checked|].
  split; [exact set_mario_action_return_source_checked|].
  intros []; vm_compute; repeat split; reflexivity.
Qed.

Definition InkFallbackSourceOrderBoundary : Prop :=
  InkFallbackObjectSourceOrder /\ InkFallbackMarioSourceOrder /\
  InkFallbackInputSourceOrder /\ InkFallbackGeometrySourceOrder /\
  InkFallbackCachedLookupSource /\ InkFallbackInteractionSource.

Theorem ifso_generated_source_order_boundary_checked : InkFallbackSourceOrderBoundary.
Proof.
  split; [exact ifso_collision_precedes_nonterrain_in_generated_sequence|].
  split; [exact ifso_interactions_precede_exact_null_return_and_action_loop|].
  split; [exact ifso_inputs_import_cached_mask_before_geometry|].
  split; [exact ifso_first_floor_then_guarded_copy_retry_then_death_source|].
  split; [exact ifso_whole_collided_getter_reads_and_returns_cached_pointer|].
  exact ifso_cached_contact_consumption_and_nonfading_short_circuit_source.
Qed.

(** This frontier is reached only after mario_process_interactions. Its
    live floor load is an explicit premise, rather than a claim that NULL
    survived from geometry across special-floor and interaction calls. *)
Definition ifso_null_floor_temps version le mario :=
  PTree.set (ifso_floor_temp version) (Vint Int.zero)
    (PTree.set (ifso_state_temp version) (Vptr mario Ptrofs.zero) le).

Lemma ifso_selected_floor_field : forall version,
  ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IFSOM._MarioState IFSOM._floor 104 = true.
Proof.
  intro version. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Lemma ifso_null_floor_guard_true : forall ge e le memory version,
  le ! (ifso_floor_temp version) = Some (Vint Int.zero) ->
  eval_expr ge e le memory
    (Ebinop Oeq (Etempvar (ifso_floor_temp version)
      (tptr (Tstruct IFSOM._Surface noattr)))
      (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint)
    (Vint Int.one).
Proof.
  intros ge e le memory version Hfloor.
  eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vint Int.zero).
  - apply eval_Etempvar. exact Hfloor.
  - eapply eval_Ecast; [constructor|reflexivity].
  - reflexivity.
Qed.

Lemma ifso_construct_null_floor_return : forall version le memory cell mario,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IFSOM._gMarioState = Some cell ->
  Mem.load Mint32 memory cell 0 = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mint32 memory mario 104 = Some (Vint Int.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le memory
    (ifso_floor_check version) E0 (ifso_null_floor_temps version le mario)
    memory (Out_return (Some (Vint Int.zero, tint))).
Proof.
  intros version le memory cell mario Hsymbol Hglobal Hfloor.
  destruct (ifso_interactions_precede_exact_null_return_and_action_loop version)
    as (_ & _ & Hcheck & _).
  rewrite Hcheck. unfold ifso_null_floor_temps.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    (le1 := PTree.set (ifso_state_temp version) (Vptr mario Ptrofs.zero) le)
    (m1 := memory).
  - apply exec_Sset. eapply ias_global_read; eauto.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
      (le1 := PTree.set (ifso_floor_temp version) (Vint Int.zero)
        (PTree.set (ifso_state_temp version) (Vptr mario Ptrofs.zero) le))
      (m1 := memory).
    + apply exec_Sset. eapply ias_field_read with (chunk := Mint32) (offset := 104);
        [exact (ifso_selected_floor_field version)|reflexivity|apply PTree.gss|exact Hfloor].
    + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
      * apply ifso_null_floor_guard_true. apply PTree.gss.
      * reflexivity.
      * apply exec_Sreturn_some. constructor.
Qed.

(** The constructed return propagates through the exact remaining body.
    No execution premise for the action loop or its tail is required: the
    actual sequence return rule bypasses both. This is a suffix result,
    not a whole execute_mario_action call or failed-retry frame theorem. *)
Definition InkFallbackNullFloorExecution : Prop :=
  forall version le memory cell mario,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IFSOM._gMarioState = Some cell ->
  Mem.load Mint32 memory cell 0 = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mint32 memory mario 104 = Some (Vint Int.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le memory
    (iap_after_preparation version) E0 (ifso_null_floor_temps version le mario)
    memory (Out_return (Some (Vint Int.zero, tint))).

Theorem ifso_reached_null_floor_returns_before_dispatch : InkFallbackNullFloorExecution.
Proof.
  intros version le memory cell mario Hsymbol Hglobal Hfloor.
  assert (iap_after_preparation version =
    Ssequence (ifso_floor_check version)
      (Ssequence (ifso_action_loop version) (ifso_after_action_loop version)))
    as Hsource by (destruct version; reflexivity).
  rewrite Hsource. eapply exec_Sseq_2.
  - eapply ifso_construct_null_floor_return; eauto.
  - discriminate.
Qed.

Definition InkFallbackSourceOrderExecutionBoundary : Prop :=
  InkFallbackSourceOrderBoundary /\ InkFallbackNullFloorExecution.

Theorem ifso_source_order_and_null_floor_execution_checked :
  InkFallbackSourceOrderExecutionBoundary.
Proof.
  split; [exact ifso_generated_source_order_boundary_checked|].
  exact ifso_reached_null_floor_returns_before_dispatch.
Qed.
