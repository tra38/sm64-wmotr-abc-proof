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

Inductive InkCancelHelper := ICPush | ICJump | ICTriple.
Definition icz_body version kind := match version, kind with
| VersionUS, ICPush => us_mario_step.f_mario_push_off_steep_floor
| VersionJP, ICPush => jp_mario_step.f_mario_push_off_steep_floor
| VersionUS, ICJump => us_mario.f_set_jumping_action
| VersionJP, ICJump => jp_mario.f_set_jumping_action
| VersionUS, ICTriple => us_mario_actions_moving.f_set_triple_jump_action
| VersionJP, ICTriple => jp_mario_actions_moving.f_set_triple_jump_action end.
Definition icz_ident kind := match kind with
| ICPush => IMB._mario_push_off_steep_floor
| ICJump => IMB._set_jumping_action
| ICTriple => IMB._set_triple_jump_action end.
Definition icz_unit kind : nat := match kind with ICPush => 9 | ICJump => 1 | ICTriple => 5 end.
Definition icz_us_definitions kind := match kind with
| ICPush => us_mario_step.global_definitions
| ICJump => us_mario.global_definitions
| ICTriple => us_mario_actions_moving.global_definitions end.
Lemma icz_us_source : forall kind,
  nth_error (icz_us_definitions kind)
    (ueqr_definition_index (icz_ident kind) (icz_us_definitions kind)) =
  Some (icz_ident kind, Gfun (Internal (icz_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma icz_us_member : forall kind,
  In (icz_ident kind, Gfun (Internal (icz_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind.
  assert (prog_defs (us_nlist_at (icz_unit kind) us_units) =
    icz_us_definitions kind) as Hunit by (destruct kind; reflexivity).
  eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (icz_unit kind) us_units).
  - exact (us_nlist_at_nIn _ (icz_unit kind) us_units).
  - rewrite Hunit. eapply nth_error_In. exact (icz_us_source kind).
Qed.
Lemma icz_us_selection : forall kind,
  us_normalized_global_definition_map ! (icz_ident kind) =
    Some (Gfun (Internal (icz_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (icz_us_member kind).
Qed.
Lemma icz_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (icz_ident kind, Gfun (Internal (icz_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma icz_us_selected_member : forall kind,
  In (icz_ident kind, Gfun (Internal (icz_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite icz_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (icz_us_selection kind).
Qed.
Lemma icz_jp_source : forall kind,
  (prog_defmap (nlist_at (icz_unit kind) jp_cleaned_units)) ! (icz_ident kind) =
    Some (Gfun (Internal (icz_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem icz_selected_helpers_resolve : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (icz_ident kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (icz_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (icz_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (icz_unit kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (icz_unit kind) jp_cleaned_units).
    + exact (icz_jp_source kind).
Qed.
