(** Resolve the four stock action initializers in the actual selected programs. *)
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

Inductive InkActionInitializer := IAIAir | IAIMoving | IAISubmerged | IAICutscene.
Definition iai_body version kind := match version, kind with
| VersionUS, IAIAir => us_mario.f_set_mario_action_airborne
| VersionJP, IAIAir => jp_mario.f_set_mario_action_airborne
| VersionUS, IAIMoving => us_mario.f_set_mario_action_moving
| VersionJP, IAIMoving => jp_mario.f_set_mario_action_moving
| VersionUS, IAISubmerged => us_mario.f_set_mario_action_submerged
| VersionJP, IAISubmerged => jp_mario.f_set_mario_action_submerged
| VersionUS, IAICutscene => us_mario.f_set_mario_action_cutscene
| VersionJP, IAICutscene => jp_mario.f_set_mario_action_cutscene end.
Definition iai_ident kind := match kind with
| IAIAir => IBM._set_mario_action_airborne
| IAIMoving => IBM._set_mario_action_moving
| IAISubmerged => IBM._set_mario_action_submerged
| IAICutscene => IBM._set_mario_action_cutscene end.
Definition iai_unit (_ : InkActionInitializer) : nat := 1.
Definition iai_us_definitions (_ : InkActionInitializer) := us_mario.global_definitions.
Lemma iai_us_source : forall kind,
  nth_error (iai_us_definitions kind)
    (ueqr_definition_index (iai_ident kind) (iai_us_definitions kind)) =
  Some (iai_ident kind, Gfun (Internal (iai_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma iai_us_member : forall kind,
  In (iai_ident kind, Gfun (Internal (iai_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind.
  assert (prog_defs (us_nlist_at (iai_unit kind) us_units) =
    iai_us_definitions kind) as Hunit by (destruct kind; reflexivity).
  eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (iai_unit kind) us_units).
  - exact (us_nlist_at_nIn _ (iai_unit kind) us_units).
  - rewrite Hunit. eapply nth_error_In. exact (iai_us_source kind).
Qed.
Lemma iai_us_selection : forall kind,
  us_normalized_global_definition_map ! (iai_ident kind) =
    Some (Gfun (Internal (iai_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (iai_us_member kind).
Qed.
Lemma iai_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (iai_ident kind, Gfun (Internal (iai_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definitions normalize_global_definition_map.
Lemma iai_us_selected_member : forall kind,
  In (iai_ident kind, Gfun (Internal (iai_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite iai_us_no_repair. reflexivity.
  - unfold us_normalized_global_definitions.
    pose proof (iai_us_selection kind) as Hselected.
    unfold us_normalized_global_definition_map in Hselected.
    exact (every_selected_internal_body_is_preserved_verbatim
      (unit_global_definitions us_units) (iai_ident kind) (iai_body VersionUS kind)
      Hselected).
Qed.
Lemma iai_jp_source : forall kind,
  (prog_defmap (nlist_at (iai_unit kind) jp_cleaned_units)) ! (iai_ident kind) =
    Some (Gfun (Internal (iai_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem iai_selected_helpers_resolve : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (iai_ident kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (iai_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (iai_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (iai_unit kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (iai_unit kind) jp_cleaned_units).
    + exact (iai_jp_source kind).
Qed.

