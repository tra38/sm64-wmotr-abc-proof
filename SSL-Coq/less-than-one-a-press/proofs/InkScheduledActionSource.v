(** Resolve the actual behavior-command and Mario callback bodies.  These
    are internal functions, not assumed outside-call effects. *)
From Coq Require Import List.
From compcert Require Import AST Clight Ctypes Globalenvs Maps.
From LessThanOneAPress.Generated Require Import us_object_list_processor
  jp_object_list_processor us_behavior_script jp_behavior_script.
From LessThanOneAPress.Proofs Require Import GameTypes
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.

Module ISC := us_object_list_processor.
Module ISN := us_behavior_script.
Inductive InkScheduledHelper := ISMarioCallback | ISNativeCommand.
Definition ish_body version kind := match version, kind with
| VersionUS, ISMarioCallback => ISC.f_bhv_mario_update
| VersionJP, ISMarioCallback => jp_object_list_processor.f_bhv_mario_update
| VersionUS, ISNativeCommand => ISN.f_bhv_cmd_call_native
| VersionJP, ISNativeCommand => jp_behavior_script.f_bhv_cmd_call_native end.
Definition ish_ident kind := match kind with
| ISMarioCallback => ISC._bhv_mario_update
| ISNativeCommand => ISN._bhv_cmd_call_native end.
Definition ish_unit_index kind := match kind with
| ISMarioCallback => 13%nat | ISNativeCommand => 14%nat end.
Definition ish_us_definitions kind := match kind with
| ISMarioCallback => ISC.global_definitions
| ISNativeCommand => ISN.global_definitions end.

Lemma ish_us_source : forall kind,
  nth_error (ish_us_definitions kind)
    (ueqr_definition_index (ish_ident kind) (ish_us_definitions kind)) =
  Some (ish_ident kind, Gfun (Internal (ish_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma ish_us_member : forall kind,
  In (ish_ident kind, Gfun (Internal (ish_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind.
  assert (prog_defs (us_nlist_at (ish_unit_index kind) us_units) =
    ish_us_definitions kind) as Hunit by (destruct kind; reflexivity).
  eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (ish_unit_index kind) us_units).
  - exact (us_nlist_at_nIn _ (ish_unit_index kind) us_units).
  - rewrite Hunit. eapply nth_error_In. exact (ish_us_source kind).
Qed.

Lemma ish_us_selection : forall kind,
  us_normalized_global_definition_map ! (ish_ident kind) =
    Some (Gfun (Internal (ish_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ish_us_member kind).
Qed.

Lemma ish_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ish_ident kind, Gfun (Internal (ish_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.

Lemma ish_us_selected_member : forall kind,
  In (ish_ident kind, Gfun (Internal (ish_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ish_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (ish_us_selection kind).
Qed.

Lemma ish_jp_source : forall kind,
  (prog_defmap (nlist_at (ish_unit_index kind) jp_cleaned_units)) ! (ish_ident kind) =
    Some (Gfun (Internal (ish_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.

Theorem ish_selected_helpers_resolve : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ish_ident kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ish_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ish_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (ish_unit_index kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (ish_unit_index kind) jp_cleaned_units).
    + exact (ish_jp_source kind).
Qed.
