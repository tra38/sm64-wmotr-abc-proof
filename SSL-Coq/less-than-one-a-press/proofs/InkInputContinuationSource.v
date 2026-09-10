(** Selected, unmodified input/angle helpers used after the button call. *)
From Coq Require Import List.
From compcert Require Import AST Clight Clightdefs Ctypes Globalenvs Maps.
From LessThanOneAPress.Generated Require Import us_mario jp_mario us_math_util jp_math_util.
From LessThanOneAPress.Proofs Require Import GameTypes InkControllerSource
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SelectedClightTarget SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Inductive InkInputHelper := IIJoystick | IIGeometry | IIAngle | IILookup.
Definition iis_body version kind := match version, kind with
| VersionUS, IIJoystick => us_mario.f_update_mario_joystick_inputs
| VersionJP, IIJoystick => jp_mario.f_update_mario_joystick_inputs
| VersionUS, IIGeometry => us_mario.f_update_mario_geometry_inputs
| VersionJP, IIGeometry => jp_mario.f_update_mario_geometry_inputs
| VersionUS, IIAngle => us_math_util.f_atan2s
| VersionJP, IIAngle => jp_math_util.f_atan2s
| VersionUS, IILookup => us_math_util.f_atan2_lookup
| VersionJP, IILookup => jp_math_util.f_atan2_lookup end.
Definition iis_ident kind := match kind with
| IIJoystick => us_mario._update_mario_joystick_inputs
| IIGeometry => us_mario._update_mario_geometry_inputs
| IIAngle => us_math_util._atan2s
| IILookup => us_math_util._atan2_lookup end.
Definition iis_unit kind : nat := match kind with
| IIJoystick | IIGeometry => 1 | _ => 30 end.
Definition iis_us_definitions kind := match kind with
| IIJoystick | IIGeometry => us_mario.global_definitions
| _ => us_math_util.global_definitions end.

Lemma iis_us_source : forall kind,
  nth_error (iis_us_definitions kind)
    (ueqr_definition_index (iis_ident kind) (iis_us_definitions kind)) =
  Some (iis_ident kind, Gfun (Internal (iis_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma iis_us_member : forall kind,
  In (iis_ident kind, Gfun (Internal (iis_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (iis_unit kind) us_units).
  - exact (us_nlist_at_nIn _ (iis_unit kind) us_units).
  - destruct kind; eapply nth_error_In.
    + exact (iis_us_source IIJoystick).
    + exact (iis_us_source IIGeometry).
    + exact (iis_us_source IIAngle).
    + exact (iis_us_source IILookup).
Qed.
Lemma iis_us_selection : forall kind,
  us_normalized_global_definition_map ! (iis_ident kind) =
    Some (Gfun (Internal (iis_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (iis_us_member kind).
Qed.
Lemma iis_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (iis_ident kind, Gfun (Internal (iis_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma iis_us_selected_member : forall kind,
  In (iis_ident kind, Gfun (Internal (iis_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite iis_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (iis_us_selection kind).
Qed.
Lemma iis_jp_source : forall kind,
  (prog_defmap (nlist_at (iis_unit kind) jp_cleaned_units)) ! (iis_ident kind) =
    Some (Gfun (Internal (iis_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem iis_selected_helpers_resolve : forall version kind,
  exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (iis_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (iis_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (iis_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (iis_unit kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (iis_unit kind) jp_cleaned_units).
    + exact (iis_jp_source kind).
Qed.

Lemma iis_helpers_have_no_stack_objects : forall version kind,
  fn_vars (iis_body version kind) = [].
Proof. intros [] []; reflexivity. Qed.
