(** Exact generated platform-displacement callees, resolved in both selected programs. *)
From Coq Require Import List.
From compcert Require Import AST Clight Clightdefs Ctypes Globalenvs Maps.
From LessThanOneAPress.Generated Require Import us_platform_displacement jp_platform_displacement us_math_util jp_math_util
  us_object_helpers jp_object_helpers.
From LessThanOneAPress.Proofs Require Import GameTypes InkControllerSource
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SelectedClightTarget SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Inductive InkPlatformLeaf := IPLGet | IPLSet | IPLMatrix | IPLMultiply | IPLTranspose.
Definition ipm_body version (kind : option InkPlatformLeaf) :=
  match version, kind with
  | VersionUS, None => us_platform_displacement.f_apply_platform_displacement
  | VersionJP, None => jp_platform_displacement.f_apply_platform_displacement
  | VersionUS, Some IPLGet => us_platform_displacement.f_get_mario_pos
  | VersionJP, Some IPLGet => jp_platform_displacement.f_get_mario_pos
  | VersionUS, Some IPLSet => us_platform_displacement.f_set_mario_pos
  | VersionJP, Some IPLSet => jp_platform_displacement.f_set_mario_pos
  | VersionUS, Some IPLMatrix => us_math_util.f_mtxf_rotate_zxy_and_translate
  | VersionJP, Some IPLMatrix => jp_math_util.f_mtxf_rotate_zxy_and_translate
  | VersionUS, Some IPLMultiply => us_object_helpers.f_linear_mtxf_mul_vec3f
  | VersionJP, Some IPLMultiply => jp_object_helpers.f_linear_mtxf_mul_vec3f
  | VersionUS, Some IPLTranspose => us_object_helpers.f_linear_mtxf_transpose_mul_vec3f
  | VersionJP, Some IPLTranspose => jp_object_helpers.f_linear_mtxf_transpose_mul_vec3f
  end.
Definition ipm_ident kind := match kind with
| None => us_platform_displacement._apply_platform_displacement
| Some IPLGet => us_platform_displacement._get_mario_pos
| Some IPLSet => us_platform_displacement._set_mario_pos
| Some IPLMatrix => us_math_util._mtxf_rotate_zxy_and_translate
| Some IPLMultiply => us_object_helpers._linear_mtxf_mul_vec3f
| Some IPLTranspose => us_object_helpers._linear_mtxf_transpose_mul_vec3f end.
Definition ipm_unit kind : nat := match kind with
| Some IPLMatrix => 30 | Some IPLMultiply | Some IPLTranspose => 19 | _ => 29 end.
Definition ipm_us_definitions kind := match kind with
| Some IPLMatrix => us_math_util.global_definitions
| Some IPLMultiply | Some IPLTranspose => us_object_helpers.global_definitions
| _ => us_platform_displacement.global_definitions end.

Lemma ipm_us_source : forall kind,
  nth_error (ipm_us_definitions kind)
    (ueqr_definition_index (ipm_ident kind) (ipm_us_definitions kind)) =
  Some (ipm_ident kind, Gfun (Internal (ipm_body VersionUS kind))).
Proof. intros [[]|]; vm_compute; reflexivity. Qed.
Lemma ipm_us_member : forall kind,
  In (ipm_ident kind, Gfun (Internal (ipm_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (ipm_unit kind) us_units).
  - exact (us_nlist_at_nIn _ (ipm_unit kind) us_units).
  - destruct kind as [[]|]; eapply nth_error_In.
    + exact (ipm_us_source (Some IPLGet)).
    + exact (ipm_us_source (Some IPLSet)).
    + exact (ipm_us_source (Some IPLMatrix)).
    + exact (ipm_us_source (Some IPLMultiply)).
    + exact (ipm_us_source (Some IPLTranspose)).
    + exact (ipm_us_source None).
Qed.
Lemma ipm_us_selection : forall kind,
  us_normalized_global_definition_map ! (ipm_ident kind) =
    Some (Gfun (Internal (ipm_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ipm_us_member kind).
Qed.
Lemma ipm_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ipm_ident kind, Gfun (Internal (ipm_body VersionUS kind))) = false.
Proof. intros [[]|]; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma ipm_us_selected_member : forall kind,
  In (ipm_ident kind, Gfun (Internal (ipm_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ipm_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (ipm_us_selection kind).
Qed.
Lemma ipm_jp_source : forall kind,
  (prog_defmap (nlist_at (ipm_unit kind) jp_cleaned_units)) ! (ipm_ident kind) =
    Some (Gfun (Internal (ipm_body VersionJP kind))).
Proof. intros [[]|]; vm_compute; reflexivity. Qed.
Theorem ipm_selected_helpers_resolve : forall version kind,
  exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ipm_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ipm_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ipm_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (ipm_unit kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (ipm_unit kind) jp_cleaned_units).
    + exact (ipm_jp_source kind).
Qed.


Lemma ipm_leaf_vars : forall version kind, fn_vars (ipm_body version (Some kind)) = [].
Proof. intros [] []; reflexivity. Qed.
Lemma ipm_leaf_params : forall version kind,
  fn_params (ipm_body version (Some kind)) = fn_params (ipm_body VersionUS (Some kind)).
Proof. intros [] []; reflexivity. Qed.
