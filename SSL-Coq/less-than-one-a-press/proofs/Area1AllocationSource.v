(** The real object allocator and its callers in the selected US/JP target. *)
From Coq Require Import List.
From compcert Require Import AST Clight Clightdefs Ctypes Globalenvs Maps.
From LessThanOneAPress.Generated Require Import us_spawn_object jp_spawn_object
  us_object_helpers jp_object_helpers us_math_util jp_math_util.
From LessThanOneAPress.Proofs Require Import GameTypes
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module PAS := us_spawn_object.
Module PAH := us_object_helpers.
Inductive PostCopyAllocator := PATry | PAAllocate | PAFind | PACreate | PASpawn | PAIdentity.
Definition pas_body version kind := match version, kind with
| VersionUS, PATry => us_spawn_object.f_try_allocate_object
| VersionJP, PATry => jp_spawn_object.f_try_allocate_object
| VersionUS, PAAllocate => us_spawn_object.f_allocate_object
| VersionJP, PAAllocate => jp_spawn_object.f_allocate_object
| VersionUS, PAFind => us_object_helpers.f_find_unimportant_object
| VersionJP, PAFind => jp_object_helpers.f_find_unimportant_object
| VersionUS, PACreate => us_spawn_object.f_create_object
| VersionJP, PACreate => jp_spawn_object.f_create_object
| VersionUS, PASpawn => us_object_helpers.f_spawn_object_at_origin
| VersionJP, PASpawn => jp_object_helpers.f_spawn_object_at_origin
| VersionUS, PAIdentity => us_math_util.f_mtxf_identity
| VersionJP, PAIdentity => jp_math_util.f_mtxf_identity end.
Definition pas_ident kind := match kind with
| PATry => PAS._try_allocate_object | PAAllocate => PAS._allocate_object
| PAFind => PAH._find_unimportant_object | PACreate => PAS._create_object
| PASpawn => PAH._spawn_object_at_origin | PAIdentity => us_math_util._mtxf_identity end.
Definition pas_unit_index kind := match kind with PAFind | PASpawn => 19%nat | PAIdentity => 30%nat | _ => 18%nat end.
Definition pas_us_definitions kind := match kind with
| PAFind | PASpawn => us_object_helpers.global_definitions
| PAIdentity => us_math_util.global_definitions | _ => us_spawn_object.global_definitions end.
Lemma pas_us_source : forall kind,
  nth_error (pas_us_definitions kind)
    (ueqr_definition_index (pas_ident kind) (pas_us_definitions kind)) =
  Some (pas_ident kind, Gfun (Internal (pas_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma pas_us_member : forall kind,
  In (pas_ident kind, Gfun (Internal (pas_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind.
  assert (prog_defs (us_nlist_at (pas_unit_index kind) us_units) =
    pas_us_definitions kind) as Hunit by (destruct kind; reflexivity).
  eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (pas_unit_index kind) us_units).
  - exact (us_nlist_at_nIn _ (pas_unit_index kind) us_units).
  - rewrite Hunit. eapply nth_error_In. exact (pas_us_source kind).
Qed.
Lemma pas_us_selection : forall kind,
  us_normalized_global_definition_map ! (pas_ident kind) =
    Some (Gfun (Internal (pas_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (pas_us_member kind).
Qed.
Lemma pas_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (pas_ident kind, Gfun (Internal (pas_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma pas_us_selected_member : forall kind,
  In (pas_ident kind, Gfun (Internal (pas_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite pas_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (pas_us_selection kind).
Qed.
Lemma pas_jp_source : forall kind,
  (prog_defmap (nlist_at (pas_unit_index kind) jp_cleaned_units)) ! (pas_ident kind) =
    Some (Gfun (Internal (pas_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem pas_selected_helpers_resolve : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (pas_ident kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (pas_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (pas_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (pas_unit_index kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (pas_unit_index kind) jp_cleaned_units).
    + exact (pas_jp_source kind).
Qed.
