(** The real object-copy callees used after Mario's ordinary copy.
    Resolve the selected US/JP definitions, rather than assuming a function
    with the right name has the expected body. *)
From Coq Require Import List.
From compcert Require Import AST Clight Clightdefs Ctypes Globalenvs Maps.
From LessThanOneAPress.Generated Require Import us_object_helpers jp_object_helpers.
From LessThanOneAPress.Proofs Require Import GameTypes
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Module PCC := us_object_helpers.
Inductive PostCopyChildHelper := PCCPosition | PCCAngle | PCCBoth.
Definition pcc_body version kind := match version, kind with
| VersionUS, PCCPosition => us_object_helpers.f_obj_copy_pos
| VersionJP, PCCPosition => jp_object_helpers.f_obj_copy_pos
| VersionUS, PCCAngle => us_object_helpers.f_obj_copy_angle
| VersionJP, PCCAngle => jp_object_helpers.f_obj_copy_angle
| VersionUS, PCCBoth => us_object_helpers.f_obj_copy_pos_and_angle
| VersionJP, PCCBoth => jp_object_helpers.f_obj_copy_pos_and_angle end.
Definition pcc_ident kind := match kind with
| PCCPosition => PCC._obj_copy_pos | PCCAngle => PCC._obj_copy_angle
| PCCBoth => PCC._obj_copy_pos_and_angle end.
Definition pcc_object := tptr (Tstruct PCC._Object noattr).
Definition pcc_type := Tfunction [pcc_object; pcc_object] tvoid cc_default.

Lemma pcc_us_source : forall kind,
  nth_error PCC.global_definitions
    (ueqr_definition_index (pcc_ident kind) PCC.global_definitions) =
  Some (pcc_ident kind, Gfun (Internal (pcc_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma pcc_us_member : forall kind,
  In (pcc_ident kind, Gfun (Internal (pcc_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at 19 us_units).
  - exact (us_nlist_at_nIn _ 19 us_units).
  - eapply nth_error_In. exact (pcc_us_source kind).
Qed.
Lemma pcc_us_selection : forall kind,
  us_normalized_global_definition_map ! (pcc_ident kind) =
    Some (Gfun (Internal (pcc_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (pcc_us_member kind).
Qed.
Lemma pcc_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (pcc_ident kind, Gfun (Internal (pcc_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma pcc_us_selected_member : forall kind,
  In (pcc_ident kind, Gfun (Internal (pcc_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite pcc_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (pcc_us_selection kind).
Qed.
Lemma pcc_jp_source : forall kind,
  (prog_defmap (nlist_at 19 jp_cleaned_units)) ! (pcc_ident kind) =
    Some (Gfun (Internal (pcc_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem pcc_selected_helpers_resolve : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (pcc_ident kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (pcc_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (pcc_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at 19 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 19 jp_cleaned_units).
    + exact (pcc_jp_source kind).
Qed.

Lemma pcc_params : forall version kind,
  fn_vars (pcc_body version kind) = [] /\
  fn_params (pcc_body version kind) = [(PCC._dst, pcc_object); (PCC._src, pcc_object)].
Proof. intros [] []; split; reflexivity. Qed.
