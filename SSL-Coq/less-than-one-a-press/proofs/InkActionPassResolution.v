(** Resolve the action-pass body in each actual selected program. *)
From Coq Require Import List.
From compcert Require Import AST Clight Ctypes Globalenvs Maps.
From LessThanOneAPress.Generated Require Import us_mario jp_mario.
From LessThanOneAPress.Proofs Require Import GameTypes InkActionPassHistory
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.

Lemma ias_us_action_source :
  nth_error us_mario.global_definitions
    (ueqr_definition_index us_mario._execute_mario_action us_mario.global_definitions) =
  Some (us_mario._execute_mario_action, Gfun (Internal (iap_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.

Lemma ias_us_action_member :
  In (us_mario._execute_mario_action, Gfun (Internal (iap_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 1 us_units).
  - exact (us_nlist_at_nIn _ 1 us_units).
  - eapply nth_error_In. exact ias_us_action_source.
Qed.

Lemma ias_us_action_selection :
  PTree.get us_mario._execute_mario_action us_normalized_global_definition_map =
    Some (Gfun (Internal (iap_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact ias_us_action_member.
Qed.

Lemma ias_us_action_no_repair : us_selected_definition_needs_viewport_repair
  (us_mario._execute_mario_action, Gfun (Internal (iap_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.

Lemma ias_us_action_selected_member :
  In (us_mario._execute_mario_action, Gfun (Internal (iap_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ias_us_action_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact ias_us_action_selection.
Qed.

Lemma ias_jp_action_source :
  PTree.get us_mario._execute_mario_action (prog_defmap (nlist_at 1 jp_cleaned_units)) =
    Some (Gfun (Internal (iap_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.

Theorem ias_selected_action_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_mario._execute_mario_action = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (iap_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ias_us_action_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 1 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 1 jp_cleaned_units).
    + exact ias_jp_action_source.
Qed.
