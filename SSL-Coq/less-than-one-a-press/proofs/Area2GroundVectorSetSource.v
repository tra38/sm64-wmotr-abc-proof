(** Conditional Rank-10A ground alignment. The live query answers remain
    premises; the generated vector setter and post-alignment wall handling
    do not. No assumption says that a completed quarter aligns Mario. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_math_util jp_math_util.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank10ABlockedStep Area2Rank12BContact
  InkFloorHistorySource InkFloorHistoryExecution InkFloorHistoryCall InkFloorHistoryQuery
  InkBackwardSource InkBackwardExecution InkCopyEntry InkCopyCaller
  InkCopyCompletion InkRetryCompletion InkFloorResetExecution InkFloorResetSource
  InkInputContinuationSource InkInputAngleFrame ObjectContactNecessity
  ContactConsumerExecution SecretContactExecution SelectedClightTarget
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition rank10g_set_body version := match version with
| VersionUS => us_math_util.f_vec3f_set
| VersionJP => jp_math_util.f_vec3f_set end.

Lemma rank10g_set_us_source :
  nth_error IBV.global_definitions
    (ueqr_definition_index IBV._vec3f_set IBV.global_definitions) =
  Some (IBV._vec3f_set, Gfun (Internal (rank10g_set_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma rank10g_set_us_member :
  In (IBV._vec3f_set, Gfun (Internal (rank10g_set_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at 30 us_units).
  - exact (us_nlist_at_nIn _ 30 us_units).
  - eapply nth_error_In. exact rank10g_set_us_source.
Qed.
Lemma rank10g_set_us_selection :
  us_normalized_global_definition_map ! IBV._vec3f_set =
    Some (Gfun (Internal (rank10g_set_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance
      (unit_global_definitions us_units)).
  - exact rank10g_set_us_member.
Qed.
Lemma rank10g_set_us_no_repair :
  us_selected_definition_needs_viewport_repair
    (IBV._vec3f_set, Gfun (Internal (rank10g_set_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma rank10g_set_us_selected :
  In (IBV._vec3f_set, Gfun (Internal (rank10g_set_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite rank10g_set_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim.
    exact rank10g_set_us_selection.
Qed.
Lemma rank10g_set_jp_source :
  (prog_defmap (nlist_at 30 jp_cleaned_units)) ! IBV._vec3f_set =
    Some (Gfun (Internal (rank10g_set_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem rank10g_selected_set_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IBV._vec3f_set = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (rank10g_set_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact rank10g_set_us_selected.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 30 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 30 jp_cleaned_units).
    + exact rank10g_set_jp_source.
Qed.
