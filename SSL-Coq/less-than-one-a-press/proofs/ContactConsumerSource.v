(** Actual consumers of the recorded contact pair. These receipts select
    existing US/JP bodies; they do not assume a gameplay schedule or credit. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Coqlib Ctypes Globalenvs
  Integers Maps.
From LessThanOneAPress.Generated Require Import
  us_object_helpers jp_object_helpers us_interaction jp_interaction
  us_obj_behaviors jp_obj_behaviors.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank9AStarSource
  Area2Rank11PoleExitSplit Area2Rank11BodyResolution
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module CCH := us_object_helpers.
Module CCI := us_interaction.
Module CCB := us_obj_behaviors.

Inductive ContactConsumer :=
| CCPairSearch | CCStarSearch | CCSecret | CCSecretInit | CCStarDispatch.

Definition ccs_body version consumer : function := match version, consumer with
| VersionUS, CCPairSearch => us_object_helpers.f_obj_check_if_collided_with_object
| VersionJP, CCPairSearch => jp_object_helpers.f_obj_check_if_collided_with_object
| VersionUS, CCStarSearch => us_interaction.f_mario_get_collided_object
| VersionJP, CCStarSearch => jp_interaction.f_mario_get_collided_object
| VersionUS, CCSecret => us_obj_behaviors.f_bhv_hidden_star_trigger_loop
| VersionJP, CCSecret => jp_obj_behaviors.f_bhv_hidden_star_trigger_loop
| VersionUS, CCSecretInit => us_obj_behaviors.f_bhv_hidden_star_init
| VersionJP, CCSecretInit => jp_obj_behaviors.f_bhv_hidden_star_init
| VersionUS, CCStarDispatch => us_interaction.f_mario_process_interactions
| VersionJP, CCStarDispatch => jp_interaction.f_mario_process_interactions end.

Definition ccs_ident consumer := match consumer with
| CCPairSearch => CCH._obj_check_if_collided_with_object
| CCStarSearch => CCI._mario_get_collided_object
| CCSecret => CCB._bhv_hidden_star_trigger_loop
| CCSecretInit => CCB._bhv_hidden_star_init
| CCStarDispatch => CCI._mario_process_interactions end.
Definition ccs_unit consumer : nat := match consumer with
| CCPairSearch => 19 | CCStarSearch | CCStarDispatch => 10
| CCSecret | CCSecretInit => 23 end.
Definition ccs_us_definitions consumer := match consumer with
| CCPairSearch => us_object_helpers.global_definitions
| CCStarSearch | CCStarDispatch => us_interaction.global_definitions
| CCSecret | CCSecretInit => us_obj_behaviors.global_definitions end.

Lemma ccs_us_source_receipt : forall consumer,
  nth_error (ccs_us_definitions consumer)
    (rank11_definition_index (ccs_ident consumer) (ccs_us_definitions consumer)) =
  Some (ccs_ident consumer, Gfun (Internal (ccs_body VersionUS consumer))).
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma ccs_us_source_member : forall consumer,
  In (ccs_ident consumer, Gfun (Internal (ccs_body VersionUS consumer)))
    (unit_global_definitions us_units).
Proof.
  intro consumer. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (ccs_unit consumer) us_units).
  - exact (us_nlist_at_nIn _ (ccs_unit consumer) us_units).
  - destruct consumer; eapply nth_error_In.
    + exact (ccs_us_source_receipt CCPairSearch).
    + exact (ccs_us_source_receipt CCStarSearch).
    + exact (ccs_us_source_receipt CCSecret).
    + exact (ccs_us_source_receipt CCSecretInit).
    + exact (ccs_us_source_receipt CCStarDispatch).
Qed.

Lemma ccs_us_selection : forall consumer,
  us_normalized_global_definition_map ! (ccs_ident consumer) =
    Some (Gfun (Internal (ccs_body VersionUS consumer))).
Proof.
  intro consumer. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance
      (unit_global_definitions us_units)).
  - exact (ccs_us_source_member consumer).
Qed.

Lemma ccs_us_no_repair : forall consumer,
  us_selected_definition_needs_viewport_repair
    (ccs_ident consumer, Gfun (Internal (ccs_body VersionUS consumer))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma ccs_us_selected_member : forall consumer,
  In (ccs_ident consumer, Gfun (Internal (ccs_body VersionUS consumer)))
    us_viewport_repaired_global_definitions.
Proof.
  intro consumer. unfold us_viewport_repaired_global_definitions.
  apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ccs_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim.
    exact (ccs_us_selection consumer).
Qed.

Lemma ccs_jp_source_receipt : forall consumer,
  (prog_defmap (nlist_at (ccs_unit consumer) jp_cleaned_units)) !
    (ccs_ident consumer) = Some (Gfun (Internal (ccs_body VersionJP consumer))).
Proof. intros []; vm_compute; reflexivity. Qed.

Theorem ccs_selected_consumer_resolves : forall version consumer,
  exists function_block,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      (ccs_ident consumer) = Some function_block /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
      function_block = Some (Internal (ccs_body version consumer)).
Proof.
  intros [] consumer.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ccs_us_selected_member consumer).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (ccs_unit consumer) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (ccs_unit consumer) jp_cleaned_units).
    + exact (ccs_jp_source_receipt consumer).
Qed.

(** Shared extraction of the two actual search loops. No bound on the number
    of iterations, memory contents, or controller inputs is inserted here. *)
Definition ccs_search_loop version consumer :=
  match fn_body (ccs_body version consumer) with
  | Ssequence (Ssequence _ loop) _ => loop | _ => Sskip end.
Definition ccs_search_iteration version consumer :=
  match ccs_search_loop version consumer with
  | Sloop iteration _ => iteration | _ => Sskip end.
Definition ccs_search_increment version consumer :=
  match ccs_search_loop version consumer with
  | Sloop _ increment => increment | _ => Sskip end.
Definition ccs_search_fallback version consumer :=
  match fn_body (ccs_body version consumer) with
  | Ssequence _ fallback => fallback | _ => Sskip end.

Theorem ccs_search_body_shape : forall version consumer,
  consumer = CCPairSearch \/ consumer = CCStarSearch ->
  fn_body (ccs_body version consumer) =
    Ssequence (Ssequence (Sset CCH._i (Econst_int Int.zero tint))
      (Sloop (ccs_search_iteration version consumer)
        (ccs_search_increment version consumer)))
      (ccs_search_fallback version consumer).
Proof. intros [] consumer [H | H]; subst consumer; reflexivity. Qed.
