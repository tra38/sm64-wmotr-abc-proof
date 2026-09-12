(** Finishing a rollout animation does not make ordinary freefall available.
    This is an execution theorem for the actual US/JP rollout endings and
    airborne dispatch, not a theorem that every elevator history stays there.
    The animation helper is resolved and proved read-only, including entry and
    return. Earlier movement, interactions and later scheduling remain outside
    this segment; no frame condition for those calls is assumed. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_mario jp_mario
  us_mario_actions_airborne jp_mario_actions_airborne.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts
  Area2Rank10AGroundPound Area2Rank12BContact UpperElevatorQueryResolution
  InkBackwardSource InkBackwardExecution InkBodyResetFrame InkCopyCaller
  InkControllerSource InkControllerEdge ObjectContactNecessity
  ContactConsumerExecution EyerokRank15LiveMovement
  SelectedClightTarget CleanedClightPrograms ClightLinkExecution
  GlobalInterfaceStructural JPSourceSymbolTransport JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module RGA := us_mario_actions_airborne.

Inductive RolloutDirection := RolloutForward | RolloutBackward.
Inductive RolloutGateNative := RGAnimationEnd | RGDispatch | RGRollout (d : RolloutDirection).
Definition rag_ident native := match native with
| RGAnimationEnd => us_mario._is_anim_past_end
| RGDispatch => RGA._mario_execute_airborne_action
| RGRollout RolloutForward => RGA._act_forward_rollout
| RGRollout RolloutBackward => RGA._act_backward_rollout end.
Definition rag_body version native := match version, native with
| VersionUS, RGAnimationEnd => us_mario.f_is_anim_past_end
| VersionJP, RGAnimationEnd => jp_mario.f_is_anim_past_end
| VersionUS, RGDispatch => RGA.f_mario_execute_airborne_action
| VersionJP, RGDispatch => jp_mario_actions_airborne.f_mario_execute_airborne_action
| VersionUS, RGRollout RolloutForward => RGA.f_act_forward_rollout
| VersionJP, RGRollout RolloutForward => jp_mario_actions_airborne.f_act_forward_rollout
| VersionUS, RGRollout RolloutBackward => RGA.f_act_backward_rollout
| VersionJP, RGRollout RolloutBackward => jp_mario_actions_airborne.f_act_backward_rollout end.
Definition rag_unit native : nat := match native with RGAnimationEnd => 1 | _ => 2 end.
Definition rag_definitions native := match native with
| RGAnimationEnd => us_mario.global_definitions | _ => RGA.global_definitions end.

Lemma rag_us_receipt : forall native,
  nth_error (rag_definitions native)
    (ueqr_definition_index (rag_ident native) (rag_definitions native)) =
  Some (rag_ident native, Gfun (Internal (rag_body VersionUS native))).
Proof. intros [| |[]]; vm_compute; reflexivity. Qed.
Lemma rag_us_unit : forall native,
  prog_defs (us_nlist_at (rag_unit native) us_units) = rag_definitions native.
Proof. intros [| |[]]; reflexivity. Qed.
Lemma rag_us_member : forall native,
  In (rag_ident native, Gfun (Internal (rag_body VersionUS native)))
    (unit_global_definitions us_units).
Proof.
  intro native. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (rag_unit native) us_units).
  - exact (us_nlist_at_nIn _ (rag_unit native) us_units).
  - rewrite rag_us_unit. eapply nth_error_In. exact (rag_us_receipt native).
Qed.
Lemma rag_us_selection : forall native,
  us_normalized_global_definition_map ! (rag_ident native) =
    Some (Gfun (Internal (rag_body VersionUS native))).
Proof.
  intro native. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (rag_us_member native).
Qed.
Lemma rag_us_no_repair : forall native,
  us_selected_definition_needs_viewport_repair
    (rag_ident native, Gfun (Internal (rag_body VersionUS native))) = false.
Proof. intros [| |[]]; vm_compute; reflexivity. Qed.
Lemma rag_us_selected : forall native,
  In (rag_ident native, Gfun (Internal (rag_body VersionUS native)))
    us_viewport_repaired_global_definitions.
Proof.
  intro native. unfold us_viewport_repaired_global_definitions.
  apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite rag_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (rag_us_selection native).
Qed.
Lemma rag_jp_receipt : forall native,
  (prog_defmap (nlist_at (rag_unit native) jp_cleaned_units)) ! (rag_ident native) =
    Some (Gfun (Internal (rag_body VersionJP native))).
Proof. intros [| |[]]; vm_compute; reflexivity. Qed.
Theorem rag_selected_bodies_resolve : forall version native,
  exists fb, Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    (rag_ident native) = Some fb /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb =
    Some (Internal (rag_body version native)).
Proof.
  intros [] native.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (rag_us_selected native).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (rag_unit native) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (rag_unit native) jp_cleaned_units).
    + exact (rag_jp_receipt native).
Qed.
