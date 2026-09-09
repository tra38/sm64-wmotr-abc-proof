(** The real late animation, sound and animation-loader bodies in both targets. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Ctypes Globalenvs Maps.
From LessThanOneAPress.Generated Require Import us_mario jp_mario us_memory jp_memory.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Inductive InkLateHelper := ILAnimation | ILLoad | ILSoundOnce | ILSoundAction | ILSoundParticles.
Definition ill_body version kind := match version, kind with
| VersionUS, ILAnimation => us_mario.f_set_mario_animation
| VersionJP, ILAnimation => jp_mario.f_set_mario_animation
| VersionUS, ILLoad => us_memory.f_load_patchable_table
| VersionJP, ILLoad => jp_memory.f_load_patchable_table
| VersionUS, ILSoundOnce => us_mario.f_play_mario_landing_sound_once
| VersionJP, ILSoundOnce => jp_mario.f_play_mario_landing_sound_once
| VersionUS, ILSoundAction => us_mario.f_play_mario_action_sound
| VersionJP, ILSoundAction => jp_mario.f_play_mario_action_sound
| VersionUS, ILSoundParticles => us_mario.f_play_sound_and_spawn_particles
| VersionJP, ILSoundParticles => jp_mario.f_play_sound_and_spawn_particles end.
Definition ill_ident kind := match kind with
| ILAnimation => IBM._set_mario_animation | ILLoad => IBM._load_patchable_table
| ILSoundOnce => IBM._play_mario_landing_sound_once
| ILSoundAction => IBM._play_mario_action_sound
| ILSoundParticles => IBM._play_sound_and_spawn_particles end.
Definition ill_unit_index kind := match kind with ILLoad => 21%nat | _ => 1%nat end.
Definition ill_us_definitions kind := match kind with
| ILLoad => us_memory.global_definitions | _ => us_mario.global_definitions end.

Lemma ill_us_source : forall kind,
  nth_error (ill_us_definitions kind)
    (ueqr_definition_index (ill_ident kind) (ill_us_definitions kind)) =
  Some (ill_ident kind, Gfun (Internal (ill_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ill_us_member : forall kind,
  In (ill_ident kind, Gfun (Internal (ill_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind.
  assert (prog_defs (us_nlist_at (ill_unit_index kind) us_units) =
    ill_us_definitions kind) as Hunit by (destruct kind; reflexivity).
  eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (ill_unit_index kind) us_units).
  - exact (us_nlist_at_nIn _ (ill_unit_index kind) us_units).
  - rewrite Hunit. eapply nth_error_In. exact (ill_us_source kind).
Qed.
Lemma ill_us_selection : forall kind,
  us_normalized_global_definition_map ! (ill_ident kind) =
    Some (Gfun (Internal (ill_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ill_us_member kind).
Qed.
Lemma ill_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ill_ident kind, Gfun (Internal (ill_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ill_us_selected_member : forall kind,
  In (ill_ident kind, Gfun (Internal (ill_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ill_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (ill_us_selection kind).
Qed.
Lemma ill_jp_source : forall kind,
  (prog_defmap (nlist_at (ill_unit_index kind) jp_cleaned_units)) ! (ill_ident kind) =
    Some (Gfun (Internal (ill_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem ill_selected_helpers_resolve : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ill_ident kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ill_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ill_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (ill_unit_index kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (ill_unit_index kind) jp_cleaned_units).
    + exact (ill_jp_source kind).
Qed.

Definition ill_mario_pointer := tptr (Tstruct IBM._MarioState noattr).
Definition ill_sound_type := Tfunction [tint; tptr tfloat] tvoid cc_default.
Definition ill_mario_sound_type := Tfunction [ill_mario_pointer; tuint; tuint] tvoid cc_default.

Theorem ill_empty_locals_and_original_argument : forall version kind,
  fn_vars (ill_body version kind) = [] /\
  exists rest, fn_params (ill_body version kind) =
    (match kind with ILLoad => (us_memory._list, tptr (Tstruct us_memory._DmaHandlerList noattr))
     | _ => (IBM._m, ill_mario_pointer) end) :: rest.
Proof. intros [] []; split; try reflexivity; eexists; reflexivity. Qed.
