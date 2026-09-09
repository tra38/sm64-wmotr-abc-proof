(** Actual ordinary downward floor snaps and their following display reset.
    Both paths are extracted from generated code, not a movement model. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Globalenvs Integers Maps.
From LessThanOneAPress.Generated Require Import us_mario_step jp_mario_step.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkCopyCaller ObjectContactNecessity Area2Rank12BContact
  UpperElevatorQueryResolution ContactConsumerSource
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module IFR := us_mario_step.

Inductive InkFloorReset := IFRStop | IFRStationary.
Definition ifr_body version kind := match version, kind with
| VersionUS, IFRStop => us_mario_step.f_stop_and_set_height_to_floor
| VersionJP, IFRStop => jp_mario_step.f_stop_and_set_height_to_floor
| VersionUS, IFRStationary => us_mario_step.f_stationary_ground_step
| VersionJP, IFRStationary => jp_mario_step.f_stationary_ground_step end.
Definition ifr_ident kind := match kind with
| IFRStop => IFR._stop_and_set_height_to_floor
| IFRStationary => IFR._stationary_ground_step end.

Lemma ifr_us_source : forall kind,
  nth_error IFR.global_definitions
    (ueqr_definition_index (ifr_ident kind) IFR.global_definitions) =
  Some (ifr_ident kind, Gfun (Internal (ifr_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma ifr_us_member : forall kind,
  In (ifr_ident kind, Gfun (Internal (ifr_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intros kind. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at 9 us_units).
  - exact (us_nlist_at_nIn _ 9 us_units).
  - eapply nth_error_In. exact (ifr_us_source kind).
Qed.

Lemma ifr_us_selection : forall kind,
  us_normalized_global_definition_map ! (ifr_ident kind) =
    Some (Gfun (Internal (ifr_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ifr_us_member kind).
Qed.

Lemma ifr_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ifr_ident kind, Gfun (Internal (ifr_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma ifr_us_selected_member : forall kind,
  In (ifr_ident kind, Gfun (Internal (ifr_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions.
  apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ifr_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (ifr_us_selection kind).
Qed.

Lemma ifr_jp_source : forall kind,
  (prog_defmap (nlist_at 9 jp_cleaned_units)) ! (ifr_ident kind) =
    Some (Gfun (Internal (ifr_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.

Theorem ifr_selected_bodies_resolve : forall version kind,
  exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      (ifr_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ifr_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ifr_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 9 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 9 jp_cleaned_units).
    + exact (ifr_jp_source kind).
Qed.

Definition ifr_prefix_count kind := match kind with IFRStop => 2%nat | IFRStationary => 4%nat end.
Definition ifr_prefix version kind := ocn_prefix_items (ifr_prefix_count kind)
  (rank12b_drop_sequences 1 (fn_body (ifr_body version kind))).
Definition ifr_after_prefix version kind := rank12b_drop_sequences
  (S (ifr_prefix_count kind)) (fn_body (ifr_body version kind)).
Definition ifr_stationary_choice version := ibk_head (ifr_after_prefix version IFRStationary).
Definition ifr_moving_branch version := match ifr_stationary_choice version with
| Sifthenelse _ yes _ => yes | _ => Sskip end.
Definition ifr_reset_tail version kind := match kind with
| IFRStop => ifr_after_prefix version IFRStop
| IFRStationary => match ifr_stationary_choice version with
    | Sifthenelse _ _ no => no | _ => Sskip end end.
Definition ifr_snap version kind := ibk_head (ifr_reset_tail version kind).
Definition ifr_copy_call version kind := ibk_head
  (rank12b_drop_sequences 1 (ifr_reset_tail version kind)).
Definition ifr_after_copy version kind := rank12b_drop_sequences 2 (ifr_reset_tail version kind).
Definition ifr_floor_temp kind := match kind with IFRStop => IFR._t'2 | IFRStationary => IFR._t'5 end.
Definition ifr_floor_read := Efield ibcc_state IFR._floorHeight tfloat.
Definition ifr_y_cell := Ederef (Ebinop Oadd ibcc_destination
  (Econst_int (Int.repr 1) tint) (tptr tfloat)) tfloat.
Definition ifr_object := Ederef (Etempvar IFR._marioObj (tptr (Tstruct IFR._Object noattr)))
  (Tstruct IFR._Object noattr).
Definition ifr_graphics := Efield (Efield ifr_object IFR._header
  (Tstruct IFR._ObjectNode noattr)) IFR._gfx (Tstruct IFR._GraphNodeObject noattr).
Definition ifr_graphics_position := Efield ifr_graphics IFR._pos (tarray tfloat 3).

Theorem ifr_source_cuts : forall version kind,
  fn_vars (ifr_body version kind) = [] /\
  fn_body (ifr_body version kind) =
    Ssequence (Sset IFR._marioObj ibk_object_read)
      (ocn_prepend (ifr_prefix version kind) (ifr_after_prefix version kind)) /\
  ifr_reset_tail version kind = Ssequence (ifr_snap version kind)
    (Ssequence (ifr_copy_call version kind) (ifr_after_copy version kind)) /\
  ifr_snap version kind = Ssequence (Sset (ifr_floor_temp kind) ifr_floor_read)
    (Sassign ifr_y_cell (Etempvar (ifr_floor_temp kind) tfloat)) /\
  ifr_copy_call version kind = Scall None
    (Evar IFR._vec3f_copy (Tfunction [tptr tfloat; tptr tfloat] (tptr tvoid) cc_default))
    [ifr_graphics_position; ibcc_destination].
Proof. intros [] []; repeat split; reflexivity. Qed.

Theorem ifr_stationary_split_source : forall version,
  ifr_after_prefix version IFRStationary =
    Ssequence (Sifthenelse (Etempvar IFR._takeStep tuint)
      (ifr_moving_branch version) (ifr_reset_tail version IFRStationary))
      (Sreturn (Some (Etempvar IFR._stepResult tuint))).
Proof. intros []; reflexivity. Qed.
