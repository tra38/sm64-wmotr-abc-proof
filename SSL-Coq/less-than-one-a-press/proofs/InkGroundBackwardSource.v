(** The real ground-step display refresh, after the quarter-step loop. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Ctypes Globalenvs Maps.
From LessThanOneAPress.Generated Require Import us_mario_step jp_mario_step.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkFloorResetSource ObjectContactNecessity
  Area2Rank12BContact UpperElevatorQueryResolution ContactConsumerSource
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition igb_body version := match version with
| VersionUS => us_mario_step.f_perform_ground_step
| VersionJP => jp_mario_step.f_perform_ground_step end.

Lemma igb_us_source :
  nth_error IFR.global_definitions
    (ueqr_definition_index IFR._perform_ground_step IFR.global_definitions) =
  Some (IFR._perform_ground_step, Gfun (Internal (igb_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma igb_us_member :
  In (IFR._perform_ground_step, Gfun (Internal (igb_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 9 us_units).
  - exact (us_nlist_at_nIn _ 9 us_units).
  - eapply nth_error_In. exact igb_us_source.
Qed.
Lemma igb_us_selection :
  us_normalized_global_definition_map ! IFR._perform_ground_step =
    Some (Gfun (Internal (igb_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact igb_us_member.
Qed.
Lemma igb_us_no_repair : us_selected_definition_needs_viewport_repair
  (IFR._perform_ground_step, Gfun (Internal (igb_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Lemma igb_us_selected_member :
  In (IFR._perform_ground_step, Gfun (Internal (igb_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite igb_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact igb_us_selection.
Qed.
Lemma igb_jp_source :
  (prog_defmap (nlist_at 9 jp_cleaned_units)) ! IFR._perform_ground_step =
    Some (Gfun (Internal (igb_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem igb_selected_body_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IFR._perform_ground_step = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (igb_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact igb_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 9 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 9 jp_cleaned_units).
    + exact igb_jp_source.
Qed.

Definition igb_first version := ibk_head (fn_body (igb_body version)).
Definition igb_sound version := ibk_head (rank12b_drop_sequences 1 (fn_body (igb_body version))).
Definition igb_refresh version := ibk_head (rank12b_drop_sequences 2 (fn_body (igb_body version))).
Definition igb_tail version := rank12b_drop_sequences 3 (fn_body (igb_body version)).
Definition igb_object := Ederef (Etempvar IFR._t'6 (tptr (Tstruct IFR._Object noattr)))
  (Tstruct IFR._Object noattr).
Definition igb_graphics := Efield (Efield igb_object IFR._header
  (Tstruct IFR._ObjectNode noattr)) IFR._gfx (Tstruct IFR._GraphNodeObject noattr).
Definition igb_display := Efield igb_graphics IFR._pos (tarray tfloat 3).
Definition igb_copy := Scall None
  (Evar IFR._vec3f_copy (Tfunction [tptr tfloat; tptr tfloat] (tptr tvoid) cc_default))
  [igb_display; ibcc_destination].

Theorem igb_source_cuts : forall version,
  fn_vars (igb_body version) = [(IFR._intendedPos, tarray tfloat 3)] /\
  fn_params (igb_body version) = [(IFR._m, tptr (Tstruct IFR._MarioState noattr))] /\
  fn_body (igb_body version) = Ssequence (igb_first version)
    (Ssequence (igb_sound version) (Ssequence (igb_refresh version) (igb_tail version))) /\
  igb_refresh version = Ssequence (Sset IFR._t'6 ibk_object_read) igb_copy /\
  ibk_normal (igb_sound version) = true /\ ibk_normal (igb_refresh version) = true.
Proof. intros []; repeat split; reflexivity. Qed.
