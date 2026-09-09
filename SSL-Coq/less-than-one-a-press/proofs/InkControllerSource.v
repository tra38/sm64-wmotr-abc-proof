(** Ordinary controller sampling and Mario's per-frame input preparation.
    Every cut below is extracted from the selected US/JP generated program. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Globalenvs Integers Maps.
From LessThanOneAPress.Generated Require Import us_game_init jp_game_init us_mario jp_mario.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkCopyCaller Area2Rank12BContact UpperElevatorQueryResolution
  ContactConsumerSource CleanedClightPrograms ClightLinkExecution
  GlobalInterfaceStructural JPSourceSymbolTransport JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SelectedClightTarget
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module ICG := us_game_init.

Inductive InkControllerBody := ICRead | ICButtons | ICInputs.
Definition ics_body version kind := match version, kind with
| VersionUS, ICRead => us_game_init.f_read_controller_inputs
| VersionJP, ICRead => jp_game_init.f_read_controller_inputs
| VersionUS, ICButtons => us_mario.f_update_mario_button_inputs
| VersionJP, ICButtons => jp_mario.f_update_mario_button_inputs
| VersionUS, ICInputs => us_mario.f_update_mario_inputs
| VersionJP, ICInputs => jp_mario.f_update_mario_inputs end.
Definition ics_ident kind := match kind with
| ICRead => ICG._read_controller_inputs
| ICButtons => IBM._update_mario_button_inputs
| ICInputs => IBM._update_mario_inputs end.
Definition ics_unit kind : nat := match kind with ICRead => 0 | _ => 1 end.
Definition ics_us_definitions kind := match kind with
| ICRead => ICG.global_definitions | _ => IBM.global_definitions end.

Lemma ics_us_source : forall kind,
  nth_error (ics_us_definitions kind)
    (ueqr_definition_index (ics_ident kind) (ics_us_definitions kind)) =
  Some (ics_ident kind, Gfun (Internal (ics_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ics_us_member : forall kind,
  In (ics_ident kind, Gfun (Internal (ics_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (ics_unit kind) us_units).
  - exact (us_nlist_at_nIn _ (ics_unit kind) us_units).
  - destruct kind; eapply nth_error_In.
    + exact (ics_us_source ICRead).
    + exact (ics_us_source ICButtons).
    + exact (ics_us_source ICInputs).
Qed.
Lemma ics_us_selection : forall kind,
  us_normalized_global_definition_map ! (ics_ident kind) =
    Some (Gfun (Internal (ics_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ics_us_member kind).
Qed.
Lemma ics_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ics_ident kind, Gfun (Internal (ics_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ics_us_selected_member : forall kind,
  In (ics_ident kind, Gfun (Internal (ics_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ics_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (ics_us_selection kind).
Qed.
Lemma ics_jp_source : forall kind,
  (prog_defmap (nlist_at (ics_unit kind) jp_cleaned_units)) ! (ics_ident kind) =
    Some (Gfun (Internal (ics_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem ics_selected_bodies_resolve : forall version kind,
  exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ics_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ics_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ics_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (ics_unit kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (ics_unit kind) jp_cleaned_units).
    + exact (ics_jp_source kind).
Qed.

Definition ics_field id tag field ty := Efield
  (Ederef (Etempvar id (tptr (Tstruct tag noattr))) (Tstruct tag noattr)) field ty.
Definition ics_controller_field field ty := ics_field ICG._controller ICG._Controller field ty.
Definition ics_pad_field id := ics_field id ICG.__319 ICG._button tushort.
Definition ics_data := ics_controller_field ICG._controllerData (tptr (Tstruct ICG.__319 noattr)).
Definition ics_down := ics_controller_field ICG._buttonDown tushort.
Definition ics_pressed := ics_controller_field ICG._buttonPressed tushort.
Definition ics_iteration version := match ibk_head
  (rank12b_drop_sequences 2 (fn_body (ics_body version ICRead))) with
| Ssequence _ (Sloop iteration _) => iteration | _ => Sskip end.
Definition ics_present version := match ics_iteration version with
| Ssequence _ (Ssequence _ (Ssequence _ (Sifthenelse _ yes _))) => yes | _ => Sskip end.
Definition ics_edge_stage version := ibk_head (rank12b_drop_sequences 2 (ics_present version)).
Definition ics_down_stage version := ibk_head (rank12b_drop_sequences 3 (ics_present version)).
Definition ics_edge_expression := Ebinop Oand (Etempvar ICG._t'26 tushort)
  (Ebinop Oxor (Etempvar ICG._t'28 tushort) (Etempvar ICG._t'29 tushort) tint) tint.
Definition ics_mario_controller := ics_field IBM._m IBM._MarioState IBM._controller
  (tptr (Tstruct IBM._Controller noattr)).
Definition ics_mario_a version := ibk_head (fn_body (ics_body version ICButtons)).
Definition ics_mario_tail version := rank12b_drop_sequences 1 (fn_body (ics_body version ICButtons)).
Definition ics_mario_a_yes version := match ics_mario_a version with
| Ssequence _ (Ssequence _ (Sifthenelse _ yes _)) => yes | _ => Sskip end.
Definition ics_input := ics_field IBM._m IBM._MarioState IBM._input tushort.
Definition ics_reset version := ibk_head (rank12b_drop_sequences 1 (fn_body (ics_body version ICInputs))).

Theorem ics_source_cuts : forall version,
  ics_edge_stage version =
    Ssequence (Sset ICG._t'25 ics_data)
    (Ssequence (Sset ICG._t'26 (ics_pad_field ICG._t'25))
    (Ssequence (Sset ICG._t'27 ics_data)
    (Ssequence (Sset ICG._t'28 (ics_pad_field ICG._t'27))
    (Ssequence (Sset ICG._t'29 ics_down)
      (Sassign ics_pressed ics_edge_expression))))) /\
  ics_down_stage version = Ssequence (Sset ICG._t'23 ics_data)
    (Ssequence (Sset ICG._t'24 (ics_pad_field ICG._t'23))
      (Sassign ics_down (Etempvar ICG._t'24 tushort))) /\
  fn_body (ics_body version ICButtons) =
    Ssequence (ics_mario_a version) (ics_mario_tail version) /\
  ics_mario_a version = Ssequence (Sset IBM._t'20 ics_mario_controller)
    (Ssequence (Sset IBM._t'21 (ics_field IBM._t'20 IBM._Controller IBM._buttonPressed tushort))
      (Sifthenelse (Ebinop Oand (Etempvar IBM._t'21 tushort)
        (Econst_int (Int.repr 32768) tint) tint) (ics_mario_a_yes version) Sskip)) /\
  ics_mario_a_yes version = Ssequence (Sset IBM._t'22 ics_input)
    (Sassign ics_input (Ebinop Oor (Etempvar IBM._t'22 tushort)
      (Econst_int (Int.repr 2) tint) tint)) /\
  ics_reset version = Sassign ics_input (Econst_int Int.zero tint).
Proof. intros []; repeat split; reflexivity. Qed.
