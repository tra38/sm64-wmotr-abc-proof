(** The next backward height producer: the selected post-action sink body. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Globalenvs Integers Maps.
From LessThanOneAPress.Generated Require Import us_mario jp_mario.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkFloorResetExecution
  ObjectContactNecessity Area2Rank12BContact UpperElevatorQueryResolution
  ContactConsumerSource CleanedClightPrograms ClightLinkExecution
  GlobalInterfaceStructural JPSourceSymbolTransport JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SelectedClightTarget
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module IQ := us_mario.

Definition iq_body version := match version with
| VersionUS => us_mario.f_sink_mario_in_quicksand
| VersionJP => jp_mario.f_sink_mario_in_quicksand end.

Lemma iq_us_source :
  nth_error IQ.global_definitions
    (ueqr_definition_index IQ._sink_mario_in_quicksand IQ.global_definitions) =
  Some (IQ._sink_mario_in_quicksand, Gfun (Internal (iq_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.

Lemma iq_us_member :
  In (IQ._sink_mario_in_quicksand, Gfun (Internal (iq_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 1 us_units).
  - exact (us_nlist_at_nIn _ 1 us_units).
  - eapply nth_error_In. exact iq_us_source.
Qed.

Lemma iq_us_selection :
  us_normalized_global_definition_map ! IQ._sink_mario_in_quicksand =
    Some (Gfun (Internal (iq_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact iq_us_member.
Qed.

Lemma iq_us_no_repair :
  us_selected_definition_needs_viewport_repair
    (IQ._sink_mario_in_quicksand, Gfun (Internal (iq_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.

Lemma iq_us_selected_member :
  In (IQ._sink_mario_in_quicksand, Gfun (Internal (iq_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite iq_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact iq_us_selection.
Qed.

Lemma iq_jp_source :
  (prog_defmap (nlist_at 1 jp_cleaned_units)) ! IQ._sink_mario_in_quicksand =
    Some (Gfun (Internal (iq_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.

Theorem iq_selected_body_resolves : forall version,
  exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      IQ._sink_mario_in_quicksand = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (iq_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact iq_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 1 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 1 jp_cleaned_units).
    + exact iq_jp_source.
Qed.

Definition iq_object := Ederef (Etempvar IQ._o (tptr (Tstruct IQ._Object noattr)))
  (Tstruct IQ._Object noattr).
Definition iq_header := Efield iq_object IQ._header (Tstruct IQ._ObjectNode noattr).
Definition iq_graphics := Efield iq_header IQ._gfx (Tstruct IQ._GraphNodeObject noattr).
Definition iq_graphics_pos := Efield iq_graphics IQ._pos (tarray tfloat 3).
Definition iq_y := Ederef (Ebinop Oadd iq_graphics_pos
  (Econst_int (Int.repr 1) tint) (tptr tfloat)) tfloat.
Definition iq_depth := Efield ibcc_state IQ._quicksandDepth tfloat.
Definition iq_matrix_type := tptr (tarray (tarray tfloat 4) 4).
Definition iq_matrix := Efield iq_graphics IQ._throwMatrix iq_matrix_type.
Definition iq_matrix_y receiver := Ederef (Ebinop Oadd
  (Ederef (Ebinop Oadd
    (Ederef (Etempvar receiver iq_matrix_type) (tarray (tarray tfloat 4) 4))
    (Econst_int (Int.repr 3) tint) (tptr (tarray tfloat 4))) (tarray tfloat 4))
  (Econst_int (Int.repr 1) tint) (tptr tfloat)) tfloat.
Definition iq_matrix_branch version := match ibk_head
  (rank12b_drop_sequences 1 (fn_body (iq_body version))) with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Definition iq_display_tail version := rank12b_drop_sequences 2 (fn_body (iq_body version)).

Theorem iq_generated_cuts : forall version,
  fn_vars (iq_body version) = [] /\
  fn_params (iq_body version) = [(IQ._m, tptr (Tstruct IQ._MarioState noattr))] /\
  fn_body (iq_body version) = Ssequence (Sset IQ._o ibk_object_read)
    (Ssequence (Ssequence (Sset IQ._t'3 iq_matrix)
      (Sifthenelse (Etempvar IQ._t'3 iq_matrix_type) (iq_matrix_branch version) Sskip))
      (iq_display_tail version)) /\
  iq_matrix_branch version = Ssequence (Sset IQ._t'4 iq_matrix)
    (Ssequence (Sset IQ._t'5 iq_matrix)
      (Ssequence (Sset IQ._t'6 (iq_matrix_y IQ._t'5))
        (Ssequence (Sset IQ._t'7 iq_depth)
          (Sassign (iq_matrix_y IQ._t'4)
            (Ebinop Osub (Etempvar IQ._t'6 tfloat) (Etempvar IQ._t'7 tfloat) tfloat))))) /\
  iq_display_tail version = Ssequence (Sset IQ._t'1 iq_y)
    (Ssequence (Sset IQ._t'2 iq_depth)
      (Sassign iq_y (Ebinop Osub (Etempvar IQ._t'1 tfloat) (Etempvar IQ._t'2 tfloat) tfloat))) /\
  ibk_normal (iq_matrix_branch version) = true /\
  ifr_keeps_temp IQ._m (iq_matrix_branch version) = true /\
  ifr_keeps_temp IQ._o (iq_matrix_branch version) = true.
Proof. intros []; repeat split; reflexivity. Qed.
