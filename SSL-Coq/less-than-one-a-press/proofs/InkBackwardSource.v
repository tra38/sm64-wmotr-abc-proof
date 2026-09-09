(** Backward cuts for Ink, taken from the selected generated bodies.
    These are execution checkpoints, not a new model of Mario movement. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Coqlib Ctypes Globalenvs Integers Maps.
From LessThanOneAPress.Generated Require Import
  us_mario jp_mario us_math_util jp_math_util.
From LessThanOneAPress.Proofs Require Import
  GameTypes Area2Rank10AGroundPound Area2Rank12BContact UpperElevatorQueryResolution
  ObjectContactNecessity ContactConsumerSource
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module IBM := us_mario.
Module IBV := us_math_util.

Definition ibk_geometry_body version := rank10a_body version GPGeometryInputs.
Definition ibk_copy_body version := match version with
| VersionUS => us_math_util.f_vec3f_copy
| VersionJP => jp_math_util.f_vec3f_copy end.

Lemma ibk_copy_us_source_receipt :
  nth_error IBV.global_definitions
    (ueqr_definition_index IBV._vec3f_copy IBV.global_definitions) =
  Some (IBV._vec3f_copy, Gfun (Internal (ibk_copy_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.

Lemma ibk_copy_us_source_member :
  In (IBV._vec3f_copy, Gfun (Internal (ibk_copy_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at 30 us_units).
  - exact (us_nlist_at_nIn _ 30 us_units).
  - eapply nth_error_In. exact ibk_copy_us_source_receipt.
Qed.

Lemma ibk_copy_us_selection :
  us_normalized_global_definition_map ! IBV._vec3f_copy =
    Some (Gfun (Internal (ibk_copy_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance
      (unit_global_definitions us_units)).
  - exact ibk_copy_us_source_member.
Qed.

Lemma ibk_copy_us_no_repair :
  us_selected_definition_needs_viewport_repair
    (IBV._vec3f_copy, Gfun (Internal (ibk_copy_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.

Local Opaque normalize_global_definition_map.

Lemma ibk_copy_us_normalized_member :
  In (IBV._vec3f_copy, Gfun (Internal (ibk_copy_body VersionUS)))
    us_normalized_global_definitions.
Proof.
  unfold us_normalized_global_definitions, normalize_global_definitions.
  apply PTree.elements_correct. exact ibk_copy_us_selection.
Qed.

Lemma ibk_copy_us_selected_member :
  In (IBV._vec3f_copy, Gfun (Internal (ibk_copy_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions.
  apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition.
    rewrite ibk_copy_us_no_repair. reflexivity.
  - exact ibk_copy_us_normalized_member.
Qed.

Lemma ibk_copy_jp_source_receipt :
  (prog_defmap (nlist_at 30 jp_cleaned_units)) ! IBV._vec3f_copy =
    Some (Gfun (Internal (ibk_copy_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.

Theorem ibk_selected_copy_resolves : forall version,
  exists function_block,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      IBV._vec3f_copy = Some function_block /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
      function_block = Some (Internal (ibk_copy_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ibk_copy_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at 30 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 30 jp_cleaned_units).
    + exact ibk_copy_jp_source_receipt.
Qed.

Definition ibk_head (s : statement) := match s with
| Ssequence head _ => head | _ => Sskip end.
Definition ibk_before_retry version :=
  ocn_prefix_items 3 (fn_body (ibk_geometry_body version)).
Definition ibk_choice version :=
  ibk_head (rank12b_drop_sequences 3 (fn_body (ibk_geometry_body version))).
Definition ibk_after_retry version :=
  rank12b_drop_sequences 4 (fn_body (ibk_geometry_body version)).
Definition ibk_retry version := match ibk_choice version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Definition ibk_floor_read := Efield
  (Ederef (Etempvar IBM._m (tptr (Tstruct IBM._MarioState noattr)))
    (Tstruct IBM._MarioState noattr)) IBM._floor
  (tptr (Tstruct IBM._Surface noattr)).
Definition ibk_null_guard := Ebinop Oeq
  (Etempvar IBM._t'41 (tptr (Tstruct IBM._Surface noattr)))
  (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint.
Definition ibk_copy_prefix version := ibk_head (ibk_retry version).
Definition ibk_second_query version := rank12b_drop_sequences 1 (ibk_retry version).
Definition ibk_object_read := Efield
  (Ederef (Etempvar IBM._m (tptr (Tstruct IBM._MarioState noattr)))
    (Tstruct IBM._MarioState noattr)) IBM._marioObj
  (tptr (Tstruct IBM._Object noattr)).
Definition ibk_copy_call version := rank12b_drop_sequences 1 (ibk_copy_prefix version).
Definition ibk_copy_args version := match ibk_copy_call version with
| Scall _ _ args => args | _ => [] end.

Theorem ibk_geometry_cuts_are_generated : forall version,
  fn_body (ibk_geometry_body version) =
    ocn_prepend (ibk_before_retry version)
      (Ssequence (ibk_choice version) (ibk_after_retry version)) /\
  ibk_choice version = Ssequence (Sset IBM._t'41 ibk_floor_read)
    (Sifthenelse ibk_null_guard (ibk_retry version) Sskip) /\
  ibk_retry version = Ssequence (ibk_copy_prefix version) (ibk_second_query version) /\
  ibk_copy_prefix version = Ssequence (Sset IBM._t'45 ibk_object_read)
    (ibk_copy_call version) /\
  ibk_copy_call version = Scall None
    (Evar IBM._vec3f_copy
      (Tfunction [tptr tfloat; tptr tfloat] (tptr tvoid) cc_default))
    (ibk_copy_args version).
Proof. intros []; repeat split; reflexivity. Qed.

(** The actual copy reads and writes X, then Y, then Z. In particular its Y
    source is sampled AFTER the X write, not necessarily at function entry. *)
Definition ibk_copy_before_y version := ocn_prefix_items 2 (fn_body (ibk_copy_body version)).
Definition ibk_copy_y version :=
  ibk_head (rank12b_drop_sequences 2 (fn_body (ibk_copy_body version))).
Definition ibk_copy_after_y version :=
  rank12b_drop_sequences 3 (fn_body (ibk_copy_body version)).
Definition ibk_source_y := Ederef
  (Ebinop Oadd (Etempvar IBV._src (tptr tfloat))
    (Econst_int (Int.repr 1) tint) (tptr tfloat)) tfloat.
Definition ibk_destination_y := Ederef
  (Ebinop Oadd (Etempvar IBV._t'3 (tptr tfloat))
    (Econst_int (Int.repr 1) tint) (tptr tfloat)) tfloat.
Definition ibk_y_store := Sassign ibk_destination_y (Etempvar IBV._t'4 tfloat).

Theorem ibk_copy_y_cut_is_generated : forall version,
  fn_body (ibk_copy_body version) =
    ocn_prepend (ibk_copy_before_y version)
      (Ssequence (ibk_copy_y version) (ibk_copy_after_y version)) /\
  ibk_copy_y version = Ssequence (Sset IBV._t'3 (Evar IBV._dest (tptr tfloat)))
    (Ssequence (Sset IBV._t'4 ibk_source_y) ibk_y_store).
Proof. intros []; split; reflexivity. Qed.
