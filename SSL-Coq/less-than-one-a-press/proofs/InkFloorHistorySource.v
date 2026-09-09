(** Earlier floor-history checkpoints from the real selected US/JP bodies.
    In particular, the no-update returns and the accepted-position path are
    distinct statements, not alternative constructors of a gameplay model. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Floats
  Globalenvs Integers Maps.
From LessThanOneAPress.Generated Require Import us_mario_step jp_mario_step.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkGroundBackwardSource
  InkFloorResetSource ObjectContactNecessity Area2Rank12BContact
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Module IFH := us_mario_step.

Definition ifh_quarter_body version := match version with
| VersionUS => us_mario_step.f_perform_ground_quarter_step
| VersionJP => jp_mario_step.f_perform_ground_quarter_step end.

Lemma ifh_quarter_us_source :
  nth_error IFH.global_definitions
    (ueqr_definition_index IFH._perform_ground_quarter_step IFH.global_definitions) =
  Some (IFH._perform_ground_quarter_step, Gfun (Internal (ifh_quarter_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma ifh_quarter_us_member :
  In (IFH._perform_ground_quarter_step, Gfun (Internal (ifh_quarter_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 9 us_units).
  - exact (us_nlist_at_nIn _ 9 us_units).
  - eapply nth_error_In. exact ifh_quarter_us_source.
Qed.
Lemma ifh_quarter_us_selection :
  us_normalized_global_definition_map ! IFH._perform_ground_quarter_step =
    Some (Gfun (Internal (ifh_quarter_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact ifh_quarter_us_member.
Qed.
Lemma ifh_quarter_us_no_repair : us_selected_definition_needs_viewport_repair
  (IFH._perform_ground_quarter_step, Gfun (Internal (ifh_quarter_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma ifh_quarter_us_selected_member :
  In (IFH._perform_ground_quarter_step, Gfun (Internal (ifh_quarter_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ifh_quarter_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact ifh_quarter_us_selection.
Qed.
Lemma ifh_quarter_jp_source :
  (prog_defmap (nlist_at 9 jp_cleaned_units)) ! IFH._perform_ground_quarter_step =
    Some (Gfun (Internal (ifh_quarter_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem ifh_selected_quarter_body_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IFH._perform_ground_quarter_step = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ifh_quarter_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ifh_quarter_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 9 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 9 jp_cleaned_units).
    + exact ifh_quarter_jp_source.
Qed.

Definition ifh_quarter_prefix version := ocn_prefix_items 6 (fn_body (ifh_quarter_body version)).
Definition ifh_quarter_tail version := rank12b_drop_sequences 6 (fn_body (ifh_quarter_body version)).
Definition ifh_missing version := ibk_head (ifh_quarter_tail version).
Definition ifh_water version := ibk_head (rank12b_drop_sequences 7 (fn_body (ifh_quarter_body version))).
Definition ifh_vertical version := ibk_head (rank12b_drop_sequences 8 (fn_body (ifh_quarter_body version))).
Definition ifh_post_water version := rank12b_drop_sequences 8 (fn_body (ifh_quarter_body version)).
Definition ifh_floor_ceil version := ibk_head (rank12b_drop_sequences 9 (fn_body (ifh_quarter_body version))).
Definition ifh_accept version := rank12b_drop_sequences 10 (fn_body (ifh_quarter_body version)).
Definition ifh_leave version := match ifh_vertical version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Definition ifh_leave_commit version := rank12b_drop_sequences 1 (ifh_leave version).
Definition ifh_accept_move version := ibk_head (ifh_accept version).
Definition ifh_accept_floor version := ibk_head (rank12b_drop_sequences 1 (ifh_accept version)).
Definition ifh_accept_height version := ibk_head (rank12b_drop_sequences 2 (ifh_accept version)).
Definition ifh_accept_after version := rank12b_drop_sequences 3 (ifh_accept version).

Definition ifh_next n := Ederef
  (Ebinop Oadd (Etempvar IFH._nextPos (tptr tfloat))
    (Econst_int (Int.repr n) tint) (tptr tfloat)) tfloat.
Definition ifh_null_guard := Ebinop Oeq
  (Etempvar IFH._t'21 (tptr (Tstruct IFH._Surface noattr)))
  (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint.
Definition ifh_leave_guard := Ebinop Ogt (Etempvar IFH._t'16 tfloat)
  (Ebinop Oadd (Etempvar IFH._floorHeight tfloat)
    (Econst_single (Float32.of_bits (Int.repr 1120403456)) tfloat) tfloat) tint.
Definition ifh_y_ceil_guard := Ebinop Oge
  (Ebinop Oadd (Etempvar IFH._t'18 tfloat)
    (Econst_single (Float32.of_bits (Int.repr 1126170624)) tfloat) tfloat)
  (Etempvar IFH._ceilHeight tfloat) tint.
Definition ifh_floor_ceil_guard := Ebinop Oge
  (Ebinop Oadd (Etempvar IFH._floorHeight tfloat)
    (Econst_single (Float32.of_bits (Int.repr 1126170624)) tfloat) tfloat)
  (Etempvar IFH._ceilHeight tfloat) tint.
Definition ifh_return n := Sreturn (Some (Econst_int (Int.repr n) tint)).

Theorem ifh_quarter_source_cuts : forall version,
  fn_params (ifh_quarter_body version) =
    [(IFH._m, tptr (Tstruct IFH._MarioState noattr)); (IFH._nextPos, tptr tfloat)] /\
  fn_vars (ifh_quarter_body version) =
    [(IFH._ceil, tptr (Tstruct IFH._Surface noattr));
     (IFH._floor, tptr (Tstruct IFH._Surface noattr))] /\
  fn_body (ifh_quarter_body version) =
    ocn_prepend (ifh_quarter_prefix version) (ifh_quarter_tail version) /\
  forallb ibk_normal (ifh_quarter_prefix version) = true /\
  ifh_quarter_tail version = Ssequence (ifh_missing version)
    (Ssequence (ifh_water version) (Ssequence (ifh_vertical version)
      (Ssequence (ifh_floor_ceil version) (ifh_accept version)))) /\
  ifh_missing version = Ssequence
    (Sset IFH._t'21 (Evar IFH._floor (tptr (Tstruct IFH._Surface noattr))))
    (Sifthenelse ifh_null_guard (ifh_return 2) Sskip) /\
  ibk_normal (ifh_water version) = true /\
  ifh_vertical version = Ssequence (Sset IFH._t'16 (ifh_next 1))
    (Sifthenelse ifh_leave_guard (ifh_leave version) Sskip) /\
  ifh_leave version = Ssequence
    (Ssequence (Sset IFH._t'18 (ifh_next 1))
      (Sifthenelse ifh_y_ceil_guard (ifh_return 2) Sskip))
    (ifh_leave_commit version) /\
  ifh_floor_ceil version = Sifthenelse ifh_floor_ceil_guard (ifh_return 2) Sskip /\
  ifh_accept version = Ssequence (ifh_accept_move version)
    (Ssequence (ifh_accept_floor version)
      (Ssequence (ifh_accept_height version) (ifh_accept_after version))) /\
  ifh_accept_move version = Ssequence (Sset IFH._t'14 (ifh_next 0))
    (Ssequence (Sset IFH._t'15 (ifh_next 2))
      (Scall None (Evar IFH._vec3f_set
        (Tfunction [tptr tfloat; tfloat; tfloat; tfloat] (tptr tvoid) cc_default))
        [ibcc_destination; Etempvar IFH._t'14 tfloat;
         Etempvar IFH._floorHeight tfloat; Etempvar IFH._t'15 tfloat])) /\
  ifh_accept_height version = Sassign ifr_floor_read (Etempvar IFH._floorHeight tfloat).
Proof. intros []; repeat split; reflexivity. Qed.

(** The floor source preceding actions is a query at the movement position
    after both actual wall calls. The query-result assignment does not itself
    snap the movement position. *)
Definition ifh_geometry_walls version := ocn_prefix_items 2 (fn_body (ibk_geometry_body version)).
Definition ifh_geometry_query version := ibk_head
  (rank12b_drop_sequences 2 (fn_body (ibk_geometry_body version))).
Definition ifh_geometry_query_call version := ibk_head (ifh_geometry_query version).
Definition ifh_geometry_query_store version := rank12b_drop_sequences 1 (ifh_geometry_query version).
Definition ifh_geometry_after_query version := rank12b_drop_sequences 3 (fn_body (ibk_geometry_body version)).
Definition ifh_state_coord n := Ederef (Ebinop Oadd ibcc_destination
  (Econst_int (Int.repr n) tint) (tptr tfloat)) tfloat.
Definition ifh_geometry_find_floor := Scall (Some IBM._t'1)
  (Evar IBM._find_floor
    (Tfunction [tfloat; tfloat; tfloat; tptr (tptr (Tstruct IBM._Surface noattr))]
      tfloat cc_default))
  [Etempvar IBM._t'46 tfloat; Etempvar IBM._t'47 tfloat; Etempvar IBM._t'48 tfloat;
   Eaddrof ibk_floor_read (tptr (tptr (Tstruct IBM._Surface noattr)))].

Theorem ifh_geometry_source_cuts : forall version,
  fn_body (ibk_geometry_body version) = ocn_prepend (ifh_geometry_walls version)
    (Ssequence (ifh_geometry_query version) (ifh_geometry_after_query version)) /\
  forallb ibk_normal (ifh_geometry_walls version) = true /\
  ifh_geometry_query version = Ssequence (ifh_geometry_query_call version)
    (ifh_geometry_query_store version) /\
  ifh_geometry_query_call version = Ssequence (Sset IBM._t'46 (ifh_state_coord 0))
    (Ssequence (Sset IBM._t'47 (ifh_state_coord 1))
      (Ssequence (Sset IBM._t'48 (ifh_state_coord 2)) ifh_geometry_find_floor)) /\
  ifh_geometry_query_store version = Sassign ifr_floor_read (Etempvar IBM._t'1 tfloat) /\
  ibk_normal (ifh_geometry_query version) = true.
Proof. intros []; repeat split; reflexivity. Qed.
