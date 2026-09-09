(** Selected moving-action bodies and exact backward checkpoints. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Floats Globalenvs Integers Maps.
From LessThanOneAPress.Generated Require Import us_mario_actions_moving jp_mario_actions_moving.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkFloorResetSource InkQuicksandSource
  ObjectContactNecessity Area2Rank12BContact UpperElevatorQueryResolution
  ContactConsumerSource CleanedClightPrograms ClightLinkExecution
  GlobalInterfaceStructural JPSourceSymbolTransport JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SelectedClightTarget
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module IMB := us_mario_actions_moving.

Inductive InkMovingBody := IMBAlign | IMBLanding | IMBCrouch.
Definition imb_body version kind := match version, kind with
| VersionUS, IMBAlign => us_mario_actions_moving.f_align_with_floor
| VersionJP, IMBAlign => jp_mario_actions_moving.f_align_with_floor
| VersionUS, IMBLanding => us_mario_actions_moving.f_common_landing_action
| VersionJP, IMBLanding => jp_mario_actions_moving.f_common_landing_action
| VersionUS, IMBCrouch => us_mario_actions_moving.f_act_crouch_slide
| VersionJP, IMBCrouch => jp_mario_actions_moving.f_act_crouch_slide end.
Definition imb_ident kind := match kind with
| IMBAlign => IMB._align_with_floor | IMBLanding => IMB._common_landing_action
| IMBCrouch => IMB._act_crouch_slide end.

Lemma imb_us_source : forall kind,
  nth_error IMB.global_definitions
    (ueqr_definition_index (imb_ident kind) IMB.global_definitions) =
  Some (imb_ident kind, Gfun (Internal (imb_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma imb_us_member : forall kind,
  In (imb_ident kind, Gfun (Internal (imb_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at 5 us_units).
  - exact (us_nlist_at_nIn _ 5 us_units).
  - eapply nth_error_In. exact (imb_us_source kind).
Qed.
Lemma imb_us_selection : forall kind,
  us_normalized_global_definition_map ! (imb_ident kind) =
    Some (Gfun (Internal (imb_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (imb_us_member kind).
Qed.
Lemma imb_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (imb_ident kind, Gfun (Internal (imb_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma imb_us_selected_member : forall kind,
  In (imb_ident kind, Gfun (Internal (imb_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite imb_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (imb_us_selection kind).
Qed.
Lemma imb_jp_source : forall kind,
  (prog_defmap (nlist_at 5 jp_cleaned_units)) ! (imb_ident kind) =
    Some (Gfun (Internal (imb_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem imb_selected_bodies_resolve : forall version kind,
  exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (imb_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (imb_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (imb_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 5 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 5 jp_cleaned_units).
    + exact (imb_jp_source kind).
Qed.

Definition imb_align_tail version := rank12b_drop_sequences 1 (fn_body (imb_body version IMBAlign)).
Definition imb_timer := Efield ibcc_state IMB._actionTimer tushort.
Definition imb_input := Efield ibcc_state IMB._input tushort.
Definition imb_landing_delta := Ebinop Osub
  (Ebinop Omul (Ebinop Osub (Econst_int (Int.repr 4) tint)
    (Etempvar IMB._t'4 tushort) tint)
    (Econst_single (Float32.of_bits (Int.repr 1080033280)) tfloat) tfloat)
  (Econst_single (Float32.of_bits (Int.repr 1056964608)) tfloat) tfloat.
Definition imb_landing_write version := match ibk_head
  (rank12b_drop_sequences 6 (fn_body (imb_body version IMBLanding))) with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Definition imb_crouch_a_guard version := match ibk_head
  (rank12b_drop_sequences 1 (fn_body (imb_body version IMBCrouch))) with
| Ssequence _ (Sifthenelse _ (Ssequence _ guard) _) => guard | _ => Sskip end.
Definition imb_crouch_a_yes version := match imb_crouch_a_guard version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.

Theorem imb_source_cuts : forall version,
  fn_vars (imb_body version IMBAlign) = [] /\
  fn_params (imb_body version IMBAlign) = [(IMB._m, tptr (Tstruct IMB._MarioState noattr))] /\
  fn_body (imb_body version IMBAlign) =
    Ssequence (ifr_snap version IFRStationary) (imb_align_tail version) /\
  imb_landing_write version = Ssequence (Sset IMB._t'3 iq_depth)
    (Ssequence (Sset IMB._t'4 imb_timer)
      (Sassign iq_depth (Ebinop Oadd (Etempvar IMB._t'3 tfloat) imb_landing_delta tfloat))) /\
  imb_crouch_a_guard version = Ssequence (Sset IMB._t'13 imb_input)
    (Sifthenelse (Ebinop Oand (Etempvar IMB._t'13 tushort)
      (Econst_int (Int.repr 2) tint) tint) (imb_crouch_a_yes version) Sskip).
Proof. intros []; repeat split; reflexivity. Qed.
