(** Actual landing-cancellation history checkpoints.  These are projections
    of the generated bodies, not a replacement landing transition model. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Globalenvs Integers Maps.
From LessThanOneAPress.Generated Require Import us_mario_actions_moving jp_mario_actions_moving.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkBackwardSource InkBackwardExecution InkFloorResetExecution InkCopyCaller
  Area2Rank12BContact UpperElevatorQueryResolution ContactConsumerSource ObjectContactNecessity
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition ilh_cancel_body version := match version with
| VersionUS => us_mario_actions_moving.f_common_landing_cancels
| VersionJP => jp_mario_actions_moving.f_common_landing_cancels end.

Lemma ilh_us_source :
  nth_error IMB.global_definitions
    (ueqr_definition_index IMB._common_landing_cancels IMB.global_definitions) =
  Some (IMB._common_landing_cancels, Gfun (Internal (ilh_cancel_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma ilh_us_member :
  In (IMB._common_landing_cancels, Gfun (Internal (ilh_cancel_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 5 us_units).
  - exact (us_nlist_at_nIn _ 5 us_units).
  - eapply nth_error_In. exact ilh_us_source.
Qed.
Lemma ilh_us_selection :
  us_normalized_global_definition_map ! IMB._common_landing_cancels =
    Some (Gfun (Internal (ilh_cancel_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact ilh_us_member.
Qed.
Lemma ilh_us_no_repair :
  us_selected_definition_needs_viewport_repair
    (IMB._common_landing_cancels, Gfun (Internal (ilh_cancel_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Lemma ilh_us_selected_member :
  In (IMB._common_landing_cancels, Gfun (Internal (ilh_cancel_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ilh_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact ilh_us_selection.
Qed.
Lemma ilh_jp_source :
  (prog_defmap (nlist_at 5 jp_cleaned_units)) ! IMB._common_landing_cancels =
    Some (Gfun (Internal (ilh_cancel_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem ilh_selected_cancels_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IMB._common_landing_cancels = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ilh_cancel_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ilh_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 5 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 5 jp_cleaned_units).
    + exact ilh_jp_source.
Qed.

Definition ilh_before_gate version := ocn_prefix_items 4 (fn_body (ilh_cancel_body version)).
Definition ilh_gate_tail version := rank12b_drop_sequences 4 (fn_body (ilh_cancel_body version)).
Definition ilh_gate version := ibk_head (ilh_gate_tail version).
Definition ilh_after_gate version := rank12b_drop_sequences 5 (fn_body (ilh_cancel_body version)).
Definition ilh_increment version := match ilh_gate version with Ssequence first _ => first | _ => Sskip end.
Definition ilh_duration_guard version := match ilh_gate version with Ssequence _ rest => rest | _ => Sskip end.
Definition ilh_duration_yes version := match ilh_duration_guard version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Definition ilh_frames := Efield
  (Ederef (Etempvar IMB._landingAction (tptr (Tstruct IMB._LandingAction noattr)))
    (Tstruct IMB._LandingAction noattr)) IMB._numFrames tshort.
Definition ilh_duration_test := Ebinop Oge (Etempvar IMB._t'6 tushort)
  (Etempvar IMB._t'13 tshort) tint.
Definition ilh_increment_value := Ecast (Ebinop Oadd
  (Etempvar IMB._t'15 tushort) (Econst_int Int.one tint) tint) tushort.
Definition ilh_a_guard version := ibk_head (ilh_after_gate version).
Definition ilh_off_guard version := ibk_head (rank12b_drop_sequences 1 (ilh_after_gate version)).
Definition ilh_a_yes version := match ilh_a_guard version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Definition ilh_off_yes version := match ilh_off_guard version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.

Theorem ilh_source_cuts : forall version,
  fn_vars (ilh_cancel_body version) = [] /\
  fn_body (ilh_cancel_body version) =
    ocn_prepend (ilh_before_gate version) (ilh_gate_tail version) /\
  ilh_gate_tail version = Ssequence (ilh_gate version) (ilh_after_gate version) /\
  ilh_gate version = Ssequence (ilh_increment version) (ilh_duration_guard version) /\
  ilh_increment version = Ssequence
    (Ssequence (Sset IMB._t'15 imb_timer) (Sset IMB._t'6 ilh_increment_value))
    (Sassign imb_timer (Etempvar IMB._t'6 tushort)) /\
  ilh_duration_guard version = Ssequence (Sset IMB._t'13 ilh_frames)
    (Sifthenelse ilh_duration_test (ilh_duration_yes version) Sskip) /\
  ilh_after_gate version = Ssequence (ilh_a_guard version)
    (Ssequence (ilh_off_guard version) (Sreturn (Some (Econst_int Int.zero tint)))) /\
  ilh_a_guard version = Ssequence (Sset IMB._t'11 imb_input)
    (Sifthenelse (Ebinop Oand (Etempvar IMB._t'11 tushort)
      (Econst_int (Int.repr 2) tint) tint) (ilh_a_yes version) Sskip) /\
  ilh_off_guard version = Ssequence (Sset IMB._t'9 imb_input)
    (Sifthenelse (Ebinop Oand (Etempvar IMB._t'9 tushort)
      (Econst_int (Int.repr 4) tint) tint) (ilh_off_yes version) Sskip) /\
  ifr_keeps_temp IMB._m (ocn_prepend (ilh_before_gate version) Sskip) = true /\
  ifr_keeps_temp IMB._landingAction (ocn_prepend (ilh_before_gate version) Sskip) = true.
Proof. intros []; repeat split; reflexivity. Qed.

(** A return branch cannot masquerade as a normal continuation, regardless
    of what its genuine callee writes or returns. *)
Definition ilh_duration_before_return version := match ilh_duration_yes version with
| Ssequence before _ => before | _ => Sskip end.
Theorem ilh_duration_return_shape : forall version,
  ilh_duration_yes version = Ssequence (ilh_duration_before_return version)
    (Sreturn (Some (Etempvar IMB._t'5 tuint))) /\
  ibk_normal (ilh_duration_before_return version) = true.
Proof. intros []; split; reflexivity. Qed.
