(** Resolve the actual generated US/JP platform update and displacement
    dispatcher. Extract their owner-test, clearing, and dispatch branches;
    InkPlatformDeparture proves the corresponding memory effects. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_platform_displacement jp_platform_displacement.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkBackwardSource InkBackwardExecution InkBodyResetFrame InkBodyResetConstruction
  InkCopyCaller InkFloorListEffects ObjectContactNecessity ContactConsumerExecution
  SecretContactExecution SelectedClightTarget EyerokRank15LiveMovement
  Area2Rank12BContact UpperElevatorQueryResolution
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IPD := us_platform_displacement.

Inductive InkPlatformBody := IPDUpdate | IPDApply.
Definition ipd_body version kind := match version, kind with
| VersionUS, IPDUpdate => us_platform_displacement.f_update_mario_platform
| VersionJP, IPDUpdate => jp_platform_displacement.f_update_mario_platform
| VersionUS, IPDApply => us_platform_displacement.f_apply_mario_platform_displacement
| VersionJP, IPDApply => jp_platform_displacement.f_apply_mario_platform_displacement end.
Definition ipd_ident kind := match kind with
| IPDUpdate => IPD._update_mario_platform | IPDApply => IPD._apply_mario_platform_displacement end.

Lemma ipd_us_source : forall kind,
  nth_error IPD.global_definitions (ueqr_definition_index (ipd_ident kind) IPD.global_definitions) =
    Some (ipd_ident kind, Gfun (Internal (ipd_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ipd_us_member : forall kind,
  In (ipd_ident kind, Gfun (Internal (ipd_body VersionUS kind))) (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 29 us_units).
  - exact (us_nlist_at_nIn _ 29 us_units).
  - eapply nth_error_In. exact (ipd_us_source kind).
Qed.
Lemma ipd_us_selection : forall kind,
  us_normalized_global_definition_map ! (ipd_ident kind) =
    Some (Gfun (Internal (ipd_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ipd_us_member kind).
Qed.
Lemma ipd_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ipd_ident kind, Gfun (Internal (ipd_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ipd_us_selected_member : forall kind,
  In (ipd_ident kind, Gfun (Internal (ipd_body VersionUS kind))) us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ipd_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (ipd_us_selection kind).
Qed.
Lemma ipd_jp_source : forall kind,
  (prog_defmap (nlist_at 29 jp_cleaned_units)) ! (ipd_ident kind) =
    Some (Gfun (Internal (ipd_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem ipd_selected_bodies_resolve : forall version kind,
  exists b, Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ipd_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ipd_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ipd_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 29 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 29 jp_cleaned_units).
    + exact (ipd_jp_source kind).
Qed.

Definition ipd_object := tptr (Tstruct IPD._Object noattr).
Definition ipd_surface := tptr (Tstruct IPD._Surface noattr).
Definition ipd_null := Ecast (Econst_int Int.zero tint) (tptr tvoid).
Definition ipd_nonnull id ty := Ebinop One (Etempvar id ty) ipd_null tint.
Definition ipd_switch version := rank12b_drop_sequences 6 (fn_body (ipd_body version IPDUpdate)).
Definition ipd_near version := match ipd_switch version with
| Sswitch _ (LScons _ _ (LScons _ near _)) => near | _ => Sskip end.
Definition ipd_owner_branch version := ibk_head (ipd_near version).
Definition ipd_owner_guard version := ibk_head (ipd_owner_branch version).
Definition ipd_owner_choice version := rank12b_drop_sequences 1 (ipd_owner_branch version).
Definition ipd_clear version := match ipd_owner_choice version with
| Sifthenelse _ _ no => no | _ => Sskip end.
Definition ipd_apply_prefix version := ibk_head
  (rank12b_drop_sequences 1 (fn_body (ipd_body version IPDApply))).
Definition ipd_apply_call version := rank12b_drop_sequences 2 (fn_body (ipd_body version IPDApply)).
Definition ipd_apply_other_tests version := ibk_head (ipd_apply_prefix version).

Lemma ipd_source : forall version,
  ipd_near version = Ssequence (ipd_owner_branch version) Sbreak /\
  ipd_owner_branch version = Ssequence (ipd_owner_guard version) (ipd_owner_choice version) /\
  ipd_owner_guard version = Ssequence
    (Sset IPD._t'10 (Evar IPD._floor ipd_surface))
    (Sifthenelse (ipd_nonnull IPD._t'10 ipd_surface)
      (Ssequence (Sset IPD._t'11 (Evar IPD._floor ipd_surface))
        (Ssequence (Sset IPD._t'12 (ibr_field IPD._t'11 IPD._Surface IPD._object ipd_object))
          (Sset IPD._t'3 (Ecast (ipd_nonnull IPD._t'12 ipd_object) tbool))))
      (Sset IPD._t'3 (Econst_int Int.zero tint))) /\
  ipd_clear version = Ssequence (Sassign (Evar IPD._gMarioPlatform ipd_object) ipd_null)
    (Ssequence (Sset IPD._t'4 (Evar IPD._gMarioObject ipd_object))
      (Sassign (ibr_field IPD._t'4 IPD._Object IPD._platform ipd_object) ipd_null)) /\
  fn_vars (ipd_body version IPDApply) = [] /\
  fn_body (ipd_body version IPDApply) = Ssequence
    (Sset IPD._platform (Evar IPD._gMarioPlatform ipd_object))
    (Ssequence (ipd_apply_prefix version) (ipd_apply_call version)) /\
  ipd_apply_prefix version = Ssequence (ipd_apply_other_tests version)
    (Sifthenelse (Etempvar IPD._t'1 tint)
      (Sset IPD._t'2 (Ecast (ipd_nonnull IPD._platform ipd_object) tbool))
      (Sset IPD._t'2 (Econst_int Int.zero tint))) /\
  cce_readonly_keep IPD._platform (ipd_apply_other_tests version) = true /\
  ibk_normal (ipd_apply_other_tests version) = true.
Proof. intros []; repeat split; reflexivity. Qed.
