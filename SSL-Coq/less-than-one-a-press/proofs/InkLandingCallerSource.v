(** The nine real common-landing wrappers cannot skip their cancellation guard.
    This connects caller execution to a real common_landing_cancels return;
    it does not assume a stock timer bound or harmless intervening calls. *)
From Coq Require Import Bool List Lia ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts ActionDepthAliasCensus
  ZeroAQuicksandEntryBoundary InkLandingHistorySource InkLandingHistory
  InkLandingHistoryReturn InkMovingBackwardSource InkBackwardSource
  InkBackwardExecution InkFloorResetExecution ObjectContactNecessity
  ContactConsumerExecution SecretContactExecution
  Area2Rank12BContact UpperElevatorQueryResolution ContactConsumerSource
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition ilw_kinds : list stock_landing_kind :=
  [StockJumpLand; StockFreefallLand; StockSideFlipLand; StockHoldJumpLand; StockHoldFreefallLand; StockLongJumpLand; StockDoubleJumpLand; StockTripleJumpLand; StockBackflipLand].
Definition ilw_ident kind := match kind with
| StockJumpLand => IMB._act_jump_land
| StockFreefallLand => IMB._act_freefall_land
| StockSideFlipLand => IMB._act_side_flip_land
| StockHoldJumpLand => IMB._act_hold_jump_land
| StockHoldFreefallLand => IMB._act_hold_freefall_land
| StockLongJumpLand => IMB._act_long_jump_land
| StockDoubleJumpLand => IMB._act_double_jump_land
| StockTripleJumpLand => IMB._act_triple_jump_land
| StockBackflipLand => IMB._act_backflip_land
end.
Definition ilw_body version kind := match version, kind with
| VersionUS, StockJumpLand => IMB.f_act_jump_land
| VersionJP, StockJumpLand => jp_mario_actions_moving.f_act_jump_land
| VersionUS, StockFreefallLand => IMB.f_act_freefall_land
| VersionJP, StockFreefallLand => jp_mario_actions_moving.f_act_freefall_land
| VersionUS, StockSideFlipLand => IMB.f_act_side_flip_land
| VersionJP, StockSideFlipLand => jp_mario_actions_moving.f_act_side_flip_land
| VersionUS, StockHoldJumpLand => IMB.f_act_hold_jump_land
| VersionJP, StockHoldJumpLand => jp_mario_actions_moving.f_act_hold_jump_land
| VersionUS, StockHoldFreefallLand => IMB.f_act_hold_freefall_land
| VersionJP, StockHoldFreefallLand => jp_mario_actions_moving.f_act_hold_freefall_land
| VersionUS, StockLongJumpLand => IMB.f_act_long_jump_land
| VersionJP, StockLongJumpLand => jp_mario_actions_moving.f_act_long_jump_land
| VersionUS, StockDoubleJumpLand => IMB.f_act_double_jump_land
| VersionJP, StockDoubleJumpLand => jp_mario_actions_moving.f_act_double_jump_land
| VersionUS, StockTripleJumpLand => IMB.f_act_triple_jump_land
| VersionJP, StockTripleJumpLand => jp_mario_actions_moving.f_act_triple_jump_land
| VersionUS, StockBackflipLand => IMB.f_act_backflip_land
| VersionJP, StockBackflipLand => jp_mario_actions_moving.f_act_backflip_land
end.
Definition ilw_descriptor kind := match kind with
| StockJumpLand => IMB._sJumpLandAction
| StockFreefallLand => IMB._sFreefallLandAction
| StockSideFlipLand => IMB._sSideFlipLandAction
| StockHoldJumpLand => IMB._sHoldJumpLandAction
| StockHoldFreefallLand => IMB._sHoldFreefallLandAction
| StockLongJumpLand => IMB._sLongJumpLandAction
| StockDoubleJumpLand => IMB._sDoubleJumpLandAction
| StockTripleJumpLand => IMB._sTripleJumpLandAction
| StockBackflipLand => IMB._sBackflipLandAction
end.
Definition ilw_callback kind := match kind with
| StockDoubleJumpLand => IMB._set_triple_jump_action
| _ => IMB._set_jumping_action end.
Definition ilw_result_temp kind := match kind with
| StockHoldJumpLand | StockHoldFreefallLand => IMB._t'2
| _ => IMB._t'1 end.
Definition ilw_before_count kind : nat := match kind with
| StockJumpLand | StockFreefallLand | StockSideFlipLand | StockDoubleJumpLand => 0
| _ => 1 end.
Definition ilw_before version kind :=
  ocn_prefix_items (ilw_before_count kind) (fn_body (ilw_body version kind)).
Definition ilw_gate_tail version kind :=
  rank12b_drop_sequences (ilw_before_count kind) (fn_body (ilw_body version kind)).
Definition ilw_guard version kind := ibk_head (ilw_gate_tail version kind).
Definition ilw_after version kind := rank12b_drop_sequences 1 (ilw_gate_tail version kind).
Definition ilw_mario_type := tptr (Tstruct IMB._MarioState noattr).
Definition ilw_descriptor_type := Tstruct IMB._LandingAction noattr.
Definition ilw_callback_type := Tfunction [ilw_mario_type; tuint; tuint] tint cc_default.
Definition ilw_cancel_type := Tfunction
  [ilw_mario_type; tptr ilw_descriptor_type; tptr ilw_callback_type] tint cc_default.
Definition ilw_arguments kind :=
  [Etempvar IMB._m ilw_mario_type;
   Eaddrof (Evar (ilw_descriptor kind) ilw_descriptor_type) (tptr ilw_descriptor_type);
   Evar (ilw_callback kind) ilw_callback_type].
Definition ilw_call kind := Scall (Some (ilw_result_temp kind))
  (Evar IMB._common_landing_cancels ilw_cancel_type) (ilw_arguments kind).
Definition ilw_test kind := Etempvar (ilw_result_temp kind) tint.
Definition ilw_return_one := Sreturn (Some (Econst_int Int.one tint)).

Theorem ilw_all_direct_common_landing_callers :
  internal_statement_predicate_sites (calls_ident_s IMB._common_landing_action)
    us_generated_definitions = map ilw_ident ilw_kinds /\
  internal_statement_predicate_sites (calls_ident_s IMB._common_landing_action)
    jp_generated_definitions_for_alias = map ilw_ident ilw_kinds.
Proof. vm_compute; split; reflexivity. Qed.

Theorem ilw_source_cuts : forall version kind,
  fn_vars (ilw_body version kind) = [] /\
  fn_params (ilw_body version kind) = [(IMB._m, ilw_mario_type)] /\
  fn_body (ilw_body version kind) =
    ocn_prepend (ilw_before version kind)
      (Ssequence (ilw_guard version kind) (ilw_after version kind)) /\
  ilw_guard version kind = Ssequence (ilw_call kind)
    (Sifthenelse (ilw_test kind) ilw_return_one Sskip) /\
  ifr_keeps_temp IMB._m (ocn_prepend (ilw_before version kind) Sskip) = true /\
  calls_ident_s IMB._common_landing_action
    (ocn_prepend (ilw_before version kind) Sskip) = false /\
  calls_ident_s IMB._common_landing_action (ilw_after version kind) = true.
Proof. intros [] []; repeat split; reflexivity. Qed.

Lemma ilw_us_source : forall kind,
  nth_error IMB.global_definitions
    (ueqr_definition_index (ilw_ident kind) IMB.global_definitions) =
  Some (ilw_ident kind, Gfun (Internal (ilw_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ilw_us_member : forall kind,
  In (ilw_ident kind, Gfun (Internal (ilw_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at 5 us_units).
  - exact (us_nlist_at_nIn _ 5 us_units).
  - eapply nth_error_In. exact (ilw_us_source kind).
Qed.
Lemma ilw_us_selection : forall kind,
  us_normalized_global_definition_map ! (ilw_ident kind) =
    Some (Gfun (Internal (ilw_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ilw_us_member kind).
Qed.
Lemma ilw_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ilw_ident kind, Gfun (Internal (ilw_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ilw_us_selected_member : forall kind,
  In (ilw_ident kind, Gfun (Internal (ilw_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions.
  apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ilw_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (ilw_us_selection kind).
Qed.
Lemma ilw_jp_source : forall kind,
  (prog_defmap (nlist_at 5 jp_cleaned_units)) ! (ilw_ident kind) =
    Some (Gfun (Internal (ilw_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem ilw_selected_wrappers_resolve : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ilw_ident kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ilw_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ilw_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 5 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 5 jp_cleaned_units).
    + exact (ilw_jp_source kind).
Qed.
