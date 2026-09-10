(** Connect the milestone helper's frame to a real named call in the
    selected program. Resolution is derived from the linked definitions,
    rather than accepted as an outside-call effect. *)
From Coq Require Import List.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkStarDialogFrame
  InkSharedReadings OrdinaryArea1EntryMemory ObjectContactNecessity
  SecretContactExecution UpperElevatorQueryResolution ContactConsumerSource
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.

Lemma isd_us_check_source :
  nth_error ISD.global_definitions
    (ueqr_definition_index ISD._get_star_collection_dialog ISD.global_definitions) =
  Some (ISD._get_star_collection_dialog, Gfun (Internal (isd_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.

Lemma isd_us_check_member :
  In (ISD._get_star_collection_dialog, Gfun (Internal (isd_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 4 us_units).
  - exact (us_nlist_at_nIn _ 4 us_units).
  - eapply nth_error_In. exact isd_us_check_source.
Qed.

Lemma isd_us_check_selection :
  PTree.get ISD._get_star_collection_dialog us_normalized_global_definition_map =
    Some (Gfun (Internal (isd_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact isd_us_check_member.
Qed.

Lemma isd_us_check_no_repair : us_selected_definition_needs_viewport_repair
  (ISD._get_star_collection_dialog, Gfun (Internal (isd_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.

Lemma isd_us_check_selected_member :
  In (ISD._get_star_collection_dialog, Gfun (Internal (isd_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite isd_us_check_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact isd_us_check_selection.
Qed.

Lemma isd_jp_check_source :
  PTree.get ISD._get_star_collection_dialog (prog_defmap (nlist_at 4 jp_cleaned_units)) =
    Some (Gfun (Internal (isd_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.

Theorem isd_selected_check_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISD._get_star_collection_dialog = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (isd_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact isd_us_check_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 4 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 4 jp_cleaned_units).
    + exact isd_jp_check_source.
Qed.

Definition isd_call temp := Scall (Some temp)
  (Evar ISD._get_star_collection_dialog
    (Tfunction [tptr (Tstruct ISD._MarioState noattr)] tint cc_default))
  [Etempvar ISD._m (tptr (Tstruct ISD._MarioState noattr))].

Lemma isd_actual_named_call : forall version le m temp t le' m' out mb,
  le ! ISD._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (isd_call temp) t le' m' out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m (Internal (isd_body version))
    [Vptr mb Ptrofs.zero] t m' result.
Proof.
  intros version le m temp t le' m' out mb Hm Hcall.
  unfold isd_call in Hcall. inversion Hcall; subst; clear Hcall.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (isd_selected_check_resolves version) as (fb & Hfs & Hff).
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar ?id (Tfunction ?args ?result ?cc)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory id args result cc fb vf
        eq_refl Hfs Hr)); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hff in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hargs : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Hargs; subst; clear Hargs end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vptr mb Ptrofs.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  eexists; eassumption.
Qed.

Definition InkMilestoneNamedCallFrame : Prop :=
  forall version le m temp t le' m' out a,
  le ! ISD._m = Some (Vptr (area1_state_storage_block a) Ptrofs.zero) ->
  area1_state_storage_block a <> area1_object_pool_block a ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (isd_call temp) t le' m' out ->
  t = E0 /\ InkSameReadings a m m'.

Theorem isd_named_call_preserves_shared_readings : InkMilestoneNamedCallFrame.
Proof.
  intros version le m temp t le' m' out a Hm Hseparate Hcall.
  destruct (isd_actual_named_call _ _ _ _ _ _ _ _ _ Hm Hcall) as [result Hbody].
  eapply isd_milestone_check_preserves_shared_readings; eauto.
Qed.
