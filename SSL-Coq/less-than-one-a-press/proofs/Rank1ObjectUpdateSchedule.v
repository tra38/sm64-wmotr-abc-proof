(** A completed stock object update must execute the actual final platform
    query. Prefix callees may write memory; no harmless-call contract is used.
    This exposes the returned memory and the real remaining scheduler tail,
    rather than assuming that a retained pointer survives that tail. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor jp_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes InkPlatformSource
  InkBackwardExecution ObjectContactNecessity Area2Rank12BContact
  SecretContactExecution SelectedClightTarget UpperElevatorQueryResolution
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module R1S := us_object_list_processor.

Definition r1s_body version := match version with
| VersionUS => us_object_list_processor.f_update_objects
| VersionJP => jp_object_list_processor.f_update_objects end.
Definition r1s_before version := ocn_prefix_items 20 (fn_body (r1s_body version)).
Definition r1s_after version := rank12b_drop_sequences 21 (fn_body (r1s_body version)).
Definition r1s_query := Scall None
  (Evar IPD._update_mario_platform (Tfunction [] tvoid cc_default)) [].

Lemma r1s_actual_source_order : forall version,
  fn_body (r1s_body version) =
    ocn_prepend (r1s_before version) (Ssequence r1s_query (r1s_after version)) /\
  forallb ibk_normal (r1s_before version) = true.
Proof. intros []; split; reflexivity. Qed.

Lemma r1s_us_source :
  nth_error R1S.global_definitions
    (ueqr_definition_index R1S._update_objects R1S.global_definitions) =
    Some (R1S._update_objects, Gfun (Internal (r1s_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma r1s_us_member :
  In (R1S._update_objects, Gfun (Internal (r1s_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 13 us_units).
  - exact (us_nlist_at_nIn _ 13 us_units).
  - eapply nth_error_In. exact r1s_us_source.
Qed.
Lemma r1s_us_selection :
  us_normalized_global_definition_map ! R1S._update_objects =
    Some (Gfun (Internal (r1s_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact r1s_us_member.
Qed.
Lemma r1s_us_selected_member :
  In (R1S._update_objects, Gfun (Internal (r1s_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition.
    assert (us_selected_definition_needs_viewport_repair
      (R1S._update_objects, Gfun (Internal (r1s_body VersionUS))) = false) as Hrepair
      by (vm_compute; reflexivity).
    rewrite Hrepair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact r1s_us_selection.
Qed.
Lemma r1s_jp_source :
  (prog_defmap (nlist_at 13 jp_cleaned_units)) ! R1S._update_objects =
    Some (Gfun (Internal (r1s_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem r1s_selected_update_resolves : forall version,
  exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) R1S._update_objects = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (r1s_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact r1s_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 13 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 13 jp_cleaned_units).
    + exact r1s_jp_source.
Qed.

Lemma r1s_call_is_real_platform_update : forall version e le m t le' m' out,
  e ! IPD._update_mario_platform = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    r1s_query t le' m' out ->
  exists result,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ipd_body version IPDUpdate)) [] t m' result /\
    le' = le /\ out = Out_normal.
Proof.
  intros version e le m t le' m' out Hlocal Hrun.
  unfold r1s_query, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (ipd_selected_bodies_resolve version IPDUpdate) as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hr : eval_exprlist _ _ _ _ [] _ _ |- _ => inversion Hr; subst end.
  eexists. repeat split; try reflexivity; eassumption.
Qed.

Definition Rank1MandatoryFinalPlatformQuery : Prop :=
  forall version e le m t le' m' out,
  e ! IPD._update_mario_platform = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (r1s_body version)) t le' m' out ->
  exists query_le query_m returned_m result prefix query_trace tail_trace,
    t = prefix ++ (query_trace ++ tail_trace) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ocn_prepend (r1s_before version) Sskip) prefix query_le query_m Out_normal /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      query_m (Internal (ipd_body version IPDUpdate)) [] query_trace returned_m result /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e query_le returned_m
      (r1s_after version) tail_trace le' m' out.

Theorem r1s_completed_update_must_query : Rank1MandatoryFinalPlatformQuery.
Proof.
  intros version e le m t le' m' out Hlocal Hrun.
  destruct (r1s_actual_source_order version) as [Hbody Hnormal]. rewrite Hbody in Hrun.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (query_le & query_m & prefix & rest & Htrace & Hprefix & Hrest).
  destruct (ibk_split_sequence _ _ _ _ r1s_query _ _ _ _ _ eq_refl Hrest)
    as (returned_le & returned_m & query_trace & tail_trace & HrestTrace & Hquery & Htail).
  destruct (r1s_call_is_real_platform_update _ _ _ _ _ _ _ _ Hlocal Hquery)
    as (result & Hcall & -> & _).
  exists query_le, query_m, returned_m, result, prefix, query_trace, tail_trace.
  split; [subst; reflexivity|]. repeat split; assumption.
Qed.

(** Remove the local-name premise at a genuine update_objects call: its only
    allocated local is the clock array, which cannot shadow the query name.
    Allocation/free memory is kept explicit in the witnesses. *)
Definition Rank1CompletedObjectUpdateQuery : Prop :=
  forall version m unused t after result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (r1s_body version)) [unused] t after result ->
  exists environment locals allocated final_locals final_memory outcome
      query_le query_m returned_m query_result prefix query_trace tail_trace,
    ocn_exec (Clight.globalenv (selected_clight_target version)) environment
      locals allocated (fn_body (r1s_body version)) t final_locals final_memory outcome /\
    Mem.free_list final_memory
      (blocks_of_env (Clight.globalenv (selected_clight_target version)) environment) = Some after /\
    t = prefix ++ (query_trace ++ tail_trace) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) environment locals allocated
      (ocn_prepend (r1s_before version) Sskip) prefix query_le query_m Out_normal /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      query_m (Internal (ipd_body version IPDUpdate)) [] query_trace returned_m query_result /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) environment query_le returned_m
      (r1s_after version) tail_trace final_locals final_memory outcome.

Theorem r1s_actual_completed_call_must_query : Rank1CompletedObjectUpdateQuery.
Proof.
  intros version m unused t after result Hcall.
  assert (fn_vars (r1s_body version) = [(R1S._cycleCounts, tarray tlong 30)])
    as Hvars by (destruct version; reflexivity).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ ?e ?le ?allocated |- _ =>
    assert (e ! IPD._update_mario_platform = None) as Hlocal;
    [inversion Hentry; subst; clear Hentry;
      match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
        rewrite Hvars in Ha; inversion Ha; subst; clear Ha end;
      match goal with Ha : alloc_variables _ _ _ [] _ _ |- _ =>
        inversion Ha; subst; clear Ha end;
      rewrite PTree.gso by discriminate; apply PTree.gempty
    |] end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ ?e ?le ?allocated _ ?tr ?final ?final_m ?out |- _ =>
    destruct (r1s_completed_update_must_query version e le allocated tr final final_m out Hlocal Hrun)
      as (query_le & query_m & returned_m & query_result & prefix & query_trace & tail_trace &
        Htrace & Hprefix & Hquery & Htail);
    exists e, le, allocated, final, final_m, out,
      query_le, query_m, returned_m, query_result, prefix, query_trace, tail_trace;
    repeat split; eassumption end.
Qed.
