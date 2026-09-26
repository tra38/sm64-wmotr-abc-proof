(** The two sliding tests reached by landing cancellation are real read-only calls. *)
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

From LessThanOneAPress.Proofs Require Import InkLandingCallerSource.

From LessThanOneAPress.Generated Require Import us_mario jp_mario us_mario_step jp_mario_step.
From LessThanOneAPress.Proofs Require Import InkLandingCallerGate InkLandingHistoryGate.
Local Open Scope Z_scope.

Inductive InkLandingReadOnlyHelper := ILRDownhill | ILRSlide.
Definition ilr_body version kind := match version, kind with
| VersionUS, ILRDownhill => us_mario.f_mario_facing_downhill
| VersionJP, ILRDownhill => jp_mario.f_mario_facing_downhill
| VersionUS, ILRSlide => us_mario_actions_moving.f_should_begin_sliding
| VersionJP, ILRSlide => jp_mario_actions_moving.f_should_begin_sliding end.
Definition ilr_ident kind := match kind with
| ILRDownhill => IMB._mario_facing_downhill
| ILRSlide => IMB._should_begin_sliding end.
Definition ilr_unit kind : nat := match kind with ILRDownhill => 1 | ILRSlide => 5 end.
Definition ilr_us_definitions kind := match kind with
| ILRDownhill => us_mario.global_definitions
| ILRSlide => us_mario_actions_moving.global_definitions end.
Lemma ilr_us_source : forall kind,
  nth_error (ilr_us_definitions kind)
    (ueqr_definition_index (ilr_ident kind) (ilr_us_definitions kind)) =
  Some (ilr_ident kind, Gfun (Internal (ilr_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ilr_us_member : forall kind,
  In (ilr_ident kind, Gfun (Internal (ilr_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind.
  assert (prog_defs (us_nlist_at (ilr_unit kind) us_units) =
    ilr_us_definitions kind) as Hunit by (destruct kind; reflexivity).
  eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (ilr_unit kind) us_units).
  - exact (us_nlist_at_nIn _ (ilr_unit kind) us_units).
  - rewrite Hunit. eapply nth_error_In. exact (ilr_us_source kind).
Qed.
Lemma ilr_us_selection : forall kind,
  us_normalized_global_definition_map ! (ilr_ident kind) =
    Some (Gfun (Internal (ilr_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ilr_us_member kind).
Qed.
Lemma ilr_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ilr_ident kind, Gfun (Internal (ilr_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definitions normalize_global_definition_map.
Lemma ilr_us_selected_member : forall kind,
  In (ilr_ident kind, Gfun (Internal (ilr_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ilr_us_no_repair. reflexivity.
  - unfold us_normalized_global_definitions.
    pose proof (ilr_us_selection kind) as Hselected.
    unfold us_normalized_global_definition_map in Hselected.
    exact (every_selected_internal_body_is_preserved_verbatim
      (unit_global_definitions us_units) (ilr_ident kind) (ilr_body VersionUS kind)
      Hselected).
Qed.
Lemma ilr_jp_source : forall kind,
  (prog_defmap (nlist_at (ilr_unit kind) jp_cleaned_units)) ! (ilr_ident kind) =
    Some (Gfun (Internal (ilr_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem ilr_selected_helpers_resolve : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ilr_ident kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ilr_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ilr_us_selected_member kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (ilr_unit kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (ilr_unit kind) jp_cleaned_units).
    + exact (ilr_jp_source kind).
Qed.


Local Opaque selected_clight_target.

Lemma ilr_empty_locals : forall version kind,
  fn_vars (ilr_body version kind) = [].
Proof. intros [] []; reflexivity. Qed.

Lemma ilr_call_body : forall version kind m args t m' result,
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ilr_body version kind)) args t m' result ->
  exists le le' out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (fn_body (ilr_body version kind)) t le' m' out.
Proof.
  intros version kind m args t m' result Hrun. inversion Hrun; subst.
  match goal with H : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with H : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite ilr_empty_locals in H; inversion H; subst; clear H end.
  match goal with H : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in H; inversion H; subst end.
  do 3 eexists; eassumption.
Qed.

Lemma ilr_downhill_preserves_memory : forall version m args t m' result,
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ilr_body version ILRDownhill)) args t m' result ->
  t = E0 /\ m' = m.
Proof.
  intros version m args t m' result Hrun.
  destruct (ilr_call_body _ _ _ _ _ _ _ Hrun) as (le & le' & out & Hbody).
  assert (cce_readonly_keep IMB._m (fn_body (ilr_body version ILRDownhill)) = true)
    as Hshape by (destruct version; reflexivity).
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hbody Hshape) as (Ht & Hm & _).
  auto.
Qed.

Definition ilr_type kind := Tfunction
  (match kind with ILRDownhill => [ilw_mario_type; tint] | ILRSlide => [ilw_mario_type] end)
  tint cc_default.

Lemma ilr_named_call_frame : forall version kind,
  (forall m args t m' result,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ilr_body version kind)) args t m' result -> t = E0 /\ m' = m) ->
  forall le m opt args t le' m' out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (Scall opt (Evar (ilr_ident kind) (ilr_type kind)) args) t le' m' out ->
    t = E0 /\ m' = m.
Proof.
  intros version kind Hbody le m opt args t le' m' out Hrun.
  destruct (ilr_selected_helpers_resolve version kind) as (fb & Hsymbol & Hfunction).
  inversion Hrun; subst.
  match goal with H : classify_fun _ = _ |- _ => cbn [ilr_type] in H; inversion H; subst end.
  match goal with H : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (eapply (sce_function_name_value
        (Clight.globalenv (selected_clight_target version)) empty_env le m
        (ilr_ident kind)
        (match kind with ILRDownhill => [ilw_mario_type; tint] | ILRSlide => [ilw_mario_type] end)
        tint cc_default fb vf); [apply PTree.gempty|exact Hsymbol|exact H]); subst vf end.
  match goal with H : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in H;
    rewrite Hfunction in H; inversion H; subst fd end.
  eapply Hbody; eassumption.
Qed.


Definition ilr_downhill_name fn := match fn with
| Evar id ty => Pos.eqb id IMB._mario_facing_downhill &&
    (if type_eq ty (ilr_type ILRDownhill) then true else false)
| _ => false end.
Fixpoint ilr_readonly_stmt s : bool := match s with
| Sskip | Sset _ _ | Sbreak | Scontinue | Sreturn _ => true
| Scall _ fn _ => ilr_downhill_name fn
| Ssequence a b | Sifthenelse _ a b => ilr_readonly_stmt a && ilr_readonly_stmt b
| _ => false end.

Lemma ilr_checked_statements_preserve_memory : forall version s le m t le' m' out,
  ilr_readonly_stmt s = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    s t le' m' out -> t = E0 /\ m' = m.
Proof.
  intros version s. induction s; intros le m tr le' m' out Hshape Hrun;
    cbn [ilr_readonly_stmt] in Hshape; try discriminate.
  - inversion Hrun; subst; auto.
  - inversion Hrun; subst; auto.
  - unfold ilr_downhill_name in Hshape. destruct e; try discriminate.
    apply andb_true_iff in Hshape as [Hid Hty]. apply Pos.eqb_eq in Hid; subst i.
    destruct (type_eq t (ilr_type ILRDownhill)); try discriminate. subst t.
    eapply ilr_named_call_frame; [exact (ilr_downhill_preserves_memory version)|exact Hrun].
  - apply andb_true_iff in Hshape as [Ha Hb]. inversion Hrun; subst.
    + match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ s1 _ _ _ _,
        Hlast : ClightBigstep.exec_stmt _ _ _ _ _ s2 _ _ _ _ |- _ =>
        destruct (IHs1 _ _ _ _ _ _ Ha Hfirst) as [-> ->];
        destruct (IHs2 _ _ _ _ _ _ Hb Hlast) as [-> ->] end. auto.
    + eapply IHs1; eassumption.
  - apply andb_true_iff in Hshape as [Ha Hb]. inversion Hrun; subst.
    destruct b; [eapply IHs1|eapply IHs2]; eassumption.
  - inversion Hrun; subst; auto.
  - inversion Hrun; subst; auto.
  - inversion Hrun; subst; auto.
Qed.
Theorem ilr_sliding_test_preserves_memory : forall version m args t m' result,
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ilr_body version ILRSlide)) args t m' result ->
  t = E0 /\ m' = m.
Proof.
  intros version m args t m' result Hrun.
  destruct (ilr_call_body _ _ _ _ _ _ _ Hrun) as (le & le' & out & Hbody).
  eapply ilr_checked_statements_preserve_memory; [|exact Hbody].
  destruct version; reflexivity.
Qed.

Corollary ilr_sliding_call_preserves_memory : forall version le m opt args t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Scall opt (Evar IMB._should_begin_sliding (ilr_type ILRSlide)) args)
    t le' m' out -> t = E0 /\ m' = m.
Proof.
  intros. eapply ilr_named_call_frame;
    [exact (ilr_sliding_test_preserves_memory version)|exact H].
Qed.
