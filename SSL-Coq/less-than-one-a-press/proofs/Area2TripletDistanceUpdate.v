(** Connect cur_obj_update's actual distance call and field store to the
    live helper. The post-call current-object read is kept visible: the
    unresolved sqrtf may not simply be assumed to preserve it. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_behavior_script jp_behavior_script.
From LessThanOneAPress.Proofs Require Import Area2TripletSpawner Area2TripletDistance
  GameTypes ObjectContactReadback ObjectContactNecessity EyerokRank15LiveMovement
  InkBackwardExecution InkRawCopyExpressions ContactConsumerExecution SecretContactExecution
  UpperElevatorQueryResolution CleanedClightPrograms ClightLinkExecution
  GlobalInterfaceStructural JPSourceSymbolTransport JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SelectedClightTarget
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module TU := us_behavior_script.

Lemma tdu_us_source :
  nth_error us_object_helpers.global_definitions
    (ueqr_definition_index TD._dist_between_objects us_object_helpers.global_definitions) =
    Some (TD._dist_between_objects, Gfun (Internal (ts_distance_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.

Lemma tdu_us_selection : us_normalized_global_definition_map ! TD._dist_between_objects =
  Some (Gfun (Internal (ts_distance_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 19 us_units).
    + exact (us_nlist_at_nIn _ 19 us_units).
    + eapply nth_error_In. exact tdu_us_source.
Qed.

Lemma tdu_us_no_repair : us_selected_definition_needs_viewport_repair
  (TD._dist_between_objects, Gfun (Internal (ts_distance_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.

Lemma tdu_us_member :
  In (TD._dist_between_objects, Gfun (Internal (ts_distance_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite tdu_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact tdu_us_selection.
Qed.

Lemma tdu_jp_source : (prog_defmap (nlist_at 19 jp_cleaned_units)) ! TD._dist_between_objects =
  Some (Gfun (Internal (ts_distance_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.

Theorem tdu_selected_distance_resolves : forall version, exists fb,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._dist_between_objects = Some fb /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb =
    Some (Internal (ts_distance_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact tdu_us_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 19 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 19 jp_cleaned_units).
    + exact tdu_jp_source.
Qed.

Definition tdu_object := tptr (Tstruct TU._Object noattr).
Definition tdu_current := Evar TU._gCurrentObject tdu_object.
Definition tdu_mario := Evar TU._gMarioObject tdu_object.
Definition tdu_query := Ssequence (Sset TU._t'68 tdu_current)
  (Ssequence (Sset TU._t'69 tdu_mario)
    (Scall (Some TU._t'1)
      (Evar TU._dist_between_objects (Tfunction [tdu_object; tdu_object] tfloat cc_default))
      [Etempvar TU._t'68 tdu_object; Etempvar TU._t'69 tdu_object])).
Definition tdu_store version := Ssequence (Sset TU._t'67 tdu_current)
  (Sassign (rank15_raw_float_expression version TU._t'67 (Econst_int (Int.repr 53) tint))
    (Etempvar TU._t'1 tfloat)).
Definition tdu_body version := match version with
| VersionUS => us_behavior_script.f_cur_obj_update
| VersionJP => jp_behavior_script.f_cur_obj_update end.
Definition tdu_distance_stage version := match fn_body (tdu_body version) with
| Ssequence _ (Ssequence (Sifthenelse _ (Ssequence stage _) _) _) => stage
| _ => Sskip end.
Definition tdu_query_locals le ab ao bb bo result :=
  PTree.set TU._t'1 result (PTree.set TU._t'69 (Vptr bb bo)
    (PTree.set TU._t'68 (Vptr ab ao) le)).

Lemma tdu_generated_stage : forall version,
  tdu_distance_stage version = Ssequence tdu_query (tdu_store version) /\
  ibk_normal tdu_query = true.
Proof. intros []; split; reflexivity. Qed.

Lemma tdu_query_uses_live_objects : forall version e le m cb mb ab ao bb bo t le' after out,
  e ! TU._gCurrentObject = None -> e ! TU._gMarioObject = None -> e ! TU._dist_between_objects = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gCurrentObject = Some cb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gMarioObject = Some mb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ab ao) -> Mem.load Mint32 m mb 0 = Some (Vptr bb bo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m tdu_query t le' after out ->
  exists result,
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ts_distance_body version)) [Vptr ab ao; Vptr bb bo] t after result /\
    le' = tdu_query_locals le ab ao bb bo result /\ out = Out_normal.
Proof.
  intros version e le m cb mb ab ao bb bo t le' after out Hlc Hlm Hlf Hsc Hsm Hc Hm Hrun.
  unfold tdu_query, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ tdu_current ?v |- _ =>
    assert (v = Vptr ab ao) by (eapply irc_global_pointer_read;
      [exact Hlc|exact Hsc|exact Hc|exact Hr]); subst v end.
  all: match goal with Hr : eval_expr _ _ _ _ tdu_mario ?v |- _ =>
    assert (v = Vptr bb bo) by (eapply irc_global_pointer_read;
      [exact Hlm|exact Hsm|exact Hm|exact Hr]); subst v end.
  all: match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ _ |- _ =>
    inversion Hcall; subst; clear Hcall end.
  all: try contradiction.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (tdu_selected_distance_resolves version) as (fb & Hsymbol & Hfun).
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hr : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Hr; subst; clear Hr end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar TU._t'68 _) ?v |- _ =>
    assert (v = Vptr ab ao) by (eapply ocn_temp_value; [exact Hr|
      rewrite PTree.gso by discriminate; apply PTree.gss]); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar TU._t'69 _) ?v |- _ =>
    assert (v = Vptr bb bo) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst v end.
  repeat match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  eexists. repeat split; eauto.
Qed.

Lemma tdu_store_is_silent : forall version ge e le m t le' after out,
  ocn_exec ge e le m (tdu_store version) t le' after out -> t = E0 /\ out = Out_normal.
Proof.
  intros version ge e le m t le' after out Hrun.
  unfold tdu_store, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end; auto.
Qed.

Lemma tdu_store_uses_postcall_current : forall version e le m cb ob oo value t le' after out,
  e ! TU._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) -> le ! TU._t'1 = Some value ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (tdu_store version) t le' after out ->
  Mem.store Mfloat32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 53))) value = Some after.
Proof.
  intros version e le m cb ob oo value t le' after out Hlocal Hsymbol Hcurrent Hvalue Hrun.
  unfold tdu_store, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ tdu_current ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply irc_global_pointer_read; eauto); subst v end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue ?ge ?env ?locals ?memory
      (rank15_raw_float_expression _ _ _) _ _ _ |- _ =>
    destruct ((proj2 (ocr_expression_lvalue_unique ge env locals memory)) _ _ _ _ Hl
      ob (rank15_raw_address oo (Int.repr 53)) Full
      (rank15_raw_float_lvalue version env locals memory TU._t'67
        (Econst_int (Int.repr 53) tint) (Int.repr 53) ob oo
        (PTree.gss _ _ _) (eval_Econst_int _ _ _ _ _ _) eq_refl)) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar TU._t'1 tfloat) ?v |- _ =>
    assert (v = value) by (eapply ocn_temp_value; [exact Hr|
      rewrite PTree.gso by discriminate; exact Hvalue]); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    apply td_float_cast_identity in Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  assumption.
Qed.

(** The caller, internal helper, sqrtf call and store belong to the same
    supplied execution. Retention of the current-object pointer is checked
    in sqrtf's output memory, not assumed for that external. *)
Definition TripletLiveDistanceStore : Prop :=
  forall version e le m cb mb ab ao a bb bo b t le' after out,
  e ! TU._gCurrentObject = None -> e ! TU._gMarioObject = None -> e ! TU._dist_between_objects = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gCurrentObject = Some cb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gMarioObject = Some mb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ab ao) -> Mem.load Mint32 m mb 0 = Some (Vptr bb bo) ->
  td_position m ab ao a -> td_position m bb bo b ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (tdu_distance_stage version) t le' after out ->
  exists fb fd value call_memory,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m fd
      [Vsingle (td_squared a b)] t call_memory value /\
    (forall target offset, Mem.load Mint32 call_memory cb 0 = Some (Vptr target offset) ->
      Mem.store Mfloat32 call_memory target
        (Ptrofs.unsigned (rank15_raw_address offset (Int.repr 53))) value = Some after) /\
    out = Out_normal.

Theorem tdu_live_distance_reaches_field_store : TripletLiveDistanceStore.
Proof.
  intros version e le m cb mb ab ao a bb bo b t le' after out
    Hlc Hlm Hlf Hsc Hsm Hc Hm Ha Hb Hrun.
  rewrite (proj1 (tdu_generated_stage version)) in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ (proj2 (tdu_generated_stage version)) Hrun)
    as (middle & memory & pre & suf & Htrace & Hquery & Hstore).
  destruct (tdu_query_uses_live_objects _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hlc Hlm Hlf Hsc Hsm Hc Hm Hquery) as (value & Hcall & Hlocals & Hout).
  subst middle.
  destruct (tdu_store_is_silent _ _ _ _ _ _ _ _ _ Hstore) as (-> & ->).
  unfold Eapp in Htrace. rewrite app_nil_r in Htrace. subst t.
  destruct (td_live_distance_call_reduces_to_sqrt _ _ _ _ _ _ _ _ _ _ _ Ha Hb Hcall)
    as (fb & fd & Hsymbol & Hfun & Htype & Hsqrt).
  exists fb, fd, value, memory. repeat split; try assumption; try reflexivity.
  intros target offset Hpost.
  eapply tdu_store_uses_postcall_current; [exact Hlc|exact Hsc|exact Hpost| |exact Hstore].
  unfold tdu_query_locals. apply PTree.gss.
Qed.
