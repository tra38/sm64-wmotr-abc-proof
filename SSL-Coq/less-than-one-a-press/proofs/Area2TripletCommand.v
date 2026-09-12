(** Complete CALL_NATIVE execution for the inactive stock triplet. The
    actual operand determines the actual linked callback. Its allocation
    and cleanup are covered, then the interpreter advances by two words. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_behavior_data jp_behavior_data.
From LessThanOneAPress.Proofs Require Import Area2TripletSpawner
  GameTypes ObjectContactReadback ObjectContactNecessity EyerokRank15LiveMovement
  InkBackwardExecution InkCopyCaller InkScheduledActionSource InkNativeActionHistory
  ContactConsumerExecution UpperElevatorQueryResolution CleanedClightPrograms ClightLinkExecution
  GlobalInterfaceStructural JPSourceSymbolTransport JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SelectedClightTarget
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma tcn_us_source :
  nth_error us_obj_behaviors_2.global_definitions
    (ueqr_definition_index TS._bhv_goomba_triplet_spawner_update us_obj_behaviors_2.global_definitions) =
    Some (TS._bhv_goomba_triplet_spawner_update, Gfun (Internal (ts_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.

Lemma tcn_us_selection : us_normalized_global_definition_map ! TS._bhv_goomba_triplet_spawner_update =
  Some (Gfun (Internal (ts_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 24 us_units).
    + exact (us_nlist_at_nIn _ 24 us_units).
    + eapply nth_error_In. exact tcn_us_source.
Qed.

Lemma tcn_us_no_repair : us_selected_definition_needs_viewport_repair
  (TS._bhv_goomba_triplet_spawner_update, Gfun (Internal (ts_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.

Lemma tcn_us_member :
  In (TS._bhv_goomba_triplet_spawner_update, Gfun (Internal (ts_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite tcn_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact tcn_us_selection.
Qed.

Lemma tcn_jp_source : (prog_defmap (nlist_at 24 jp_cleaned_units)) ! TS._bhv_goomba_triplet_spawner_update =
  Some (Gfun (Internal (ts_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.

Theorem tcn_selected_spawner_resolves : forall version, exists fb,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TS._bhv_goomba_triplet_spawner_update = Some fb /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some (Internal (ts_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact tcn_us_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 24 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 24 jp_cleaned_units).
    + exact tcn_jp_source.
Qed.

Definition tcn_prefix := Ssequence (Sset ISN._t'2 isn_global)
  (Ssequence (Sset ISN._t'3 isn_operand) (Sset ISN._behaviorFunc isn_cast)).
Definition tcn_locals le command ofs callback :=
  PTree.set ISN._behaviorFunc (Vptr callback Ptrofs.zero)
    (PTree.set ISN._t'3 (Vptr callback Ptrofs.zero)
      (PTree.set ISN._t'2 (Vptr command ofs) le)).
Definition tcn_advance := Ssequence (Sset ISN._t'1 isn_global)
  (Sassign isn_global (Ebinop Oadd (Etempvar ISN._t'1 (tptr tuint))
    (Econst_int (Int.repr 2) tint) (tptr tuint))).
Definition tcn_tail := Ssequence tcn_advance (Sreturn (Some (Econst_int Int.zero tint))).

Lemma tcn_source : forall version,
  fn_body (isn_body version) = Ssequence tcn_prefix (Ssequence isn_call tcn_tail) /\
  ocr_readonly_prefix tcn_prefix = true /\ ibk_normal tcn_prefix = true /\
  nth_error (gvar_init (match version with
    | VersionUS => us_behavior_data.v_bhvGoombaTripletSpawner
    | VersionJP => jp_behavior_data.v_bhvGoombaTripletSpawner end)) 5 =
      Some (Init_addrof TS._bhv_goomba_triplet_spawner_update Ptrofs.zero).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma tcn_prefix_executes : forall version le m cell command ofs callback,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) ISN._gCurBhvCommand = Some cell ->
  Mem.load Mint32 m cell 0 = Some (Vptr command ofs) ->
  Mem.load Mint32 m command (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4))) =
    Some (Vptr callback Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    tcn_prefix E0 (tcn_locals le command ofs callback) m Out_normal.
Proof.
  intros version le m cell command ofs callback Hsymbol Hcommand Hoperand.
  unfold tcn_prefix, tcn_locals.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_Sset. eapply isn_command_read; eauto.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply isn_operand_read; [apply PTree.gss|exact Hoperand].
    + apply exec_Sset. unfold isn_cast. eapply eval_Ecast;
        [apply eval_Etempvar; apply PTree.gss|reflexivity].
Qed.

Lemma tcn_empty_entry : forall version ge m e le entry,
  function_entry2 ge (isn_body version) [] m e le entry -> e = empty_env /\ entry = m.
Proof.
  intros version ge m e le entry Hentry.
  assert (Hvars : fn_vars (isn_body version) = []) by (destruct version; reflexivity).
  inversion Hentry; subst.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; auto end.
Qed.

Lemma tcn_tail_stores_next_command : forall version le m cell command ofs t le' after out,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) ISN._gCurBhvCommand = Some cell ->
  Mem.load Mint32 m cell 0 = Some (Vptr command ofs) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m tcn_tail t le' after out ->
  Mem.store Mint32 m cell 0 (Vptr command (Ptrofs.add ofs (Ptrofs.repr 8))) = Some after /\
  t = E0 /\ out = Out_return (Some (Vint Int.zero, tint)).
Proof.
  intros version le m cell command ofs t le' after out Hsymbol Hcommand Hrun.
  unfold tcn_tail, tcn_advance, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ isn_global ?v |- _ =>
    assert (v = Vptr command ofs) by
      (eapply ocr_expr_unique; [exact Hr|eapply isn_command_read; eauto]); subst v end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ _ _ isn_global _ _ _ |- _ =>
    unfold isn_global in Hl; inversion Hl; subst; clear Hl; try discriminate end.
  match goal with Hs : Genv.find_symbol _ ISN._gCurBhvCommand = Some ?found |- _ =>
    assert (found = cell) by congruence; subst found end.
  match goal with Hr : eval_expr ?ge ?e ?locals ?memory (Ebinop Oadd _ _ _) ?v |- _ =>
    assert (v = Vptr command (Ptrofs.add ofs (Ptrofs.repr 8))) by
      (eapply ocr_expr_unique; [exact Hr|eapply eval_Ebinop;
        [apply eval_Etempvar; apply PTree.gss|constructor|reflexivity]]); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) ?v |- _ =>
    apply ocn_const_int_value in Hr; subst v end.
  repeat split; try assumption; reflexivity.
Qed.

Definition TripletNativeCommandPreservation : Prop :=
  forall version m cell command ofs callback cb ob oo distance t after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) ISN._gCurBhvCommand = Some cell ->
  Mem.load Mint32 m cell 0 = Some (Vptr command ofs) ->
  Mem.load Mint32 m command (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4))) =
    Some (Vptr callback Ptrofs.zero) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TS._bhv_goomba_triplet_spawner_update = Some callback ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TS._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 49))) = Some (Vint Int.zero) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 53))) = Some (Vsingle distance) ->
  Float32.cmp Clt distance ts_threshold = false ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Internal (isn_body version)) [] t after result ->
  t = E0 /\ result = Vint Int.zero /\
  Mem.load Mint32 after cell 0 = Some (Vptr command (Ptrofs.add ofs (Ptrofs.repr 8))) /\
  (forall chunk b offset, Mem.valid_block m b -> b <> cell ->
    Mem.load chunk after b offset = Mem.load chunk m b offset).

Theorem tcn_native_command_preserves_parent_and_advances : TripletNativeCommandPreservation.
Proof.
  intros version m cell command ofs callback cb ob oo distance t after result
    Hsymbol Hcommand Hoperand Hcallback HcurrentSymbol Hcurrent Haction Hdistance Hfar Hcall.
  inversion Hcall; subst; clear Hcall.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (tcn_empty_entry _ _ _ _ _ _ He) as (-> & ->) end.
  match goal with Hfree : Mem.free_list ?memory (blocks_of_env _ empty_env) = Some after |- _ =>
    change (Some memory = Some after) in Hfree; inversion Hfree; subst end.
  destruct (tcn_source version) as (Hbody & Hreadonly & Hnormal & _).
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body (isn_body _)) _ _ _ _ |- _ =>
    rewrite Hbody in Hrun;
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
      as (middle & memory & pre & rest & Htrace & Hprefix & Hrest) end.
  pose proof (tcn_prefix_executes version le1 m cell command ofs callback Hsymbol Hcommand Hoperand) as Hbuilt.
  destruct (ocr_readonly_unique _ _ _ _ _ _ _ _ _ Hprefix Hreadonly _ _ _ _ Hbuilt)
    as (-> & -> & -> & _).
  destruct (ibk_split_sequence _ _ _ _ isn_call _ _ _ _ _ eq_refl Hrest)
    as (callee_le & callee_memory & ct & st & HrestTrace & Hnative & Htail).
  unfold isn_call in Hnative. inversion Hnative; subst; clear Hnative.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar ISN._behaviorFunc _) ?vf |- _ =>
    assert (vf = Vptr callback Ptrofs.zero) by
      (eapply ocn_temp_value; [exact Hr|unfold tcn_locals; apply PTree.gss]); subst vf end.
  match goal with Hargs : eval_exprlist _ _ _ _ [] [] _ |- _ => inversion Hargs; subst end.
  destruct (tcn_selected_spawner_resolves version) as (fb & Hfs & Hff).
  assert (fb = callback) by congruence. subst fb.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) callback = Some fd) in Hfind;
    rewrite Hff in Hfind; inversion Hfind; subst fd end.
  match goal with Hnative : ClightBigstep.eval_funcall _ _ _ (Internal (ts_body _)) _ _ _ _ |- _ =>
    destruct (ts_complete_native_call_preserves_existing_cells _ _ _ _ _ _ _ _ _
      HcurrentSymbol Hcurrent Haction Hdistance Hfar Hnative) as (Ht & Hframe); subst ct end.
  assert (HcommandAfter : Mem.load Mint32 callee_memory cell 0 = Some (Vptr command ofs)).
  { rewrite Hframe; [exact Hcommand|eapply ibcc_loaded_block_valid; exact Hcommand]. }
  destruct (tcn_tail_stores_next_command _ _ _ _ _ _ _ _ _ _ Hsymbol HcommandAfter Htail)
    as (Hstore & Hsilent & Hreturn). subst st.
  subst out.
  match goal with Hr : outcome_result_value _ _ _ _ |- _ =>
    replace (fn_return (isn_body version)) with tint in Hr by (destruct version; reflexivity);
    cbn in Hr; destruct Hr as [_ Hr]; inversion Hr; subst result end.
  split; [reflexivity|]. split; [reflexivity|].
  split.
  - erewrite Mem.load_store_same by exact Hstore. reflexivity.
  - intros chunk b offset Hb Hnot. erewrite Mem.load_store_other by (first [exact Hstore|left; exact Hnot]).
    apply Hframe. exact Hb.
Qed.
