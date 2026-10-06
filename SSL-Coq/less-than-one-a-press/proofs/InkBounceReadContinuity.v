(** Read continuity in the real falling-bounce handler prefix.

    For INT_HIT_FROM_ABOVE=64, attack_object writes only the actor's attack
    status.  bounce_back_from_attack executes neither of its attack masks,
    so its sound, camera and speed helpers are not reached.  This discharges
    the local read match across the reached attack/back/subtype prefix and
    the ensuing bounce.  The actual classifier return is connected to that
    taken cut.  Earlier contact/dispatch histories and the bounce's own later
    sound/action tail remain separate obligations. *)
From Coq Require Import Bool Lia List ZArith Reals.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_interaction jp_interaction.
From LessThanOneAPress.Proofs Require Import GameTypes InkBounceProducerEffect
  InkBounceApproachGap InkBackwardSource InkBackwardExecution InkCopyCaller
  InkFloorResetSource InkFloorResetExecution InkRawCopyExpressions InkRawCopyCompletion
  InkRawCopyStores InkActionTimerReset Area1PostCopyChildFrame ObjectContactNecessity ObjectContactReadback
  ContactConsumerExecution SecretContactExecution EyerokRank15LiveMovement OrdinaryArea1EntryMemory
  Area2Rank12BContact Area2Rank9ACoinFlight SelectedClightTarget
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module BRC := us_interaction.

Inductive IBRCNative := IBRCattack | IBRCback | IBRCbounce.
Definition ibrc_body version kind := match version,kind with
| VersionUS,IBRCattack => us_interaction.f_attack_object
| VersionJP,IBRCattack => jp_interaction.f_attack_object
| VersionUS,IBRCback => us_interaction.f_bounce_back_from_attack
| VersionJP,IBRCback => jp_interaction.f_bounce_back_from_attack
| VersionUS,IBRCbounce => us_interaction.f_bounce_off_object
| VersionJP,IBRCbounce => jp_interaction.f_bounce_off_object end.
Definition ibrc_ident kind := match kind with
| IBRCattack => BRC._attack_object | IBRCback => BRC._bounce_back_from_attack
| IBRCbounce => BRC._bounce_off_object end.

Lemma ibrc_us_source : forall kind,
  nth_error us_interaction.global_definitions
    (ueqr_definition_index (ibrc_ident kind) us_interaction.global_definitions) =
  Some (ibrc_ident kind,Gfun (Internal (ibrc_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ibrc_us_member : forall kind,
  In (ibrc_ident kind,Gfun (Internal (ibrc_body VersionUS kind)))
    (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union with
    (unit := us_nlist_at 10 us_units).
  - exact (us_nlist_at_nIn _ 10 us_units).
  - eapply nth_error_In. exact (ibrc_us_source kind).
Qed.
Lemma ibrc_us_selection : forall kind,
  us_normalized_global_definition_map ! (ibrc_ident kind) =
    Some (Gfun (Internal (ibrc_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ibrc_us_member kind).
Qed.
Lemma ibrc_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ibrc_ident kind,Gfun (Internal (ibrc_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma ibrc_us_selected : forall kind,
  In (ibrc_ident kind,Gfun (Internal (ibrc_body VersionUS kind)))
    us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ibrc_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact (ibrc_us_selection kind).
Qed.
Lemma ibrc_jp_source : forall kind,
  (prog_defmap (nlist_at 10 jp_cleaned_units)) ! (ibrc_ident kind) =
    Some (Gfun (Internal (ibrc_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem ibrc_selected_native_resolves : forall version kind, exists fb,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ibrc_ident kind) = Some fb /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb =
    Some (Internal (ibrc_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ibrc_us_selected kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 10 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 10 jp_cleaned_units).
    + exact (ibrc_jp_source kind).
Qed.

Definition ibrc_back_guard version (second : bool) :=
  match fn_body (ibrc_body version IBRCback),second with
  | Ssequence (Sifthenelse first _ _) (Sifthenelse last _ _),false => first
  | Ssequence (Sifthenelse first _ _) (Sifthenelse last _ _),true => last
  | _,_ => Econst_int Int.zero tint end.
Definition ibrc_back_effect version (second : bool) :=
  match fn_body (ibrc_body version IBRCback),second with
  | Ssequence (Sifthenelse _ first _) (Sifthenelse _ last _),false => first
  | Ssequence (Sifthenelse _ first _) (Sifthenelse _ last _),true => last
  | _,_ => Sskip end.
Lemma ibrc_back_source : forall version,
  fn_vars (ibrc_body version IBRCback) = [] /\
  fn_params (ibrc_body version IBRCback) =
    [(BRC._m,tptr (Tstruct BRC._MarioState noattr));(BRC._interaction,tuint)] /\
  fn_body (ibrc_body version IBRCback) = Ssequence
    (Sifthenelse (ibrc_back_guard version false) (ibrc_back_effect version false) Sskip)
    (Sifthenelse (ibrc_back_guard version true) (ibrc_back_effect version true) Sskip).
Proof. intros []; repeat split; reflexivity. Qed.

Ltac ibrc_build_mask_read :=
  match goal with
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => apply eval_Econst_int
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ => eapply eval_Etempvar; eassumption
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop; [ibrc_build_mask_read|ibrc_build_mask_read|reflexivity]
  | |- _ => fail 1
  end.

Lemma ibrc_above_masks_evaluate_zero : forall version second ge e le m,
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  eval_expr ge e le m (ibrc_back_guard version second) (Vint Int.zero).
Proof.
  intros [] [] ge e le m Hinteraction;
    cbn [ibrc_back_guard ibrc_body fn_body
      us_interaction.f_bounce_back_from_attack jp_interaction.f_bounce_back_from_attack];
    ibrc_build_mask_read.
Qed.
Lemma ibrc_back_guard_type : forall version second,
  typeof (ibrc_back_guard version second) = tuint.
Proof. intros [] []; reflexivity. Qed.

Theorem ibrc_above_bounce_back_has_no_effect :
  forall version ge m mb mo t after result,
  ClightBigstep.Clight2.eval_funcall ge m (Internal (ibrc_body version IBRCback))
    [Vptr mb mo;Vint (Int.repr 64)] t after result -> t = E0 /\ after = m.
Proof.
  intros version ge m mb mo t after result Hcall.
  destruct (ibrc_back_source version) as (Hvars & Hparams & Hbody).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    rewrite Hparams in Hb; cbn in Hb; inversion Hb; subst temps end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr end.
  cce_unroll_loop_free_exec.
  all: repeat match goal with
  | Hr : eval_expr ?g ?environment ?temps ?memory (ibrc_back_guard ?reached_version ?which) ?v |- _ =>
      assert (v = Vint Int.zero) by
        (eapply ocr_expr_unique; [exact Hr|eapply ibrc_above_masks_evaluate_zero;
          apply PTree.gss]); subst v; clear Hr
  end.
  all: try solve [match goal with Hb : bool_val (Vint Int.zero)
    (typeof (ibrc_back_guard ?rv ?which)) _ = Some true |- _ =>
    rewrite (ibrc_back_guard_type rv which) in Hb; discriminate end].
  all: repeat split; reflexivity.
Qed.

Definition ibrc_attack_switch version := ibk_head
  (rank12b_drop_sequences 1 (fn_body (ibrc_body version IBRCattack))).
Definition ibrc_attack_rest version := rank12b_drop_sequences 2
  (fn_body (ibrc_body version IBRCattack)).
Definition ibrc_status version := ircc_lhs version BRC._o true (Econst_int (Int.repr 43) tint).
Definition ibrc_status_value := Ebinop Oadd (Etempvar BRC._attackType tuint)
  (Ebinop Oor
    (Ebinop Oshl (Econst_int Int.one tint) (Econst_int (Int.repr 15) tint) tint)
    (Ebinop Oshl (Econst_int Int.one tint) (Econst_int (Int.repr 14) tint) tint) tint) tuint.
Lemma ibrc_attack_source : forall version,
  fn_vars (ibrc_body version IBRCattack) = [] /\
  fn_params (ibrc_body version IBRCattack) =
    [(BRC._o,tptr (Tstruct BRC._Object noattr));(BRC._interaction,tint)] /\
  fn_body (ibrc_body version IBRCattack) =
    Ssequence (Sset BRC._attackType (Econst_int Int.zero tint))
      (Ssequence (ibrc_attack_switch version) (ibrc_attack_rest version)) /\
  ibrc_attack_rest version = Ssequence (Sassign (ibrc_status version) ibrc_status_value)
    (Sreturn (Some (Etempvar BRC._attackType tuint))).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ibrc_status_location : forall version e le m ob oo b offset bf,
  le ! BRC._o = Some (Vptr ob oo) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (ibrc_status version) b offset bf ->
  b = ob /\ offset = Ptrofs.add oo (Ptrofs.repr 308) /\ bf = Full.
Proof.
  intros version e le m ob oo b offset bf Ho Hl.
  unfold ibrc_status, ircc_lhs in Hl. inversion Hl; subst.
  match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion Hr; subst; clear Hr end.
  - match goal with Hr : eval_expr _ _ _ _ (ircc_array _ _ _) ?v |- _ =>
      assert (v = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136))) by
        (eapply ircc_array_value; eauto); subst v end.
    match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hr; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn [typeof ircc_array pcc_scalar] in Hsem; inversion Hsem; subst end.
    rewrite Ptrofs.add_assoc. repeat split; reflexivity.
  - match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
Qed.

(** A single status write is the complete reached attack effect.  Its switch
    prefix is read-only; this statement does not require any attack-type value
    or live actor coordinate. *)
Definition ibrc_attack_cases version := match ibrc_attack_switch version with
| Sswitch _ cases => cases | _ => LSnil end.
Lemma ibrc_attack_switch_properties : forall version,
  ibrc_attack_switch version = Sswitch (Etempvar BRC._interaction tint) (ibrc_attack_cases version) /\
  forall selector,
    cce_readonly_keep BRC._o
      (seq_of_labeled_statement (select_switch selector (ibrc_attack_cases version))) = true /\
    iar_normal_or_break
      (seq_of_labeled_statement (select_switch selector (ibrc_attack_cases version))) = true.
Proof.
  intro version; split.
  - destruct version; reflexivity.
  - intro selector; destruct version;
    cbn [ibrc_attack_cases ibrc_attack_switch ibrc_body fn_body ibk_head rank12b_drop_sequences
      us_interaction.f_attack_object jp_interaction.f_attack_object];
    cbv [select_switch select_switch_case select_switch_default seq_of_labeled_statement
      cce_readonly_keep iar_normal_or_break];
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    split; reflexivity.
Qed.
Lemma ibrc_attack_switch_frames_memory_and_actor : forall version ge e le m t le' after out,
  ocn_exec ge e le m (ibrc_attack_switch version) t le' after out ->
  after = m /\ le' ! BRC._o = le ! BRC._o /\ out = Out_normal.
Proof.
  intros version ge e le m t le' after out Hrun.
  destruct (ibrc_attack_switch_properties version) as [Hshape Hcases].
  rewrite Hshape in Hrun.
  pose proof (iar_switch_normal _ _ _ _ _ _ _ _ _ _
    ltac:(intro; exact (proj2 (Hcases _))) Hrun) as Hnormal.
  inversion Hrun; subst.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
    (seq_of_labeled_statement (select_switch ?selector _)) _ _ _ _ |- _ =>
    destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hr (proj1 (Hcases selector)))
      as (_ & Hsame & Ho)
  end. repeat split; assumption || reflexivity.
Qed.

Theorem ibrc_complete_attack_has_only_status_store :
  forall version m ob oo interaction t after result,
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ibrc_body version IBRCattack)) [Vptr ob oo;Vint interaction] t after result ->
  exists written, Mem.store Mint32 m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 308))) written = Some after.
Proof.
  intros version m ob oo interaction t after result Hcall.
  destruct (ibrc_attack_source version) as (Hvars & Hparams & Hbody & HrestShape).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    rewrite Hparams in Hb; cbn in Hb; inversion Hb; subst temps end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rename Hr into HbodyRun end.
  rewrite Hbody in HbodyRun.
  destruct (ibk_split_sequence _ _ _ _
    (Sset BRC._attackType (Econst_int Int.zero tint))
    (Ssequence (ibrc_attack_switch version) (ibrc_attack_rest version))
    _ _ _ _ eq_refl HbodyRun)
    as (switch_le & switch_m & init_t & rest_t & Htrace & Hinit & Hrest).
  clear HbodyRun.
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ BRC._o Hinit eq_refl)
    as (_ & HinitSame & HinitO). subst switch_m.
  clear Hinit.
  assert (switch_le ! BRC._o = Some (Vptr ob oo)) as Hactor.
  { rewrite HinitO. rewrite PTree.gso by discriminate. apply PTree.gss. }
  inversion Hrest; subst; clear Hrest.
  all: repeat match goal with Hsw : ClightBigstep.exec_stmt _ _ _ _ _ (ibrc_attack_switch _) _ _ _ _ |- _ =>
    destruct (ibrc_attack_switch_frames_memory_and_actor _ _ _ _ _ _ _ _ _ Hsw)
      as (Hsame & HoEq & Hnormal); clear Hsw; subst end.
  all: try contradiction.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (ibrc_attack_rest version) _ _ _ _ |- _ =>
      rewrite HrestShape in Hr end.
  cce_unroll_loop_free_exec.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
      inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ ?temps _ (ibrc_status _) _ _ _ |- _ =>
    assert (temps ! BRC._o = Some (Vptr ob oo)) as Ho by congruence;
    destruct (ibrc_status_location _ _ _ _ _ _ _ _ _ Ho Hl) as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  eexists; eassumption.
Qed.

Definition ibrc_attack_call := Scall None
  (Evar BRC._attack_object (Tfunction [tptr (Tstruct BRC._Object noattr);tint] tuint cc_default))
  [Etempvar BRC._o (tptr (Tstruct BRC._Object noattr));Etempvar BRC._interaction tuint].
Definition ibrc_back_call := Scall None
  (Evar BRC._bounce_back_from_attack (Tfunction
    [tptr (Tstruct BRC._MarioState noattr);tuint] tvoid cc_default))
  [Etempvar BRC._m (tptr (Tstruct BRC._MarioState noattr));Etempvar BRC._interaction tuint].
Definition ibrc_prefix := Ssequence ibrc_attack_call ibrc_back_call.
Inductive IBRCHandler := IBRCTop | IBRCBelow.
Definition ibrc_handler_body version kind := match version,kind with
| VersionUS,IBRCTop => us_interaction.f_interact_bounce_top
| VersionJP,IBRCTop => jp_interaction.f_interact_bounce_top
| VersionUS,IBRCBelow => us_interaction.f_interact_hit_from_below
| VersionJP,IBRCBelow => jp_interaction.f_interact_hit_from_below end.
Definition ibrc_handler_taken version kind := match fn_body (ibrc_handler_body version kind) with
| Ssequence _ (Ssequence (Sifthenelse _ attacked _) _) => attacked | _ => Sskip end.
Definition ibrc_handler_after_prefix version kind := match ibrc_handler_taken version kind with
| Ssequence _ (Ssequence _ tail) => tail | _ => Sskip end.
Theorem ibrc_handler_prefix_is_generated : forall version kind,
  ibrc_handler_taken version kind = Ssequence ibrc_attack_call
    (Ssequence ibrc_back_call (ibrc_handler_after_prefix version kind)) /\
  ibk_normal ibrc_prefix = true /\
  cce_keeps_temp BRC._m ibrc_prefix = true /\
  cce_keeps_temp BRC._o ibrc_prefix = true /\
  cce_keeps_temp BRC._interaction ibrc_prefix = true.
Proof. intros [] []; repeat split; reflexivity. Qed.

Lemma ibrc_reached_attack_call_is_status_store :
  forall version e le m ob oo t le' after out,
  e ! BRC._attack_object = None ->
  le ! BRC._o = Some (Vptr ob oo) -> le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ibrc_attack_call t le' after out ->
  exists written, Mem.store Mint32 m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 308))) written = Some after /\ le' = le.
Proof.
  intros version e le m ob oo t le' after out Hlocal Ho Hi Hrun.
  destruct (ibrc_selected_native_resolves version IBRCattack) as (fb & Hsymbol & Hfun).
  unfold ibrc_attack_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._o _) ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._interaction _) ?v |- _ =>
    assert (v = Vint (Int.repr 64)) by (eapply ocn_temp_value; eauto); subst v end.
  repeat match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibrc_complete_attack_has_only_status_store _ _ _ _ _ _ _ _ Hcall)
      as [written Hstore] end.
  exists written. split; [exact Hstore|reflexivity].
Qed.

Lemma ibrc_reached_above_back_call_is_noop :
  forall version e le m mb mo t le' after out,
  e ! BRC._bounce_back_from_attack = None ->
  le ! BRC._m = Some (Vptr mb mo) -> le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ibrc_back_call t le' after out -> t = E0 /\ after = m /\ le' = le.
Proof.
  intros version e le m mb mo t le' after out Hlocal Hm Hi Hrun.
  destruct (ibrc_selected_native_resolves version IBRCback) as (fb & Hsymbol & Hfun).
  unfold ibrc_back_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._m _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._interaction _) ?v |- _ =>
    assert (v = Vint (Int.repr 64)) by (eapply ocn_temp_value; eauto); subst v end.
  repeat match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibrc_above_bounce_back_has_no_effect _ _ _ _ _ _ _ _ Hcall) as [Ht Hsame] end.
  repeat split; assumption || reflexivity.
Qed.

Lemma ibrc_slot_address : forall slot delta,
  (slot < object_pool_capacity)%nat -> 0 <= delta <= 512 ->
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr delta)) =
    object_slot_offset slot + delta.
Proof.
  intros slot delta Hslot Hdelta.
  pose proof (rank15_pool_slot_offset_in_pointer_range _ Hslot) as Hrange.
  unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (object_slot_offset slot)) by (unfold object_size in Hrange; lia).
  rewrite (Ptrofs.unsigned_repr delta) by (change (0 <= delta <= 4294967295); lia).
  apply Ptrofs.unsigned_repr. unfold object_size in Hrange. lia.
Qed.
Definition ibrc_outside_status (ob : block) slot chunk (b : block) offset :=
  b <> ob \/ offset + size_chunk chunk <= object_slot_offset slot + 308 \/
    object_slot_offset slot + 312 <= offset.
Definition InkBounceLocalReadContinuity : Prop :=
  forall version e le before mb mo ob slot t le' after out,
  (slot < object_pool_capacity)%nat ->
  e ! BRC._attack_object = None -> e ! BRC._bounce_back_from_attack = None ->
  le ! BRC._m = Some (Vptr mb mo) ->
  le ! BRC._o = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    ibrc_prefix t le' after out ->
  le' = le /\
  (forall chunk b offset, ibrc_outside_status ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk before b offset).

Theorem ibrc_real_above_handler_prefix_preserves_read_cells : InkBounceLocalReadContinuity.
Proof.
  intros version e le before mb mo ob slot t le' after out Hslot HattackName HbackName Hm Ho Hi Hrun.
  unfold ibrc_prefix in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ibrc_attack_call _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suffix & Htrace & Hattack & Hback).
  destruct (ibrc_reached_attack_call_is_status_store _ _ _ _ _ _ _ _ _ _
    HattackName Ho Hi Hattack) as (written & Hstore & ->).
  destruct (ibrc_reached_above_back_call_is_noop _ _ _ _ _ _ _ _ _ _
    HbackName Hm Hi Hback) as (_ & -> & ->).
  split; [reflexivity|].
  rewrite ibrc_slot_address in Hstore by (auto; lia).
  intros chunk b offset Houtside. eapply Mem.load_store_other; [exact Hstore|].
  unfold ibrc_outside_status in Houtside. cbn [size_chunk]. lia.
Qed.

(** This is the missing local read connection: no equal-read premises are
    used for the two intervening real calls.  Raw/display positions may
    already disagree with movement; the theorem leaves that inherited gap
    intact and does not turn the 251 rise bound into its global bound. *)
Theorem ibrc_handler_prefix_keeps_actual_bounce_inputs :
  forall version e le before mb ob slot movement_y actor_y hitbox_h t le' after out,
  (slot < object_pool_capacity)%nat -> mb <> ob ->
  e ! BRC._attack_object = None -> e ! BRC._bounce_back_from_attack = None ->
  le ! BRC._m = Some (Vptr mb Ptrofs.zero) ->
  le ! BRC._o = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  Mem.load Mfloat32 before mb 64 = Some (Vsingle movement_y) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 164) = Some (Vsingle actor_y) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 508) = Some (Vsingle hitbox_h) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    ibrc_prefix t le' after out ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle movement_y) /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 164) = Some (Vsingle actor_y) /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 508) = Some (Vsingle hitbox_h).
Proof.
  intros version e le before mb ob slot movement_y actor_y hitbox_h t le' after out
    Hslot Hsep Hattack Hback Hm Ho Hi Hmovement Hactor Hheight Hrun.
  destruct (ibrc_real_above_handler_prefix_preserves_read_cells version e le before mb
    Ptrofs.zero ob slot t le' after out Hslot Hattack Hback Hm Ho Hi Hrun) as [_ Hframe].
  repeat split.
  - rewrite Hframe; [exact Hmovement|unfold ibrc_outside_status; left; exact Hsep].
  - rewrite Hframe; [exact Hactor|unfold ibrc_outside_status; right; left; cbn; lia].
  - rewrite Hframe; [exact Hheight|unfold ibrc_outside_status; right; right; lia].
Qed.

Theorem ibrc_bounce_read_continuity_checked : InkBounceLocalReadContinuity.
Proof. exact ibrc_real_above_handler_prefix_preserves_read_cells. Qed.

Definition ibrc_above_guard version := match ibrc_handler_after_prefix version IBRCTop with
| Sifthenelse guard _ _ => guard | _ => Econst_int Int.zero tint end.
Definition ibrc_choice version := match ibrc_handler_after_prefix version IBRCTop with
| Sifthenelse _ choice _ => choice | _ => Sskip end.
Definition ibrc_below_check version := ibk_head (ibrc_handler_after_prefix version IBRCBelow).
Definition ibrc_below_guard version := match ibrc_below_check version with
| Sifthenelse guard _ _ => guard | _ => Econst_int Int.zero tint end.
Definition ibrc_below_effect version := match ibrc_below_check version with
| Sifthenelse _ effect _ => effect | _ => Sskip end.
Definition ibrc_subtype_read version := ibk_head (ibrc_choice version).
Definition ibrc_subtype_guard version := match ibrc_choice version with
| Ssequence _ (Sifthenelse guard _ _) => guard | _ => Econst_int Int.zero tint end.
Definition ibrc_twirl_tail version := match ibrc_choice version with
| Ssequence _ (Sifthenelse _ (Ssequence _ tail) _) => tail | _ => Sskip end.
Definition ibrc_bounce_call bits := Scall None
  (Evar BRC._bounce_off_object (Tfunction
    [tptr (Tstruct BRC._MarioState noattr);tptr (Tstruct BRC._Object noattr);tfloat]
    tvoid cc_default))
  [Etempvar BRC._m (tptr (Tstruct BRC._MarioState noattr));
   Etempvar BRC._o (tptr (Tstruct BRC._Object noattr));
   Econst_single (Float32.of_bits (Int.repr bits)) tfloat].

Lemma ibrc_choice_cuts_are_generated : forall version,
  ibrc_handler_after_prefix version IBRCTop =
    Sifthenelse (ibrc_above_guard version) (ibrc_choice version) Sskip /\
  ibrc_handler_after_prefix version IBRCBelow = Ssequence (ibrc_below_check version)
    (Sifthenelse (ibrc_above_guard version) (ibrc_choice version) Sskip) /\
  ibrc_below_check version = Sifthenelse (ibrc_below_guard version)
    (ibrc_below_effect version) Sskip /\
  ibk_normal (ibrc_below_check version) = true /\
  ibrc_choice version = Ssequence (ibrc_subtype_read version)
    (Sifthenelse (ibrc_subtype_guard version)
      (Ssequence (ibrc_bounce_call 1117782016) (ibrc_twirl_tail version))
      (ibrc_bounce_call 1106247680)) /\
  cce_readonly_keep BRC._m (ibrc_subtype_read version) = true /\
  cce_readonly_keep BRC._o (ibrc_subtype_read version) = true /\
  ibk_normal (ibrc_subtype_read version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ibrc_above_guard_value : forall version ge e le m,
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  eval_expr ge e le m (ibrc_above_guard version) (Vint (Int.repr 64)).
Proof.
  intros [] ge e le m Hi;
    cbn [ibrc_above_guard ibrc_handler_after_prefix ibrc_handler_taken ibrc_handler_body fn_body
      us_interaction.f_interact_bounce_top jp_interaction.f_interact_bounce_top];
    ibrc_build_mask_read.
Qed.
Lemma ibrc_below_guard_value : forall version ge e le m,
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  eval_expr ge e le m (ibrc_below_guard version) (Vint Int.zero).
Proof.
  intros [] ge e le m Hi;
    cbn [ibrc_below_guard ibrc_below_check ibrc_handler_after_prefix ibrc_handler_taken
      ibrc_handler_body fn_body ibk_head
      us_interaction.f_interact_hit_from_below jp_interaction.f_interact_hit_from_below];
    ibrc_build_mask_read.
Qed.
Lemma ibrc_above_guard_type : forall version, typeof (ibrc_above_guard version) = tuint.
Proof. intros []; reflexivity. Qed.
Lemma ibrc_below_guard_type : forall version, typeof (ibrc_below_guard version) = tuint.
Proof. intros []; reflexivity. Qed.

Lemma ibrc_below_check_is_skipped : forall version ge e le m t le' after out,
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  ocn_exec ge e le m (ibrc_below_check version) t le' after out ->
  t = E0 /\ le' = le /\ after = m.
Proof.
  intros version ge e le m t le' after out Hi Hr.
  destruct (ibrc_choice_cuts_are_generated version) as (_ & _ & Hshape & _).
  rewrite Hshape in Hr. inversion Hr; subst; clear Hr.
  match goal with He : eval_expr _ _ _ _ (ibrc_below_guard _) ?value |- _ =>
    assert (value = Vint Int.zero) by
      (eapply ocr_expr_unique; [exact He|apply ibrc_below_guard_value; exact Hi]); subst value end.
  match goal with Hb : bool_val (Vint Int.zero) _ _ = Some ?take |- _ =>
    rewrite ibrc_below_guard_type in Hb;
    change (Some false = Some take) in Hb; inversion Hb; subst take end.
  match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
    inversion Hskip; subst end. repeat split; reflexivity.
Qed.
Lemma ibrc_after_prefix_reaches_choice : forall version kind ge e le m t le' after out,
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  ocn_exec ge e le m (ibrc_handler_after_prefix version kind) t le' after out ->
  ocn_exec ge e le m (ibrc_choice version) t le' after out.
Proof.
  intros version kind ge e le m t le' after out Hi Hr.
  destruct (ibrc_choice_cuts_are_generated version) as (Htop & Hbelow & _ & Hnormal & _).
  destruct kind; [rewrite Htop in Hr|
    rewrite Hbelow in Hr;
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (middle & memory & pre & suffix & Htrace & Hcheck & Hnext);
    clear Hr; rename Hnext into Hr;
    destruct (ibrc_below_check_is_skipped _ _ _ _ _ _ _ _ _ Hi Hcheck) as (-> & -> & ->);
    cbn in Htrace; subst t].
  all: inversion Hr; subst; clear Hr.
  all: match goal with He : eval_expr _ _ _ _ (ibrc_above_guard _) ?value |- _ =>
    assert (value = Vint (Int.repr 64)) by
      (eapply ocr_expr_unique; [exact He|apply ibrc_above_guard_value; exact Hi]); subst value end.
  all: match goal with Hb : bool_val (Vint (Int.repr 64)) _ _ = Some ?take |- _ =>
    rewrite ibrc_above_guard_type in Hb;
    change (Some true = Some take) in Hb; inversion Hb; subst take end.
  all: assumption.
Qed.

Lemma ibrc_actual_bounce_call : forall version bits e le m mb mo ob oo t le' after out,
  e ! BRC._bounce_off_object = None ->
  le ! BRC._m = Some (Vptr mb mo) -> le ! BRC._o = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibrc_bounce_call bits) t le' after out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m (Internal (ibp_body version))
    [Vptr mb mo;Vptr ob oo;Vsingle (Float32.of_bits (Int.repr bits))] t after result.
Proof.
  intros version bits e le m mb mo ob oo t le' after out Hlocal Hm Ho Hrun.
  destruct (ibrc_selected_native_resolves version IBRCbounce) as (fb & Hsymbol & Hfun).
  unfold ibrc_bounce_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._m _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._o _) ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ =>
    inversion Hr; subst; clear Hr end.
  all: try solve [match goal with Hl : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion Hl end].
  repeat match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  assert (ibrc_body version IBRCbounce = ibp_body version) as Hbody by (destruct version; reflexivity).
  rewrite Hbody in *. eexists; eassumption.
Qed.

Theorem ibrc_after_prefix_reaches_real_bounce_without_another_write :
  forall version kind e le m mb mo ob oo t le' after out,
  e ! BRC._bounce_off_object = None ->
  le ! BRC._m = Some (Vptr mb mo) -> le ! BRC._o = Some (Vptr ob oo) ->
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibrc_handler_after_prefix version kind) t le' after out ->
  exists bits bounce_t bounced result,
    In bits [1117782016;1106247680] /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m (Internal (ibp_body version))
      [Vptr mb mo;Vptr ob oo;Vsingle (Float32.of_bits (Int.repr bits))] bounce_t bounced result.
Proof.
  intros version kind e le m mb mo ob oo t le' after out Hname Hm Ho Hi Hrun.
  pose proof (ibrc_after_prefix_reaches_choice _ _ _ _ _ _ _ _ _ _ Hi Hrun) as Hchoice.
  destruct (ibrc_choice_cuts_are_generated version) as (_ & _ & _ & _ & Hshape & HreadM & HreadO & Hnormal).
  rewrite Hshape in Hchoice.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hchoice)
    as (middle & memory & pre & suffix & Htrace & Hread & Hoptions).
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hread HreadM) as (_ & -> & HkeepM).
  pose proof (proj2 (proj2 (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hread HreadO))) as HkeepO.
  assert (middle ! BRC._m = Some (Vptr mb mo)) as HnextM by congruence.
  assert (middle ! BRC._o = Some (Vptr ob oo)) as HnextO by congruence.
  inversion Hoptions; subst; clear Hoptions. destruct b; cbn beta iota in *.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
      destruct (ibk_split_sequence _ _ _ _ (ibrc_bounce_call 1117782016) _ _ _ _ _ eq_refl Hr)
        as (last & bounced & bounce_t & tail_t & Ht & Hbounce & Htail) end.
    destruct (ibrc_actual_bounce_call version 1117782016 e middle m mb mo ob oo
      bounce_t last bounced Out_normal Hname HnextM HnextO Hbounce) as [result Hcall].
    exists 1117782016,bounce_t,bounced,result. split; [left; reflexivity|exact Hcall].
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (ibrc_bounce_call _) ?bt _ ?bm ?bo |- _ =>
      destruct (ibrc_actual_bounce_call version 1106247680 e middle m mb mo ob oo
        bt _ bm bo Hname HnextM HnextO Hr) as [result Hcall];
      exists 1106247680,bt,bm,result end.
    split; [right; left; reflexivity|exact Hcall].
Qed.

(** At the actual taken handler cut, no matching-read premises are needed
    for attack_object, bounce_back_from_attack or the subtype choice.  The
    passed falling comparison and live numeric bounds are still explicit:
    connecting the earlier contact/dispatch phase is a different boundary. *)
Definition InkBounceReachedHandlerRiseCheckpoint : Prop :=
  forall version kind e le before mb ob slot movement_y actor_y hitbox_h
    t le' after out,
  (slot < object_pool_capacity)%nat -> mb <> ob ->
  e ! BRC._attack_object = None -> e ! BRC._bounce_back_from_attack = None ->
  e ! BRC._bounce_off_object = None ->
  le ! BRC._m = Some (Vptr mb Ptrofs.zero) ->
  le ! BRC._o = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  Mem.load Mfloat32 before mb 64 = Some (Vsingle movement_y) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 164) = Some (Vsingle actor_y) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 508) = Some (Vsingle hitbox_h) ->
  Float32.cmp Cgt movement_y actor_y = true ->
  rank9cf_finite movement_y -> rank9cf_finite actor_y -> rank9cf_finite hitbox_h ->
  (-32768 <= rank9cf_real movement_y <= 32768)%R ->
  (-32768 <= rank9cf_real actor_y)%R -> (-32768 <= rank9cf_real hitbox_h <= 250)%R ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    (ibrc_handler_taken version kind) t le' after out ->
  exists bounce_m bits bounce_t bounced result start_le snap_le snap_m final_le tail_out,
    In bits [1117782016;1106247680] /\
    Mem.load Mfloat32 bounce_m mb 64 = Some (Vsingle movement_y) /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) bounce_m (Internal (ibp_body version))
      [Vptr mb Ptrofs.zero;Vptr ob (Ptrofs.repr (object_slot_offset slot));
        Vsingle (Float32.of_bits (Int.repr bits))] bounce_t bounced result /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env start_le bounce_m
      (ibp_height_stage version) E0 snap_le snap_m Out_normal /\
    Mem.store Mfloat32 bounce_m mb 64 (Vsingle (Float32.add actor_y hitbox_h)) = Some snap_m /\
    Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle (Float32.add actor_y hitbox_h)) /\
    (rank9cf_real (Float32.add actor_y hitbox_h) - rank9cf_real movement_y <= 251)%R /\
    (forall chunk b offset, b <> mb -> ibrc_outside_status ob slot chunk b offset ->
      Mem.load chunk snap_m b offset = Mem.load chunk before b offset) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env snap_le snap_m
      (ibp_tail version) bounce_t final_le bounced tail_out.

Theorem ibrc_actual_above_handler_has_at_most_251_new_rise :
  InkBounceReachedHandlerRiseCheckpoint.
Proof.
  intros version kind e le before mb ob slot movement_y actor_y hitbox_h t le' after out
    Hslot Hsep HattackName HbackName HbounceName Hm Ho Hi Hmovement Hactor Hheight
    Hcmp Fmovement Factor Fheight Bmovement Bactor Bheight Hrun.
  destruct (ibrc_handler_prefix_is_generated version kind) as (Hshape & _).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ibrc_attack_call _ _ _ _ _ eq_refl Hrun)
    as (attack_le & attack_m & attack_t & rest_t & Htrace & Hattack & Hrest).
  destruct (ibk_split_sequence _ _ _ _ ibrc_back_call _ _ _ _ _ eq_refl Hrest)
    as (prefix_le & bounce_m & back_t & following_t & HrestTrace & Hback & Hfollowing).
  assert (ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    ibrc_prefix (attack_t ++ back_t) prefix_le bounce_m Out_normal) as Hprefix.
  { unfold ibrc_prefix. eapply exec_Sseq_1; eauto. }
  destruct (ibrc_real_above_handler_prefix_preserves_read_cells version e le before mb
    Ptrofs.zero ob slot (attack_t ++ back_t) prefix_le bounce_m Out_normal
    Hslot HattackName HbackName Hm Ho Hi Hprefix) as [HsameTemps Hframe].
  subst prefix_le.
  destruct (ibrc_handler_prefix_keeps_actual_bounce_inputs version e le before mb ob slot
    movement_y actor_y hitbox_h (attack_t ++ back_t) le bounce_m Out_normal
    Hslot Hsep HattackName HbackName Hm Ho Hi Hmovement Hactor Hheight Hprefix)
    as (HactualMovement & HactualActor & HactualHeight).
  destruct (ibrc_after_prefix_reaches_real_bounce_without_another_write version kind e le
    bounce_m mb Ptrofs.zero ob (Ptrofs.repr (object_slot_offset slot)) following_t le' after out
    HbounceName Hm Ho Hi Hfollowing) as (bits & bounce_t & bounced & result & Hbits & Hcall).
  assert (Mem.load Mfloat32 bounce_m ob
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 164))) =
    Some (Vsingle actor_y)) as Hy by (rewrite ibrc_slot_address by (auto; lia); exact HactualActor).
  assert (Mem.load Mfloat32 bounce_m ob
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h)) as Hh by (rewrite ibrc_slot_address by (auto; lia); exact HactualHeight).
  destruct (ibp_completed_bounce_reaches_height_checkpoint version bounce_m mb Ptrofs.zero ob
    (Ptrofs.repr (object_slot_offset slot)) actor_y hitbox_h
    (Float32.of_bits (Int.repr bits)) bounce_t bounced result Hy Hh Hcall)
    as (start_le & snap_le & snap_m & final_le & suffix & tail_out &
      Hsuffix & Hstage & Hstore & HsnapFrame & Htail).
  subst suffix.
  change (Mem.store Mfloat32 bounce_m mb 64 (Vsingle (Float32.add actor_y hitbox_h)) = Some snap_m)
    in Hstore.
  destruct (ibag_live_snap_rise_is_at_most_251 movement_y actor_y hitbox_h Fmovement Factor
    Fheight Bmovement Bactor Bheight Hcmp) as [_ Hbound].
  exists bounce_m,bits,bounce_t,bounced,result,start_le,snap_le,snap_m,final_le,tail_out.
  repeat apply conj; try assumption.
  - exact (Mem.load_store_same _ _ _ _ _ _ Hstore).
  - intros chunk b offset HnotState Houtside.
    rewrite HsnapFrame, Hframe; [reflexivity|exact Houtside|exact HnotState].
Qed.

(** No lower height bound or falling comparison is needed to identify the
    actual first snap.  In particular, a later signed-height analysis may
    use this hook with a large negative live hitbox height. *)
Theorem ibrc_real_handler_reaches_exact_first_snap :
  forall version kind e le before mb ob slot movement_y actor_y hitbox_h
    t le' after out,
  (slot < object_pool_capacity)%nat -> mb <> ob ->
  e ! BRC._attack_object = None -> e ! BRC._bounce_back_from_attack = None ->
  e ! BRC._bounce_off_object = None ->
  le ! BRC._m = Some (Vptr mb Ptrofs.zero) ->
  le ! BRC._o = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  Mem.load Mfloat32 before mb 64 = Some (Vsingle movement_y) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 164) = Some (Vsingle actor_y) ->
  Mem.load Mfloat32 before ob (object_slot_offset slot + 508) = Some (Vsingle hitbox_h) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    (ibrc_handler_taken version kind) t le' after out ->
  exists bounce_m bits bounce_t bounced result start_le snap_le snap_m final_le tail_out,
    In bits [1117782016;1106247680] /\
    Mem.load Mfloat32 bounce_m mb 64 = Some (Vsingle movement_y) /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) bounce_m (Internal (ibp_body version))
      [Vptr mb Ptrofs.zero;Vptr ob (Ptrofs.repr (object_slot_offset slot));
        Vsingle (Float32.of_bits (Int.repr bits))] bounce_t bounced result /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env start_le bounce_m
      (ibp_height_stage version) E0 snap_le snap_m Out_normal /\
    Mem.store Mfloat32 bounce_m mb 64 (Vsingle (Float32.add actor_y hitbox_h)) = Some snap_m /\
    Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle (Float32.add actor_y hitbox_h)) /\
    (forall chunk b offset, b <> mb -> ibrc_outside_status ob slot chunk b offset ->
      Mem.load chunk snap_m b offset = Mem.load chunk before b offset) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env snap_le snap_m
      (ibp_tail version) bounce_t final_le bounced tail_out.
Proof.
  intros version kind e le before mb ob slot movement_y actor_y hitbox_h t le' after out
    Hslot Hsep HattackName HbackName HbounceName Hm Ho Hi Hmovement Hactor Hheight Hrun.
  destruct (ibrc_handler_prefix_is_generated version kind) as (Hshape & _).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ibrc_attack_call _ _ _ _ _ eq_refl Hrun)
    as (attack_le & attack_m & attack_t & rest_t & Htrace & Hattack & Hrest).
  destruct (ibk_split_sequence _ _ _ _ ibrc_back_call _ _ _ _ _ eq_refl Hrest)
    as (prefix_le & bounce_m & back_t & following_t & HrestTrace & Hback & Hfollowing).
  assert (ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    ibrc_prefix (attack_t ++ back_t) prefix_le bounce_m Out_normal) as Hprefix.
  { unfold ibrc_prefix. eapply exec_Sseq_1; eauto. }
  destruct (ibrc_real_above_handler_prefix_preserves_read_cells version e le before mb
    Ptrofs.zero ob slot (attack_t ++ back_t) prefix_le bounce_m Out_normal
    Hslot HattackName HbackName Hm Ho Hi Hprefix) as [HsameTemps Hframe].
  subst prefix_le.
  destruct (ibrc_handler_prefix_keeps_actual_bounce_inputs version e le before mb ob slot
    movement_y actor_y hitbox_h (attack_t ++ back_t) le bounce_m Out_normal
    Hslot Hsep HattackName HbackName Hm Ho Hi Hmovement Hactor Hheight Hprefix)
    as (HactualMovement & HactualActor & HactualHeight).
  destruct (ibrc_after_prefix_reaches_real_bounce_without_another_write version kind e le
    bounce_m mb Ptrofs.zero ob (Ptrofs.repr (object_slot_offset slot)) following_t le' after out
    HbounceName Hm Ho Hi Hfollowing) as (bits & bounce_t & bounced & result & Hbits & Hcall).
  assert (Mem.load Mfloat32 bounce_m ob
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 164))) =
    Some (Vsingle actor_y)) as Hy by (rewrite ibrc_slot_address by (auto; lia); exact HactualActor).
  assert (Mem.load Mfloat32 bounce_m ob
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h)) as Hh by (rewrite ibrc_slot_address by (auto; lia); exact HactualHeight).
  destruct (ibp_completed_bounce_reaches_height_checkpoint version bounce_m mb Ptrofs.zero ob
    (Ptrofs.repr (object_slot_offset slot)) actor_y hitbox_h
    (Float32.of_bits (Int.repr bits)) bounce_t bounced result Hy Hh Hcall)
    as (start_le & snap_le & snap_m & final_le & suffix & tail_out &
      Hsuffix & Hstage & Hstore & HsnapFrame & Htail).
  subst suffix.
  change (Mem.store Mfloat32 bounce_m mb 64 (Vsingle (Float32.add actor_y hitbox_h)) = Some snap_m)
    in Hstore.
  exists bounce_m,bits,bounce_t,bounced,result,start_le,snap_le,snap_m,final_le,tail_out.
  repeat apply conj; try assumption.
  - exact (Mem.load_store_same _ _ _ _ _ _ Hstore).
  - intros chunk b offset HnotState Houtside.
    rewrite HsnapFrame, Hframe; [reflexivity|exact Houtside|exact HnotState].
Qed.

Definition InkBounceReadContinuityBoundary : Prop :=
  InkBounceLocalReadContinuity /\ InkBounceReachedHandlerRiseCheckpoint.
Theorem ibrc_bounce_read_continuity_boundary_checked : InkBounceReadContinuityBoundary.
Proof.
  split; [exact ibrc_real_above_handler_prefix_preserves_read_cells|
    exact ibrc_actual_above_handler_has_at_most_251_new_rise].
Qed.

(** The classifier's returned value crosses only a temporary copy and a
    constant mask before the attacked prefix.  This is an actual caller cut,
    not an assumption that a separately supplied guard memory matches. *)
Definition ibrc_classifier_call := Scall (Some BRC._t'1)
  (Evar BRC._determine_interaction (Tfunction
    [tptr (Tstruct BRC._MarioState noattr);tptr (Tstruct BRC._Object noattr)]
    tuint cc_default))
  [Etempvar BRC._m (tptr (Tstruct BRC._MarioState noattr));
   Etempvar BRC._o (tptr (Tstruct BRC._Object noattr))].
Definition ibrc_classifier_readback := Sset BRC._interaction (Etempvar BRC._t'1 tuint).
Definition ibrc_classifier_branch version kind := match fn_body (ibrc_handler_body version kind) with
| Ssequence (Ssequence _ (Sifthenelse _ _ branch)) _ => branch | _ => Sskip end.
Definition ibrc_handler_after_init version kind := match fn_body (ibrc_handler_body version kind) with
| Ssequence _ tail => tail | _ => Sskip end.
Definition ibrc_attack_guard version kind := match ibrc_handler_after_init version kind with
| Ssequence (Sifthenelse guard _ _) _ => guard | _ => Econst_int Int.zero tint end.
Definition ibrc_nonattack version kind := match ibrc_handler_after_init version kind with
| Ssequence (Sifthenelse _ _ fallback) _ => fallback | _ => Sskip end.
Definition ibrc_handler_final version kind := match ibrc_handler_after_init version kind with
| Ssequence _ final => final | _ => Sskip end.
Definition ibrc_return_to_attack version kind :=
  Ssequence ibrc_classifier_readback (ibrc_handler_after_init version kind).

Lemma ibrc_classifier_caller_cuts_are_generated : forall version kind,
  ibrc_classifier_branch version kind = Ssequence ibrc_classifier_call ibrc_classifier_readback /\
  ibrc_handler_after_init version kind = Ssequence
    (Sifthenelse (ibrc_attack_guard version kind) (ibrc_handler_taken version kind)
      (ibrc_nonattack version kind)) (ibrc_handler_final version kind) /\
  ibk_normal ibrc_classifier_readback = true /\
  cce_readonly_keep BRC._m ibrc_classifier_readback = true /\
  cce_readonly_keep BRC._o ibrc_classifier_readback = true.
Proof. intros [] []; repeat split; reflexivity. Qed.

Lemma ibrc_above_attack_mask_value : forall version kind ge e le m,
  le ! BRC._interaction = Some (Vint (Int.repr 64)) ->
  eval_expr ge e le m (ibrc_attack_guard version kind) (Vint (Int.repr 64)).
Proof.
  intros [] [] ge e le m Hi;
    cbn [ibrc_attack_guard ibrc_handler_after_init ibrc_handler_body fn_body
      us_interaction.f_interact_bounce_top jp_interaction.f_interact_bounce_top
      us_interaction.f_interact_hit_from_below jp_interaction.f_interact_hit_from_below];
    ibrc_build_mask_read.
Qed.
Lemma ibrc_above_attack_mask_type : forall version kind,
  typeof (ibrc_attack_guard version kind) = tuint.
Proof. intros [] []; reflexivity. Qed.

Theorem ibrc_actual_classifier_return_reaches_attacked_cut :
  forall version kind ge e le returned t le' after out,
  le ! BRC._t'1 = Some (Vint (Int.repr 64)) ->
  ocn_exec ge e le returned (ibrc_return_to_attack version kind) t le' after out ->
  exists branch_t branch_le branch_m branch_out,
    ocn_exec ge e (PTree.set BRC._interaction (Vint (Int.repr 64)) le) returned
      (ibrc_handler_taken version kind) branch_t branch_le branch_m branch_out.
Proof.
  intros version kind ge e le returned t le' after out Hvalue Hrun.
  unfold ibrc_return_to_attack in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ibrc_classifier_readback _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suffix & Htrace & Hread & Hrest).
  unfold ibrc_classifier_readback in Hread. inversion Hread; subst; clear Hread.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._t'1 _) ?v |- _ =>
    assert (v = Vint (Int.repr 64)) by (eapply ocn_temp_value; eauto); subst v end.
  destruct (ibrc_classifier_caller_cuts_are_generated version kind) as (_ & Hshape & _).
  rewrite Hshape in Hrest. inversion Hrest; subst; clear Hrest.
  all: match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
    (Sifthenelse (ibrc_attack_guard _ _) _ _) _ _ _ _ |- _ =>
      inversion Hr; subst; clear Hr end.
  all: match goal with Hr : eval_expr _ _ _ _ (ibrc_attack_guard _ _) ?v |- _ =>
    assert (v = Vint (Int.repr 64)) by
      (eapply ocr_expr_unique; [exact Hr|apply ibrc_above_attack_mask_value; apply PTree.gss]);
    subst v end.
  all: match goal with Hb : bool_val (Vint (Int.repr 64)) _ _ = Some ?take |- _ =>
    rewrite ibrc_above_attack_mask_type in Hb;
    change (Some true = Some take) in Hb; inversion Hb; subst take end.
  all: do 4 eexists; eassumption.
Qed.

Lemma ibrc_us_determine_source :
  nth_error us_interaction.global_definitions
    (ueqr_definition_index BRC._determine_interaction us_interaction.global_definitions) =
  Some (BRC._determine_interaction,Gfun (Internal (ibag_determine_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma ibrc_us_determine_member :
  In (BRC._determine_interaction,Gfun (Internal (ibag_determine_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 10 us_units).
  - exact (us_nlist_at_nIn _ 10 us_units).
  - eapply nth_error_In. exact ibrc_us_determine_source.
Qed.
Lemma ibrc_us_determine_selection :
  us_normalized_global_definition_map ! BRC._determine_interaction =
    Some (Gfun (Internal (ibag_determine_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact (unit_global_definitions us_units)
    us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact ibrc_us_determine_member.
Qed.
Lemma ibrc_us_determine_selected :
  In (BRC._determine_interaction,Gfun (Internal (ibag_determine_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition.
    assert (us_selected_definition_needs_viewport_repair
      (BRC._determine_interaction,Gfun (Internal (ibag_determine_body VersionUS))) = false)
      as Hplain by (vm_compute; reflexivity). rewrite Hplain. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact ibrc_us_determine_selection.
Qed.
Lemma ibrc_jp_determine_source :
  (prog_defmap (nlist_at 10 jp_cleaned_units)) ! BRC._determine_interaction =
    Some (Gfun (Internal (ibag_determine_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem ibrc_selected_classifier_resolves : forall version, exists fb,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) BRC._determine_interaction = Some fb /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb =
    Some (Internal (ibag_determine_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ibrc_us_determine_selected.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 10 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 10 jp_cleaned_units).
    + exact ibrc_jp_determine_source.
Qed.

(** This decoder retains the classifier's actual memory effects.  Its returned
    memory is precisely the memory used by the no-write continuation above. *)
Theorem ibrc_actual_classifier_call_has_real_return_memory :
  forall version e le m mb mo ob oo t le' returned out,
  e ! BRC._determine_interaction = None ->
  le ! BRC._m = Some (Vptr mb mo) -> le ! BRC._o = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ibrc_classifier_call t le' returned out ->
  exists result,
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ibag_determine_body version)) [Vptr mb mo;Vptr ob oo] t returned result /\
    le' = PTree.set BRC._t'1 result le.
Proof.
  intros version e le m mb mo ob oo t le' returned out Hname Hm Ho Hrun.
  destruct (ibrc_selected_classifier_resolves version) as (fb & Hsymbol & Hfun).
  unfold ibrc_classifier_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._m _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BRC._o _) ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply ocn_temp_value; eauto); subst v end.
  repeat match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  eexists. split; [eassumption|reflexivity].
Qed.

Theorem ibrc_real_classifier_return64_connects_to_attacked_cut :
  forall version kind e le before mb mo ob oo t call_le returned out ct final_le after final_out,
  e ! BRC._determine_interaction = None ->
  le ! BRC._m = Some (Vptr mb mo) -> le ! BRC._o = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    ibrc_classifier_call t call_le returned out ->
  call_le ! BRC._t'1 = Some (Vint (Int.repr 64)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e call_le returned
    (ibrc_return_to_attack version kind) ct final_le after final_out ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) before
    (Internal (ibag_determine_body version)) [Vptr mb mo;Vptr ob oo]
    t returned (Vint (Int.repr 64)) /\
  exists branch_t branch_le branch_m branch_out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set BRC._interaction (Vint (Int.repr 64)) call_le) returned
      (ibrc_handler_taken version kind) branch_t branch_le branch_m branch_out.
Proof.
  intros version kind e le before mb mo ob oo t call_le returned out ct final_le after final_out
    Hname Hm Ho Hcall H64 Hcontinuation.
  destruct (ibrc_actual_classifier_call_has_real_return_memory _ _ _ _ _ _ _ _ _ _ _ _
    Hname Hm Ho Hcall) as (result & Hreal & Htemps).
  assert (result = Vint (Int.repr 64)) as Hresult.
  { rewrite Htemps, PTree.gss in H64. inversion H64; reflexivity. }
  subst result. split; [exact Hreal|].
  eapply ibrc_actual_classifier_return_reaches_attacked_cut; eauto.
Qed.
