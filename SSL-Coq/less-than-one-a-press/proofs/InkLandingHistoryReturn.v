(** The real duration-rejection callee returns one.  Its possibly extensive
    memory effects are not replaced with a frame hypothesis. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_mario jp_mario.
From LessThanOneAPress.Proofs Require Import GameTypes InkLandingHistorySource
  InkMovingBackwardSource InkBackwardSource InkBackwardExecution InkGroundCallBackward
  InkFloorResetExecution ObjectContactNecessity ContactConsumerExecution
  SecretContactExecution Area2Rank12BContact UpperElevatorQueryResolution
  ContactConsumerSource CleanedClightPrograms ClightLinkExecution
  GlobalInterfaceStructural JPSourceSymbolTransport JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SelectedClightTarget
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ilh_set_action_body version := match version with
| VersionUS => us_mario.f_set_mario_action
| VersionJP => jp_mario.f_set_mario_action end.

Lemma ilh_set_us_source :
  nth_error IBM.global_definitions
    (ueqr_definition_index IBM._set_mario_action IBM.global_definitions) =
  Some (IBM._set_mario_action, Gfun (Internal (ilh_set_action_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma ilh_set_us_member :
  In (IBM._set_mario_action, Gfun (Internal (ilh_set_action_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 1 us_units).
  - exact (us_nlist_at_nIn _ 1 us_units).
  - eapply nth_error_In. exact ilh_set_us_source.
Qed.
Lemma ilh_set_us_selection :
  us_normalized_global_definition_map ! IBM._set_mario_action =
    Some (Gfun (Internal (ilh_set_action_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact ilh_set_us_member.
Qed.
Lemma ilh_set_us_no_repair :
  us_selected_definition_needs_viewport_repair
    (IBM._set_mario_action, Gfun (Internal (ilh_set_action_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Lemma ilh_set_us_selected_member :
  In (IBM._set_mario_action, Gfun (Internal (ilh_set_action_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ilh_set_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact ilh_set_us_selection.
Qed.
Lemma ilh_set_jp_source :
  (prog_defmap (nlist_at 1 jp_cleaned_units)) ! IBM._set_mario_action =
    Some (Gfun (Internal (ilh_set_action_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem ilh_selected_set_action_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._set_mario_action = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ilh_set_action_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ilh_set_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 1 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 1 jp_cleaned_units).
    + exact ilh_set_jp_source.
Qed.

(** This class constrains enclosing-function return values only, never the
    effects of a call or store.  The sole checked body below is set_mario_action. *)
Inductive ilh_returns_one : statement -> Prop :=
| ilh_one_nonreturn : forall s, igb_no_return s = true -> ilh_returns_one s
| ilh_one_return : ilh_returns_one (Sreturn (Some (Econst_int Int.one tint)))
| ilh_one_sequence : forall first rest,
    ilh_returns_one first -> ilh_returns_one rest -> ilh_returns_one (Ssequence first rest)
| ilh_one_switch : forall expr cases,
    (forall n, ilh_returns_one (seq_of_labeled_statement (select_switch n cases))) ->
    ilh_returns_one (Sswitch expr cases).

Lemma ilh_returns_one_sound : forall s, ilh_returns_one s ->
  forall ge e le m t le' m' value ty,
  ocn_exec ge e le m s t le' m' (Out_return (Some (value, ty))) ->
  value = Vint Int.one /\ ty = tint.
Proof.
  intros s Hshape. induction Hshape; intros ge e le m t le' m' value ty Hrun.
  - pose proof (igb_no_return_outcome _ _ _ _ _ _ _ _ _ Hrun H) as Hbad. exact (False_ind _ Hbad).
  - inversion Hrun; subst. match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in H; subst end. split; reflexivity.
  - inversion Hrun; subst; [eapply IHHshape2|eapply IHHshape1]; eauto.
  - inversion Hrun; subst.
    match goal with Hout : outcome_switch ?out = Out_return _ |- _ =>
      destruct out; cbn in Hout; try discriminate; inversion Hout; subst end.
    eauto.
Qed.

Lemma ilh_actual_set_action_returns_one_shape : forall version,
  ilh_returns_one (fn_body (ilh_set_action_body version)).
Proof.
  intros []. all: unfold ilh_set_action_body; cbn [fn_body].
  all: apply ilh_one_sequence.
  1,3: apply ilh_one_switch; intro selector; apply ilh_one_nonreturn;
    cbv [select_switch select_switch_case select_switch_default seq_of_labeled_statement igb_no_return];
    repeat match goal with |- context [if ?test then _ else _] => destruct test end; reflexivity.
  all: repeat first [apply ilh_one_return
    |apply ilh_one_nonreturn; reflexivity|apply ilh_one_sequence].
Qed.

Theorem ilh_completed_set_action_call_returns_one : forall version m args t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ilh_set_action_body version)) args t m' result -> result = Vint Int.one.
Proof.
  intros version m args t m' result Hcall. inversion Hcall; subst.
  match goal with Hresult : outcome_result_value ?out _ _ _ |- _ =>
    assert (fn_return (ilh_set_action_body version) = tuint) as Hreturn
      by (destruct version; reflexivity);
    rewrite Hreturn in Hresult; destruct out; cbn in Hresult; try contradiction;
    match goal with o : option (val * type) |- _ => destruct o as [[value ty]|]; cbn in Hresult; try contradiction end
  end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (ilh_returns_one_sound _ (ilh_actual_set_action_returns_one_shape version)
      _ _ _ _ _ _ _ _ _ Hbody) as [-> ->] end.
  match goal with H : _ /\ sem_cast _ _ _ _ = Some _ |- _ =>
    destruct H as [_ Hcast]; cbn in Hcast; inversion Hcast; reflexivity end.
Qed.

Definition ilh_set_action_type := Tfunction
  [tptr (Tstruct IMB._MarioState noattr); tuint; tuint] tuint cc_default.

Lemma ilh_actual_set_action_statement_returns_one : forall version e le m id args t le' m' out,
  e ! IMB._set_mario_action = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Scall (Some id) (Evar IMB._set_mario_action ilh_set_action_type) args) t le' m' out ->
  le' = PTree.set id (Vint Int.one) le /\ out = Out_normal.
Proof.
  intros version e le m id args t le' m' out Hlocal Hrun.
  destruct (ilh_selected_set_action_resolves version) as (b & Hsymbol & Hfunction).
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hexpr : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ _ |- _ =>
    pose proof (ilh_completed_set_action_call_returns_one _ _ _ _ _ _ Hcall) as Hresult; subst end.
  split; reflexivity.
Qed.

Theorem ilh_duration_rejection_returns_one : forall version e le m t le' m' out,
  e ! IMB._set_mario_action = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ilh_duration_yes version) t le' m' out ->
  out = Out_return (Some (Vint Int.one, tuint)).
Proof.
  intros version e le m t le' m' out Hlocal Hrun.
  assert (ilh_duration_yes version =
    Ssequence (ilh_duration_before_return version) (Sreturn (Some (Etempvar IMB._t'5 tuint)))) as Hshape
    by exact (proj1 (ilh_duration_return_shape version)).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ (proj2 (ilh_duration_return_shape version)) Hrun)
    as (middle & memory & pre & suf & Htrace & Hprefix & Hreturn).
  assert (exists args read,
    ilh_duration_before_return version = Ssequence read
      (Scall (Some IMB._t'5) (Evar IMB._set_mario_action ilh_set_action_type) args) /\
    ibk_normal read = true) as (args & read & HprefixShape & HreadNormal)
    by (destruct version; eexists; eexists; split; reflexivity).
  rewrite HprefixShape in Hprefix.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HreadNormal Hprefix)
    as (call_le & call_m & read_t & call_t & Htrace2 & Hread & Hcall).
  destruct (ilh_actual_set_action_statement_returns_one _ _ _ _ _ _ _ _ _ _ Hlocal Hcall)
    as [Htemps _]. subst middle.
  inversion Hreturn; subst.
  match goal with H : eval_expr _ _ _ _ (Etempvar IMB._t'5 _) ?v |- _ =>
    assert (v = Vint Int.one) by (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst v end.
  reflexivity.
Qed.
