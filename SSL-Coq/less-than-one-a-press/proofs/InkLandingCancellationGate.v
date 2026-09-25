(** Complete cancellation calls: real rejection returns and the live duration read. *)
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

From LessThanOneAPress.Proofs Require Import InkLandingCancellationSource.

From LessThanOneAPress.Proofs Require Import InkLandingCancellationReturn.
From LessThanOneAPress.Proofs Require Import InkLandingDurationRead.
Local Opaque selected_clight_target.

Definition icz_result_type kind := match kind with ICPush => tuint | _ => tint end.
Definition icz_function_type kind := Tfunction [ilw_mario_type; tuint; tuint]
  (icz_result_type kind) cc_default.

Lemma icz_named_helper_returns_one : forall version kind le m id args t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Scall (Some id) (Evar (icz_ident kind) (icz_function_type kind)) args) t le' m' out ->
  le' = PTree.set id (Vint Int.one) le /\ out = Out_normal.
Proof.
  intros version kind le m id args t le' m' out Hrun.
  destruct (icz_selected_helpers_resolve version kind) as (b & Hsymbol & Hfunction).
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn [icz_function_type] in Hclass; inversion Hclass; subst end.
  match goal with Hexpr : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply (sce_function_name_value (Clight.globalenv (selected_clight_target version)) empty_env le m
      (icz_ident kind) [ilw_mario_type; tuint; tuint] (icz_result_type kind) cc_default b vf);
      [apply PTree.gempty|exact Hsymbol|exact Hexpr]); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ _ |- _ =>
    pose proof (icz_completed_helper_returns_one version kind _ _ _ _ _ Hcall) as Hresult; subst end.
  split; reflexivity.
Qed.

Lemma icz_indirect_callback_returns_one : forall version kind callback le m id args t le' m' out,
  Genv.find_funct (Clight.globalenv (selected_clight_target version)) callback =
    Some (Internal (icz_body version kind)) ->
  le ! IMB._setAPressAction = Some callback ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Scall (Some id) (Etempvar IMB._setAPressAction (tptr ilw_callback_type)) args) t le' m' out ->
  le' = PTree.set id (Vint Int.one) le /\ out = Out_normal.
Proof.
  intros version kind callback le m id args t le' m' out Hfunction Htemp Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hexpr : eval_expr _ _ _ _ (Etempvar _ _) ?vf |- _ =>
    assert (vf = callback) by (eapply ocn_temp_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ callback = Some ?fd |- _ =>
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ _ |- _ =>
    pose proof (icz_completed_helper_returns_one version kind _ _ _ _ _ Hcall) as Hresult; subst end.
  split; reflexivity.
Qed.

Lemma icz_read_call_return_one : forall version read id f args ty,
  ibk_normal read = true ->
  (forall le m t le' m' out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (Scall (Some id) f args) t le' m' out ->
    le' = PTree.set id (Vint Int.one) le /\ out = Out_normal) ->
  forall le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Ssequence (Ssequence read (Scall (Some id) f args))
      (Sreturn (Some (Etempvar id ty)))) t le' m' out ->
  out = Out_return (Some (Vint Int.one, ty)).
Proof.
  intros version read id f args ty Hnormal Hcall le m t le' m' out Hrun.
  assert (ibk_normal (Ssequence read (Scall (Some id) f args)) = true) as Hprefix
    by (cbn [ibk_normal]; rewrite Hnormal; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hprefix Hrun)
    as (middle & memory & pre & suf & Htrace & Hbefore & Hreturn).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hbefore)
    as (call_le & call_m & read_t & call_t & Htrace2 & Hread & Hcalled).
  destruct (Hcall _ _ _ _ _ _ Hcalled) as [Hle _]. subst middle.
  inversion Hreturn; subst.
  match goal with H : eval_expr _ _ _ _ (Etempvar id _) ?v |- _ =>
    assert (v = Vint Int.one) by (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst v end.
  reflexivity.
Qed.

Definition icz_normal_or_one version s := forall le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m s t le' m' out ->
  out = Out_normal \/ out = Out_return (Some (Vint Int.one, tuint)).

Lemma icz_prefix_normal : forall version s,
  ibk_normal s = true -> icz_normal_or_one version s.
Proof.
  intros version s Hnormal le m t le' m' out Hrun. left.
  exact (ibk_normal_outcome _ _ _ _ s _ _ _ _ Hnormal Hrun).
Qed.
Lemma icz_prefix_sequence : forall version a b,
  icz_normal_or_one version a -> icz_normal_or_one version b ->
  icz_normal_or_one version (Ssequence a b).
Proof.
  intros version a b Ha Hb le m t le' m' out Hrun.
  inversion Hrun; subst; [eapply Hb|eapply Ha]; eassumption.
Qed.
Lemma icz_prefix_if : forall version cond a b,
  icz_normal_or_one version a -> icz_normal_or_one version b ->
  icz_normal_or_one version (Sifthenelse cond a b).
Proof.
  intros version cond a b Ha Hb le m t le' m' out Hrun.
  inversion Hrun; subst. destruct b0; [eapply Ha|eapply Hb]; eassumption.
Qed.
Lemma icz_prefix_return : forall version read id f args,
  ibk_normal read = true ->
  (forall le m t le' m' out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (Scall (Some id) f args) t le' m' out ->
    le' = PTree.set id (Vint Int.one) le /\ out = Out_normal) ->
  icz_normal_or_one version (Ssequence (Ssequence read (Scall (Some id) f args))
    (Sreturn (Some (Etempvar id tuint)))).
Proof.
  intros version read id f args Hnormal Hcall le m t le' m' out Hrun.
  right. exact (icz_read_call_return_one version read id f args tuint Hnormal Hcall
    le m t le' m' out Hrun).
Qed.

Lemma icz_before_gate_normal_or_one : forall version le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ocn_prepend (ilh_before_gate version) Sskip) t le' m' out ->
  out = Out_normal \/ out = Out_return (Some (Vint Int.one, tuint)).
Proof.
  intro version. change (icz_normal_or_one version (ocn_prepend (ilh_before_gate version) Sskip)).
  destruct version; cbv [ilh_before_gate ilh_cancel_body fn_body
    us_mario_actions_moving.f_common_landing_cancels jp_mario_actions_moving.f_common_landing_cancels
    ocn_prefix_items ocn_prepend].
  all: repeat first [apply icz_prefix_normal; reflexivity
    |apply icz_prefix_return; [reflexivity|]
    |apply icz_prefix_sequence | apply icz_prefix_if].
  all: intros le m t le' m' out Hrun.
  all: lazymatch type of Hrun with
  | ocn_exec (Clight.globalenv (selected_clight_target ?v)) _ _ _ _ _ _ _ _ =>
    first [exact (icz_named_helper_returns_one v ICPush le m _ _ t le' m' out Hrun)
    |exact (ilh_actual_set_action_statement_returns_one v empty_env le m _ _ t le' m' out eq_refl Hrun)]
  end.
Qed.

Lemma icz_after_gate_zero_preserves_memory : forall version kind callback le m t le' m' out,
  Genv.find_funct (Clight.globalenv (selected_clight_target version)) callback =
    Some (Internal (icz_body version kind)) ->
  le ! IMB._setAPressAction = Some callback ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilh_after_gate version) t le' m' out ->
  outcome_result_value out tint (Vint Int.zero) m' ->
  m' = m /\ t = E0 /\ out = Out_return (Some (Vint Int.zero, tint)).
Proof.
  intros version kind callback le m t le' m' out Hfunction Hcallback Hrun Hresult.
  destruct version; cbv [ilh_after_gate ilh_cancel_body rank12b_drop_sequences fn_body
    us_mario_actions_moving.f_common_landing_cancels jp_mario_actions_moving.f_common_landing_cancels] in Hrun.
  all: unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun; cce_unroll_loop_free_exec.
  all: repeat match goal with
  | H : ClightBigstep.exec_stmt _ (Clight.globalenv (selected_clight_target ?ver)) empty_env
      ?temps ?memory (Scall (Some ?id) (Evar ?callee ?ty) ?args) ?tr ?next ?mem ?out |- _ =>
      let Heq := constr:(eq_refl : callee = IMB._set_mario_action) in
      destruct (ilh_actual_set_action_statement_returns_one ver empty_env temps memory id args tr next mem out eq_refl H)
        as [Hle Ho]; subst; clear H
  | H : ClightBigstep.exec_stmt _ (Clight.globalenv (selected_clight_target ?ver)) empty_env
      ?temps ?memory (Scall (Some ?id) (Etempvar ?callee ?ty) ?args) ?tr ?next ?mem ?out |- _ =>
      let Heq := constr:(eq_refl : callee = IMB._setAPressAction) in
      assert (temps ! IMB._setAPressAction = Some callback) as Hnow by
        (repeat rewrite PTree.gso by discriminate; exact Hcallback);
      destruct (icz_indirect_callback_returns_one ver kind callback temps memory id args tr next mem out
        Hfunction Hnow H) as [Hle Ho]; subst; clear H
  end.
  all: try solve [match goal with Hbad : ?out <> Out_normal,
    Hr : ClightBigstep.exec_stmt _ _ _ _ _ ?stmt _ _ _ ?out |- _ =>
    exfalso; apply Hbad; eapply (ibk_normal_outcome _ _ _ _ stmt); [reflexivity|exact Hr] end].
  all: repeat match goal with
  | H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst
  | H : eval_expr _ _ (PTree.set ?id (Vint Int.one) _) _ (Etempvar ?id _) ?v |- _ =>
      assert (v = Vint Int.one) by (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst v; clear H
  end.
  all: cbn in Hresult; try contradiction; try discriminate; try (destruct Hresult as [_ Hbad]; discriminate).
  all: repeat split; reflexivity.
Qed.

Definition icz_completed_path version m mb mo db dofs callback t m' : Prop :=
  exists entry_le gate_le gate_m after_le pre gate_t,
    t = pre ++ gate_t /\
    function_entry2 (Clight.globalenv (selected_clight_target version)) (ilh_cancel_body version)
      [Vptr mb mo; Vptr db dofs; callback] m empty_env entry_le m /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env entry_le m
      (ocn_prepend (ilh_before_gate version) Sskip) pre gate_le gate_m Out_normal /\
    gate_le ! IMB._m = Some (Vptr mb mo) /\
    gate_le ! IMB._landingAction = Some (Vptr db dofs) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env gate_le gate_m
      (ilh_gate version) gate_t after_le m' Out_normal /\
    (exists before frames,
        ilh_timer_load gate_m mb mo = Some (Vint before) /\
        ilh_timer_load m' mb mo = Some (Vint (ilh_next_timer before)) /\
        Mem.load Mint16signed m' db (Ptrofs.unsigned dofs) = Some (Vint frames) /\
        Int.unsigned (ilh_next_timer before) < Int.signed frames).

Definition InkCompletedCancellationGate : Prop :=
  forall version kind callback m mb mo db dofs t m',
  Genv.find_funct (Clight.globalenv (selected_clight_target version)) callback =
    Some (Internal (icz_body version kind)) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ilh_cancel_body version)) [Vptr mb mo; Vptr db dofs; callback] t m' (Vint Int.zero) ->
  icz_completed_path version m mb mo db dofs callback t m'.

Theorem icz_completed_zero_return_reaches_duration_gate : InkCompletedCancellationGate.
Proof.
  intros version kind callback m mb mo db dofs t m' Hfunction Hcall.
  destruct (ilh_source_cuts version) as (Hvars & HbodyShape & HtailShape & _).
  assert (fn_return (ilh_cancel_body version) = tint) as Hreturn by (destruct version; reflexivity).
  assert (fn_params (ilh_cancel_body version) =
    [(IMB._m, ilw_mario_type); (IMB._landingAction, tptr ilw_descriptor_type);
     (IMB._setAPressAction, tptr ilw_callback_type)]) as Hparams by (destruct version; reflexivity).
  inversion Hcall; subst.
  match goal with Hr : outcome_result_value _ (fn_return _) _ _ |- _ => rewrite Hreturn in Hr end.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    pose proof He as Hentry; inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?entry |- _ =>
    assert (entry ! IMB._m = Some (Vptr mb mo) /\
      entry ! IMB._landingAction = Some (Vptr db dofs) /\
      entry ! IMB._setAPressAction = Some callback) as (Hm & Hd & Hcallback)
      by (rewrite Hparams in Hb; cbn in Hb; inversion Hb; repeat split;
          repeat first [apply PTree.gss | rewrite PTree.gso by discriminate]) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite HbodyShape in Hr;
    destruct (ilw_prefix_paths _ _ _ _ _ _ _ _ _ _ Hr)
      as [[Hout Hpre]|(gate_le & gate_m & pre & tail & Ht & Hpre & Htail)] end.
  - destruct (icz_before_gate_normal_or_one version _ _ _ _ _ _ Hpre) as [Heq|Heq];
      [contradiction|subst].
    match goal with Hres : outcome_result_value _ _ _ _ |- _ =>
      cbn in Hres;
      destruct Hres as [_ Hbad]; discriminate end.
  - assert (gate_le ! IMB._m = Some (Vptr mb mo) /\
      gate_le ! IMB._landingAction = Some (Vptr db dofs) /\
      gate_le ! IMB._setAPressAction = Some callback) as (Hgm & Hgd & Hgc).
    { repeat split.
      all: rewrite <- ?Hm, <- ?Hd, <- ?Hcallback;
        eapply ifr_execution_keeps_temp; [exact Hpre|destruct version; reflexivity]. }
    rewrite HtailShape in Htail. inversion Htail; subst.
    + match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (ilh_gate _) _ ?after ?memory Out_normal |- _ =>
        assert (after ! IMB._setAPressAction = Some callback) as Hac by
          (rewrite <- Hgc; eapply ifr_execution_keeps_temp; [exact Hg|destruct version; reflexivity]) end.
      match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (ilh_after_gate _) _ _ _ _,
        Hr : outcome_result_value _ _ _ _ |- _ =>
        destruct (icz_after_gate_zero_preserves_memory version kind callback _ _ _ _ _ _ Hfunction Hac Ha Hr)
          as (Hmem & Htrace & Hout); subst end.
      match goal with Hg : ClightBigstep.exec_stmt _ _ _ ?temps ?mem (ilh_gate _) ?tr ?after ?last Out_normal |- _ =>
        pose proof (ild_executed_gate_reads_and_bounds_timer version empty_env temps mem mb mo db dofs
          tr after last Hgm Hgd Hg) as Hbounded end.
      unfold icz_completed_path.
      match goal with He : function_entry2 _ _ _ _ empty_env ?entry _,
        Hg : ClightBigstep.exec_stmt _ _ _ ?temps ?mem (ilh_gate _) ?tr ?after _ Out_normal |- _ =>
        exists entry, temps, mem, after, pre, tr end.
      split; [rewrite ?E0_right; reflexivity|].
      repeat first [eassumption | split].
    + match goal with Hg : ClightBigstep.exec_stmt _ _ _ ?temps ?mem (ilh_gate _) ?tr ?next ?last ?out |- _ =>
        destruct (ilh_gate_normal_or_nonzero_return version empty_env temps mem tr next last out eq_refl Hg) as [Hnormal|Hone];
        [contradiction|subst] end.
      match goal with Hr : outcome_result_value _ _ _ _ |- _ =>
        cbn in Hr; destruct Hr as [_ Hbad]; discriminate end.
Qed.
