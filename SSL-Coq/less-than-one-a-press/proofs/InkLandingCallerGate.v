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

From LessThanOneAPress.Proofs Require Import InkLandingCallerSource.

(** A caller continuation is possible only after the actual callee returns
    zero. Its full memory effects are retained in [memory]; none is framed. *)
Definition InkLandingWrapperGuard : Prop := forall version kind le m t le' m',
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilw_guard version kind) t le' m' Out_normal ->
  exists args,
    eval_exprlist (Clight.globalenv (selected_clight_target version)) empty_env le m
      (ilw_arguments kind)
      [ilw_mario_type; tptr ilw_descriptor_type; tptr ilw_callback_type] args /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ilh_cancel_body version)) args t m' (Vint Int.zero) /\
    le' = PTree.set (ilw_result_temp kind) (Vint Int.zero) le.

Lemma ilw_false_int_is_zero : forall value m,
  bool_val value tint m = Some false -> value = Vint Int.zero.
Proof.
  intros value m H. destruct value; cbn in H; try discriminate.
  destruct (Int.eq i Int.zero) eqn:E; try discriminate.
  apply Int.same_if_eq in E. subst; reflexivity.
  all: repeat match goal with H : context [if ?test then _ else _] |- _ =>
    destruct test; cbn in H end; discriminate.
Qed.

Theorem ilw_continuation_requires_real_cancel_return_zero : InkLandingWrapperGuard.
Proof.
  intros version kind le m t le' m' Hrun.
  destruct (ilw_source_cuts version kind) as (_ & _ & _ & Hguard & _).
  rewrite Hguard in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (ilw_call kind) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hcall & Htest).
  unfold ilw_call in Hcall. inversion Hcall; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (ilh_selected_cancels_resolves version) as (fb & Hsymbol & Hfunction).
  unfold ilw_cancel_type in *.
  lazymatch goal with Hr : eval_expr _ _ _ _ (Evar IMB._common_landing_cancels _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (eapply (sce_function_name_value
        (Clight.globalenv (selected_clight_target version)) empty_env le m
        IMB._common_landing_cancels
        [ilw_mario_type; tptr ilw_descriptor_type; tptr ilw_callback_type]
        tint cc_default fb vf); [reflexivity|exact Hsymbol|exact Hr]); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  inversion Htest; subst. destruct b.
  - unfold ilw_return_one in *. match goal with
      H : ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn _) _ _ _ Out_normal |- _ => inversion H end.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion H; subst end.
    match goal with H : eval_expr _ _ _ _ (ilw_test kind) ?answer |- _ =>
      unfold ilw_test in H;
      assert (answer = vres) by (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst answer end.
    match goal with H : bool_val vres _ _ = Some false |- _ =>
      apply ilw_false_int_is_zero in H; subst vres end.
    rewrite ?E0_right. eexists. repeat split; eassumption || reflexivity.
Qed.

(** Split a real statement prefix without assuming it returns normally. *)
Lemma ilw_prefix_paths : forall ge e items tail le m t le' m' out,
  ocn_exec ge e le m (ocn_prepend items tail) t le' m' out ->
  (out <> Out_normal /\ ocn_exec ge e le m (ocn_prepend items Sskip) t le' m' out) \/
  exists middle memory pre suf,
    t = pre ++ suf /\
    ocn_exec ge e le m (ocn_prepend items Sskip) pre middle memory Out_normal /\
    ocn_exec ge e middle memory tail suf le' m' out.
Proof.
  intros ge e items. induction items as [|head rest IH];
    intros tail le m t le' m' out Hrun.
  - right. exists le, m, E0, t. repeat split; try exact Hrun. constructor.
  - cbn [ocn_prepend] in Hrun. inversion Hrun; subst.
    + match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (ocn_prepend rest tail) _ _ _ _ |- _ =>
        destruct (IH _ _ _ _ _ _ _ H) as [[Hout Hprefix]|(mid & mem & pre & suf & Ht & Hp & Hs)] end.
      * left. split; [exact Hout|]. cbn [ocn_prepend]. eapply exec_Sseq_1; eauto.
      * right. exists mid, mem, (t1 ++ pre), suf.
        split.
        { change (t1 ++ t2 = (t1 ++ pre) ++ suf).
          rewrite Ht, app_assoc. reflexivity. }
        split; [cbn [ocn_prepend]; eapply exec_Sseq_1; eauto|exact Hs].
    + left. split; [assumption|]. cbn [ocn_prepend]. eapply exec_Sseq_2; eauto.
Qed.

Definition ilw_caller_path version kind le m t le' m' out : Prop :=
  (out <> Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (ocn_prepend (ilw_before version kind) Sskip) t le' m' out) \/
  exists guard_le guard_m pre tail,
    t = pre ++ tail /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (ocn_prepend (ilw_before version kind) Sskip) pre guard_le guard_m Out_normal /\
    ((out <> Out_normal /\
      ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env guard_le guard_m
        (ilw_guard version kind) tail le' m' out) \/
     exists args after_m cancel_t suffix,
       tail = cancel_t ++ suffix /\
       eval_exprlist (Clight.globalenv (selected_clight_target version)) empty_env guard_le guard_m
         (ilw_arguments kind)
         [ilw_mario_type; tptr ilw_descriptor_type; tptr ilw_callback_type] args /\
       ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
         guard_m (Internal (ilh_cancel_body version)) args cancel_t after_m (Vint Int.zero) /\
       ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
         (PTree.set (ilw_result_temp kind) (Vint Int.zero) guard_le) after_m
         (ilw_after version kind) suffix le' m' out).

Lemma ilw_body_paths : forall version kind le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (fn_body (ilw_body version kind)) t le' m' out ->
  ilw_caller_path version kind le m t le' m' out.
Proof.
  intros version kind le m t le' m' out Hrun.
  destruct (ilw_source_cuts version kind) as (_ & _ & Hbody & _).
  rewrite Hbody in Hrun.
  destruct (ilw_prefix_paths _ _ _ _ _ _ _ _ _ _ Hrun)
    as [Hearly|(guard_le & guard_m & pre & tail & Ht & Hp & Hr)].
  - left. exact Hearly.
  - right. exists guard_le, guard_m, pre, tail. split; [exact Ht|]. split; [exact Hp|].
    inversion Hr; subst.
    + right. match goal with
        Hg : ClightBigstep.exec_stmt _ _ _ _ _ (ilw_guard _ _) _ _ _ Out_normal |- _ =>
        destruct (ilw_continuation_requires_real_cancel_return_zero _ _ _ _ _ _ _ Hg)
          as (args & Hargs & Hcancel & Htemps) end.
      subst. do 4 eexists. repeat split; eassumption || reflexivity.
    + left. split; assumption.
Qed.

Definition InkCompletedLandingCaller : Prop := forall version kind m mb mo t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ilw_body version kind)) [Vptr mb mo] t m' result ->
  exists le last out,
    function_entry2 (Clight.globalenv (selected_clight_target version))
      (ilw_body version kind) [Vptr mb mo] m empty_env le m /\
    le ! IMB._m = Some (Vptr mb mo) /\
    ilw_caller_path version kind le m t last m' out /\
    outcome_result_value out (fn_return (ilw_body version kind)) result m'.

Theorem ilw_completed_wrapper_exits_or_checks_real_callee : InkCompletedLandingCaller.
Proof.
  intros version kind m mb mo t m' result Hcall.
  destruct (ilw_source_cuts version kind) as (Hvars & Hparams & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    pose proof He as Hentry; inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IMB._m = Some (Vptr mb mo)) as Hm by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; apply PTree.gss) end.
  do 3 eexists. repeat first [eassumption | split].
  eapply ilw_body_paths. eassumption.
Qed.

Definition InkLandingCallerGateBoundary : Prop :=
  (internal_statement_predicate_sites (calls_ident_s IMB._common_landing_action)
    us_generated_definitions = map ilw_ident ilw_kinds /\
   internal_statement_predicate_sites (calls_ident_s IMB._common_landing_action)
    jp_generated_definitions_for_alias = map ilw_ident ilw_kinds) /\
  (forall version kind, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ilw_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ilw_body version kind))) /\
  InkLandingWrapperGuard /\ InkCompletedLandingCaller.
Theorem ilw_landing_caller_gate_checked : InkLandingCallerGateBoundary.
Proof.
  split; [exact ilw_all_direct_common_landing_callers|].
  split; [exact ilw_selected_wrappers_resolve|].
  split; [exact ilw_continuation_requires_real_cancel_return_zero|
    exact ilw_completed_wrapper_exits_or_checks_real_callee].
Qed.
