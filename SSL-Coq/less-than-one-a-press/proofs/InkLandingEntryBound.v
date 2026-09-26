(** Six stock wrappers pass the just-checked timer straight to the actual
    common landing call.  The other three have a voice call in this interval.
    This proves the connection at body ENTRY, not the later depth write. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ZeroAQuicksandEntryBoundary
  InkLandingCallerSource InkLandingCallerGate InkLandingDescriptorFrame
  InkLandingHistoryGate InkMovingBackwardSource InkBackwardSource InkBackwardExecution
  InkLateCallExecution InkFloorResetExecution SecretContactExecution
  ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Opaque selected_clight_target.
Local Open Scope Z_scope.

Definition ile_direct_kind kind := match kind with
| StockLongJumpLand | StockTripleJumpLand | StockBackflipLand => false
| _ => true end.
Definition ile_type := Tfunction [ilw_mario_type; tshort; tuint] tuint cc_default.

Inductive ile_front_call (opt : option ident) (args : list expr) : statement -> Prop :=
| ile_here : ile_front_call opt args
    (Scall opt (Evar IMB._common_landing_action ile_type) args)
| ile_left : forall first rest, ile_front_call opt args first ->
    ile_front_call opt args (Ssequence first rest).

Lemma ile_real_six_wrappers_start_with_landing : forall version kind,
  ile_direct_kind kind = true ->
  exists opt rest, ile_front_call opt (Etempvar IMB._m ilw_mario_type :: rest)
    (ilw_after version kind).
Proof.
  intros [] []; cbn [ile_direct_kind]; intros H; try discriminate;
    do 2 eexists; repeat apply ile_left; apply ile_here.
Qed.

Lemma ile_front_call_is_executed : forall ge e opt args s,
  ile_front_call opt args s -> forall le m t le' m' out,
  ocn_exec ge e le m s t le' m' out ->
  exists call_t call_le call_m,
    ocn_exec ge e le m
      (Scall opt (Evar IMB._common_landing_action ile_type) args)
      call_t call_le call_m Out_normal.
Proof.
  intros ge e opt args s Hshape. induction Hshape;
    intros le m t le' m' out Hrun.
  - inversion Hrun; subst. eauto.
  - inversion Hrun; subst; eapply IHHshape; eassumption.
Qed.

Lemma ile_call_resolves_and_keeps_mario : forall version opt rest le m mb mo t le' m' out,
  le ! IMB._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Scall opt (Evar IMB._common_landing_action ile_type)
      (Etempvar IMB._m ilw_mario_type :: rest)) t le' m' out ->
  exists animation airAction result,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (imb_body version IMBLanding))
      [Vptr mb mo; animation; airAction] t m' result.
Proof.
  intros version opt rest le m mb mo t le' m' out Hm Hrun.
  inversion Hrun; subst.
  match goal with H : classify_fun _ = _ |- _ => cbn in H; inversion H; subst end.
  destruct (imb_selected_bodies_resolve version IMBLanding) as (fb & Hsymbol & Hfunction).
  match goal with H : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (eapply (sce_function_name_value
        (Clight.globalenv (selected_clight_target version)) empty_env le m
        IMB._common_landing_action [ilw_mario_type; tshort; tuint]
        tuint cc_default fb vf); [reflexivity|exact Hsymbol|exact H]); subst vf end.
  match goal with H : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in H;
    rewrite Hfunction in H; inversion H; subst fd end.
  match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ (Etempvar IMB._m _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : sem_cast (Vptr mb mo) _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst end.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  do 3 eexists; eassumption.
Qed.

Definition InkSixLandingEntryBound : Prop :=
  forall version kind le m mb mo db guard_t ready_le ready_m tail_t le' m' out,
  ile_direct_kind kind = true ->
  le ! IMB._m = Some (Vptr mb mo) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    (ilw_descriptor kind) = Some db -> mb <> db ->
  Mem.load Mint16signed m db 0 = Some (Vint (Int.repr (stock_landing_frames kind))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilw_guard version kind) guard_t ready_le ready_m Out_normal ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env ready_le ready_m
    (ilw_after version kind) tail_t le' m' out ->
  exists timer animation airAction call_t call_m result,
    ilh_timer_load ready_m mb mo = Some (Vint timer) /\ Int.unsigned timer < 4 /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      ready_m (Internal (imb_body version IMBLanding))
      [Vptr mb mo; animation; airAction] call_t call_m result.

Theorem ile_six_actual_wrappers_enter_landing_below_four : InkSixLandingEntryBound.
Proof.
  intros version kind le m mb mo db guard_t ready_le ready_m tail_t le' m' out
    Hkind Hm Hsymbol Hother Hstock Hguard Htail.
  destruct (ildf_stock_guard_preserves_duration_and_bounds_timer
    version kind le m mb mo db guard_t ready_le ready_m Hm Hsymbol Hother Hstock Hguard)
    as (timer & Htimer & Hbound & Hdescriptor).
  assert (Int.unsigned timer < 4) as Hsmall by
    (destruct kind; cbn [ile_direct_kind] in Hkind; try discriminate; exact Hbound).
  assert (ready_le ! IMB._m = Some (Vptr mb mo)) as Hready.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IMB._m Hguard
      ltac:(destruct version, kind; reflexivity)). exact Hm. }
  destruct (ile_real_six_wrappers_start_with_landing version kind Hkind) as (opt & rest & Hfront).
  destruct (ile_front_call_is_executed _ _ _ _ _ Hfront _ _ _ _ _ _ Htail)
    as (call_t & call_le & call_m & Hcall).
  destruct (ile_call_resolves_and_keeps_mario _ _ _ _ _ _ _ _ _ _ _ Hready Hcall)
    as (animation & airAction & result & Hlanding).
  do 6 eexists. repeat split; eassumption.
Qed.
