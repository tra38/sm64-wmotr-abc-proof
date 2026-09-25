(** Apply the completed cancellation result to the stock wrappers' actual
    descriptor address and function-pointer argument. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ZeroAQuicksandEntryBoundary
  InkLandingCallerSource InkLandingCallerGate InkLandingCancellationSource
  InkLandingCancellationGate InkLandingHistorySource InkLandingHistoryGate
  InkMovingBackwardSource InkBackwardExecution InkFloorResetExecution
  SecretContactExecution ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Opaque selected_clight_target.

Definition icz_stock_callback kind := match kind with
| StockDoubleJumpLand => ICTriple | _ => ICJump end.

Lemma icz_stock_callback_resolves : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ilw_callback kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (icz_body version (icz_stock_callback kind))).
Proof.
  intros version []; first [exact (icz_selected_helpers_resolve version ICJump)
    |exact (icz_selected_helpers_resolve version ICTriple)].
Qed.

Theorem icz_stock_cancel_arguments_are_real : forall version kind le m mb mo args,
  le ! IMB._m = Some (Vptr mb mo) ->
  eval_exprlist (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilw_arguments kind) [ilw_mario_type; tptr ilw_descriptor_type; tptr ilw_callback_type] args ->
  exists db cb,
    args = [Vptr mb mo; Vptr db Ptrofs.zero; Vptr cb Ptrofs.zero] /\
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ilw_descriptor kind) = Some db /\
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ilw_callback kind) = Some cb /\
    Genv.find_funct (Clight.globalenv (selected_clight_target version)) (Vptr cb Ptrofs.zero) =
      Some (Internal (icz_body version (icz_stock_callback kind))).
Proof.
  intros version kind le m mb mo args Hm Hargs.
  destruct (icz_stock_callback_resolves version kind) as (cb & Hsymbol & Hfunction).
  unfold ilw_arguments in Hargs.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ (Etempvar IMB._m _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : eval_expr _ _ _ _ (Evar (ilw_callback kind) _) ?v |- _ =>
    assert (v = Vptr cb Ptrofs.zero) by
      (eapply (sce_function_name_value (Clight.globalenv (selected_clight_target version))
        empty_env le m (ilw_callback kind) [ilw_mario_type; tuint; tuint] tint cc_default cb v);
       [apply PTree.gempty|exact Hsymbol|exact H]); subst v end.
  match goal with H : eval_expr _ _ _ _ (Eaddrof _ _) _ |- _ => inversion H; subst; clear H end.
  all: try solve [match goal with H : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion H end].
  match goal with H : eval_lvalue _ _ _ _ (Evar (ilw_descriptor kind) _) _ _ _ |- _ =>
    inversion H; subst; clear H end.
  - match goal with H : empty_env ! _ = Some _ |- _ => rewrite PTree.gempty in H; discriminate end.
  - repeat match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst; clear H end.
    do 2 eexists. repeat split; reflexivity || eassumption.
Qed.

Definition InkStockCancellationGuard : Prop := forall version kind le m mb mo t le' m',
  le ! IMB._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilw_guard version kind) t le' m' Out_normal ->
  exists db cb,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ilw_descriptor kind) = Some db /\
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ilw_callback kind) = Some cb /\
    icz_completed_path version m mb mo db Ptrofs.zero (Vptr cb Ptrofs.zero) t m'.

Theorem icz_stock_guard_reaches_live_duration : InkStockCancellationGuard.
Proof.
  intros version kind le m mb mo t le' m' Hm Hrun.
  destruct (ilw_continuation_requires_real_cancel_return_zero version kind le m t le' m' Hrun)
    as (args & Hargs & Hcall & Htemps).
  destruct (icz_stock_cancel_arguments_are_real version kind le m mb mo args Hm Hargs)
    as (db & cb & Hvalues & Hd & Hc & Hfunction). subst args.
  exists db, cb. split; [exact Hd|]. split; [exact Hc|].
  exact (icz_completed_zero_return_reaches_duration_gate version (icz_stock_callback kind)
    (Vptr cb Ptrofs.zero) m mb mo db Ptrofs.zero t m' Hfunction Hcall).
Qed.
