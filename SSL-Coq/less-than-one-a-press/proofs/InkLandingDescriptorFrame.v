(** Stock descriptor values survive a continuing cancellation call.  This
    proves the local storage connection, not lifetime privacy of the globals. *)
From Coq Require Import Bool List Lia ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ZeroAQuicksandEntryBoundary
  InkLandingReadOnly InkLandingCancellationSource InkLandingCancellationGate
  InkLandingCancellationCaller InkLandingCallerSource InkLandingHistorySource
  InkLandingHistoryGate InkLandingDurationRead InkMovingBackwardSource
  InkBackwardSource InkBackwardExecution InkFloorResetExecution InkAnimationDestination
  ContactConsumerExecution ObjectContactNecessity Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Opaque selected_clight_target.
Local Open Scope Z_scope.

Definition ildf_other_blocks version s : Prop :=
  forall le m mb mo t le' m',
  le ! IMB._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    s t le' m' Out_normal ->
  forall chunk db offset, mb <> db ->
    Mem.load chunk m' db offset = Mem.load chunk m db offset.

Lemma ildf_readonly : forall version s,
  cce_readonly_keep IMB._m s = true -> ildf_other_blocks version s.
Proof.
  intros version s Hshape le m mb mo t le' m' Hm Hrun chunk db offset Hother.
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun Hshape) as (_ & -> & _).
  reflexivity.
Qed.

Lemma ildf_return_tail : forall version prefix value,
  ildf_other_blocks version (Ssequence prefix (Sreturn value)).
Proof.
  intros version prefix value le m mb mo t le' m' Hm Hrun.
  inversion Hrun; subst; [|contradiction].
  match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn _) _ _ _ Out_normal |- _ =>
    inversion H end.
Qed.

Lemma ildf_sequence : forall version a b,
  ifr_keeps_temp IMB._m a = true ->
  ildf_other_blocks version a -> ildf_other_blocks version b ->
  ildf_other_blocks version (Ssequence a b).
Proof.
  intros version a b Hkeep Ha Hb le m mb mo t le' m' Hm Hrun chunk db offset Hother.
  inversion Hrun; subst; [|contradiction].
  match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ a _ ?middle ?memory Out_normal,
    Hlast : ClightBigstep.exec_stmt _ _ _ _ _ b _ _ _ Out_normal |- _ =>
    assert (middle ! IMB._m = Some (Vptr mb mo)) as Hnow by
      (rewrite <- Hm; eapply ifr_execution_keeps_temp; [exact Hfirst|exact Hkeep]);
    rewrite (Hb middle memory mb mo _ _ _ Hnow Hlast chunk db offset Hother);
    exact (Ha le m mb mo _ _ _ Hm Hfirst chunk db offset Hother)
  end.
Qed.

Lemma ildf_if : forall version condition yes no,
  ildf_other_blocks version yes -> ildf_other_blocks version no ->
  ildf_other_blocks version (Sifthenelse condition yes no).
Proof.
  intros version condition yes no Hy Hn le m mb mo t le' m' Hm Hrun.
  inversion Hrun; subst. destruct b; [eapply Hy|eapply Hn]; eassumption.
Qed.

Lemma ildf_mario_store : forall version lhs rhs,
  iad_write_root lhs = Some IMB._m ->
  ildf_other_blocks version (Sassign lhs rhs).
Proof.
  intros version lhs rhs Hroot le m mb mo t le' m' Hm Hrun chunk db offset Hother.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ lhs _ _ _ |- _ =>
    pose proof (iad_scalar_destination_block _ _ _ _ lhs IMB._m mb mo _ _ _
      Hroot Hm Hl) as Heq; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
  - eapply Mem.load_store_other; [eassumption|left; congruence].
  - destruct lhs; cbn [iad_write_root] in Hroot; try discriminate.
    match goal with Hmode : access_mode _ = By_copy |- _ =>
      cbn [typeof] in Hmode; rewrite Hmode in Hroot; discriminate end.
  - match goal with H : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ =>
      inversion H; subst end.
    eapply Mem.load_store_other; [eassumption|left; congruence].
Qed.

Lemma ildf_sliding_call : forall version opt args,
  ildf_other_blocks version
    (Scall opt (Evar IMB._should_begin_sliding (ilr_type ILRSlide)) args).
Proof.
  intros version opt args le m mb mo t le' m' Hm Hrun chunk db offset Hother.
  destruct (ilr_sliding_call_preserves_memory _ _ _ _ _ _ _ _ _ Hrun) as [_ ->].
  reflexivity.
Qed.

Theorem ildf_continuing_prefix_preserves_other_blocks : forall version,
  ildf_other_blocks version (ocn_prepend (ilh_before_gate version) Sskip).
Proof.
  intros []; cbv [ilh_before_gate ilh_cancel_body fn_body
    us_mario_actions_moving.f_common_landing_cancels
    jp_mario_actions_moving.f_common_landing_cancels ocn_prefix_items ocn_prepend].
  all: repeat first [
    apply ildf_readonly; reflexivity
  | apply ildf_return_tail
  | apply ildf_mario_store; reflexivity
  | apply ildf_sliding_call
  | apply ildf_sequence; [reflexivity| |]
  | apply ildf_if ].
Qed.

Lemma ildf_normal_gate_preserves_other_blocks : forall version,
  ildf_other_blocks version (ilh_gate version).
Proof.
  intros []; cbv [ilh_gate ilh_gate_tail ilh_cancel_body fn_body
    us_mario_actions_moving.f_common_landing_cancels
    jp_mario_actions_moving.f_common_landing_cancels rank12b_drop_sequences ibk_head].
  all: repeat first [
    apply ildf_readonly; reflexivity
  | apply ildf_return_tail
  | apply ildf_mario_store; reflexivity
  | apply ildf_sequence; [reflexivity| |]
  | apply ildf_if ].
Qed.

Lemma ildf_entry_argument : forall version m mb mo db dofs callback le,
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (ilh_cancel_body version) [Vptr mb mo; Vptr db dofs; callback]
    m empty_env le m ->
  le ! IMB._m = Some (Vptr mb mo).
Proof.
  intros version m mb mo db dofs callback le Hentry. inversion Hentry; subst.
  match goal with H : bind_parameter_temps _ _ _ = Some le |- _ =>
    assert (fn_params (ilh_cancel_body version) =
      [(IMB._m, ilw_mario_type); (IMB._landingAction, tptr ilw_descriptor_type);
       (IMB._setAPressAction, tptr ilw_callback_type)]) as Hp by (destruct version; reflexivity);
    rewrite Hp in H; cbn in H; inversion H; subst end.
  repeat rewrite PTree.gso by discriminate. apply PTree.gss.
Qed.

Definition InkCancellationDescriptorFrame : Prop :=
  forall version m mb mo db dofs callback t m',
  mb <> db ->
  icz_completed_path version m mb mo db dofs callback t m' ->
  forall chunk offset, Mem.load chunk m' db offset = Mem.load chunk m db offset.

Theorem ildf_returned_cancellation_preserves_descriptor : InkCancellationDescriptorFrame.
Proof.
  intros version m mb mo db dofs callback t m' Hother
    (entry_le & gate_le & gate_m & after_le & pre & gate_t &
     Htrace & Hentry & Hprefix & Hm & Hd & Hgate & Hbound) chunk offset.
  pose proof (ildf_entry_argument _ _ _ _ _ _ _ _ Hentry) as HentryM.
  rewrite (ildf_normal_gate_preserves_other_blocks version gate_le gate_m mb mo
    gate_t after_le m' Hm Hgate chunk db offset Hother).
  exact (ildf_continuing_prefix_preserves_other_blocks version entry_le m mb mo
    pre gate_le gate_m HentryM Hprefix chunk db offset Hother).
Qed.

Definition InkStockCancellationTimerBound : Prop :=
  forall version kind le m mb mo db t le' m',
  le ! IMB._m = Some (Vptr mb mo) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    (ilw_descriptor kind) = Some db ->
  mb <> db ->
  Mem.load Mint16signed m db 0 = Some (Vint (Int.repr (stock_landing_frames kind))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilw_guard version kind) t le' m' Out_normal ->
  exists timer,
    ilh_timer_load m' mb mo = Some (Vint timer) /\
    Int.unsigned timer < stock_landing_frames kind /\
    Mem.load Mint16signed m' db 0 =
      Some (Vint (Int.repr (stock_landing_frames kind))).

Theorem ildf_stock_guard_preserves_duration_and_bounds_timer : InkStockCancellationTimerBound.
Proof.
  intros version kind le m mb mo db t le' m' Hm Hdescriptor Hother Hstock Hrun.
  destruct (icz_stock_guard_reaches_live_duration version kind le m mb mo t le' m' Hm Hrun)
    as (db' & cb & Hdescriptor' & Hcallback & Hpath).
  rewrite Hdescriptor in Hdescriptor'. inversion Hdescriptor'; subst db'.
  pose proof (ildf_returned_cancellation_preserves_descriptor version m mb mo db
    Ptrofs.zero (Vptr cb Ptrofs.zero) t m' Hother Hpath Mint16signed 0) as Hframe.
  destruct Hpath as (entry_le & gate_le & gate_m & after_le & pre & gate_t &
    Htrace & Hentry & Hprefix & Hgm & Hgd & Hgate & before & frames & Hbefore &
    Htimer & Hframes & Hbound).
  change (Mem.load Mint16signed m' db 0 = Some (Vint frames)) in Hframes.
  rewrite Hframe, Hstock in Hframes. inversion Hframes; subst frames.
  exists (ilh_next_timer before). split; [exact Htimer|]. split.
  - destruct kind; exact Hbound.
  - now rewrite Hframe.
Qed.

Corollary ildf_stock_guard_late_timer_requires_long_jump : forall version kind le m mb mo db t le' m',
  le ! IMB._m = Some (Vptr mb mo) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    (ilw_descriptor kind) = Some db ->
  mb <> db ->
  Mem.load Mint16signed m db 0 = Some (Vint (Int.repr (stock_landing_frames kind))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilw_guard version kind) t le' m' Out_normal ->
  forall timer, ilh_timer_load m' mb mo = Some (Vint timer) -> 4 <= Int.unsigned timer ->
  kind = StockLongJumpLand /\ (Int.unsigned timer = 4 \/ Int.unsigned timer = 5).
Proof.
  intros version kind le m mb mo db t le' m' Hm Hsymbol Hother Hstock Hrun timer Htimer Hlate.
  destruct (ildf_stock_guard_preserves_duration_and_bounds_timer
    version kind le m mb mo db t le' m' Hm Hsymbol Hother Hstock Hrun)
    as (next & Hnext & Hbound & _).
  rewrite Hnext in Htimer. inversion Htimer; subst next.
  destruct kind; cbn [stock_landing_frames] in Hbound; try lia.
  split; [reflexivity|lia].
Qed.
