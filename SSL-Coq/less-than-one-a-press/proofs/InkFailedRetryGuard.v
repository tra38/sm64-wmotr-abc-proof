(** A concrete part of the failed-retry continuation: the actual US/JP
    level_trigger_warp body cannot replace an already pending operation.

    The live signed-short load at this call is required to be nonzero.
    The proof opens the generated guard and skips its entire scheduling
    branch; no callee-effect premise is used. In particular, when death or
    game-over is still pending, a later object-warp request makes no memory
    change. This does NOT derive the earlier death installation, frame the
    intervening interaction calls, block ACT_DISAPPEARED selection, or refine
    the complete scheduler/reset history. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_level_update jp_level_update.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution ObjectContactNecessity ContactConsumerExecution
  SecretContactExecution Area2Rank12BContact.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IFG := us_level_update.

Definition ifg_trigger_body version := match version with
| VersionUS => us_level_update.f_level_trigger_warp
| VersionJP => jp_level_update.f_level_trigger_warp end.
Definition ifg_after_init version := rank12b_drop_sequences 1
  (fn_body (ifg_trigger_body version)).
Definition ifg_pending_gate version := ibk_head (ifg_after_init version).
Definition ifg_return_tail version := rank12b_drop_sequences 1 (ifg_after_init version).
Definition ifg_schedule_branch version := match ifg_pending_gate version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Definition ifg_pending_guard := Ebinop Oeq (Etempvar IFG._t'7 tshort)
  (Econst_int Int.zero tint) tint.

Lemma ifg_actual_source : forall version,
  fn_vars (ifg_trigger_body version) = [] /\
  fn_body (ifg_trigger_body version) =
    Ssequence (Sset IFG._val04 (Econst_int Int.one tint))
      (Ssequence (ifg_pending_gate version) (ifg_return_tail version)) /\
  ifg_pending_gate version =
    Ssequence (Sset IFG._t'7 (Evar IFG._sDelayedWarpOp tshort))
      (Sifthenelse ifg_pending_guard (ifg_schedule_branch version) Sskip) /\
  ifg_return_tail version =
    Ssequence (Sset IFG._t'6 (Evar IFG._sDelayedWarpTimer tshort))
      (Sreturn (Some (Etempvar IFG._t'6 tshort))).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ifg_short_global_value : forall (ge : genv) le m id cell word answer,
  Genv.find_symbol ge id = Some cell ->
  Mem.load Mint16signed m cell 0 = Some (Vint word) ->
  eval_expr ge empty_env le m (Evar id tshort) answer ->
  answer = Vint word.
Proof.
  intros ge le m id cell word answer Hsymbol Hload Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    inversion Hl; subst end; try discriminate.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  match goal with Hread : Mem.loadv _ _ (Vptr ?loc _) = Some _ |- _ =>
    assert (loc = cell) by congruence; subst loc;
    change (Mem.load Mint16signed m cell 0 = Some answer) in Hread;
    congruence end.
Qed.

Lemma ifg_nonzero_pending_disables_guard : forall ge e le m pending answer,
  le ! IFG._t'7 = Some (Vint pending) ->
  pending <> Int.zero ->
  eval_expr ge e le m ifg_pending_guard answer -> answer = Vint Int.zero.
Proof.
  intros ge e le m pending answer Htemp Hnonzero Hr.
  unfold ifg_pending_guard in Hr. inversion Hr; subst.
  2: match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ =>
    inversion Hbad end.
  match goal with Hread : eval_expr _ _ _ _ (Etempvar IFG._t'7 _) ?v |- _ =>
    assert (v = Vint pending) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hconst : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hconst; subst end.
  pose proof (Int.eq_false _ _ Hnonzero) as Hneq.
  match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    change (Some (Val.of_bool (Int.eq pending Int.zero)) = Some answer) in Hsem;
    rewrite Hneq in Hsem; inversion Hsem; reflexivity end.
Qed.

Theorem ifg_live_pending_guard_skips_schedule :
  forall version (ge : genv) le m cell pending t le' after out,
  Genv.find_symbol ge IFG._sDelayedWarpOp = Some cell ->
  Mem.load Mint16signed m cell 0 = Some (Vint pending) ->
  pending <> Int.zero ->
  ocn_exec ge empty_env le m (ifg_pending_gate version) t le' after out ->
  t = E0 /\ le' = PTree.set IFG._t'7 (Vint pending) le /\
  after = m /\ out = Out_normal.
Proof.
  intros version ge le m cell pending t le' after out Hsymbol Hload Hnonzero Hrun.
  destruct (ifg_actual_source version) as (_ & _ & Hgate & _).
  rewrite Hgate in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IFG._t'7 (Evar IFG._sDelayedWarpOp tshort))
    _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hbranch).
  inversion Hread; subst; clear Hread.
  match goal with Hr : eval_expr _ _ _ _ (Evar IFG._sDelayedWarpOp _) ?v |- _ =>
    assert (v = Vint pending) by (eapply ifg_short_global_value; eauto); subst v end.
  inversion Hbranch; subst; clear Hbranch.
  match goal with Hr : eval_expr _ _ _ _ ifg_pending_guard ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ifg_nonzero_pending_disables_guard;
      [apply PTree.gss|exact Hnonzero|exact Hr]); subst v end.
  match goal with Hb : bool_val (Vint Int.zero) _ _ = Some ?choice |- _ =>
    change (Some false = Some choice) in Hb; inversion Hb; subst end.
  cbn beta iota in *.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
    inversion Hr; subst end.
  repeat split; reflexivity.
Qed.

Theorem ifg_completed_pending_trigger_body_preserves_memory :
  forall version (ge : genv) le m cell pending t le' after out,
  Genv.find_symbol ge IFG._sDelayedWarpOp = Some cell ->
  Mem.load Mint16signed m cell 0 = Some (Vint pending) ->
  pending <> Int.zero ->
  ocn_exec ge empty_env le m (fn_body (ifg_trigger_body version)) t le' after out ->
  t = E0 /\ after = m.
Proof.
  intros version ge le m cell pending t le' after out Hsymbol Hload Hnonzero Hrun.
  destruct (ifg_actual_source version) as (_ & Hbody & _ & Htail).
  rewrite Hbody in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IFG._val04 (Econst_int Int.one tint))
    _ _ _ _ _ eq_refl Hrun)
    as (ready & ready_m & init_t & rest_t & Htrace & Hinit & Hrest).
  inversion Hinit; subst; clear Hinit.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  inversion Hrest; subst; clear Hrest.
  all: match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (ifg_pending_gate ?current_version) _ _ _ _ |- _ =>
    destruct (ifg_live_pending_guard_skips_schedule current_version _ _ _ _ _ _ _ _ _
      Hsymbol Hload Hnonzero Hg) as (-> & -> & -> & Hout); try contradiction end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (ifg_return_tail _) _ _ _ _ |- _ =>
    rewrite Htail in Hrun; inversion Hrun; subst; clear Hrun end.
  all: match goal with Hread : ClightBigstep.exec_stmt _ _ _ _ _ (Sset IFG._t'6 _) _ _ _ _ |- _ =>
    inversion Hread; subst; clear Hread end.
  all: try contradiction.
  match goal with Hreturn : ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn _) _ _ _ _ |- _ =>
    inversion Hreturn; subst end.
  split; reflexivity.
Qed.

Definition InkPendingWarpActualCallFrame : Prop :=
  forall version (ge : genv) m cell pending args t after result,
  Genv.find_symbol ge IFG._sDelayedWarpOp = Some cell ->
  Mem.load Mint16signed m cell 0 = Some (Vint pending) ->
  pending <> Int.zero ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (ifg_trigger_body version))
    args t after result -> t = E0 /\ after = m.

Theorem ifg_pending_operation_blocks_actual_trigger_call : InkPendingWarpActualCallFrame.
Proof.
  intros version ge m cell pending args t after result Hsymbol Hload Hnonzero Hcall.
  destruct (ifg_actual_source version) as (Hvars & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (ifg_completed_pending_trigger_body_preserves_memory version ge _ _ cell pending
      _ _ _ _ Hsymbol Hload Hnonzero Hr) as (-> & ->) end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  split; reflexivity.
Qed.

(** The source constants are DEATH=18, GAME_OVER=20 and OBJECT=4. The same
    guard excludes replacement by ANY requested operation, including 4. *)
Theorem ifg_pending_death_or_game_over_blocks_object_warp :
  forall version (ge : genv) m cell mario pending t after result,
  Genv.find_symbol ge IFG._sDelayedWarpOp = Some cell ->
  Mem.load Mint16signed m cell 0 = Some (Vint pending) ->
  (pending = Int.repr 18 \/ pending = Int.repr 20) ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (ifg_trigger_body version))
    [mario; Vint (Int.repr 4)] t after result -> t = E0 /\ after = m.
Proof.
  intros version ge m cell mario pending t after result Hsymbol Hload Hfatal Hcall.
  eapply ifg_pending_operation_blocks_actual_trigger_call; eauto.
  destruct Hfatal as [Hdeath | Hgame]; subst pending; discriminate.
Qed.
