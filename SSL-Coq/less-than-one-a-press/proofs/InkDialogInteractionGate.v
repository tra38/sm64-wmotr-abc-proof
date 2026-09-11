(** A raised display is not the whole conditional Ink setup. If the action
    still is ACT_READING_AUTOMATIC_DIALOG when the real interaction gate reads
    it, the entire handler loop is skipped, including a cached warp contact.

    This constructs the local transition through the selected US/JP body.
    It neither assumes harmless preceding calls nor proves a post-dialog
    arrival, a selected top surface, or platform retention through the warp. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes ContactConsumerSource
  InkBackwardSource InkActionPassStart InkActionPassHistory
  InkBodyResetFrame InkBodyResetConstruction ObjectContactNecessity Area2Rank12BContact
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition idg_body version := ccs_body version CCStarDispatch.
Definition idg_frontier version := rank12b_drop_sequences 2 (fn_body (idg_body version)).
Definition idg_gate version := ibk_head (idg_frontier version).
Definition idg_after version := rank12b_drop_sequences 1 (idg_frontier version).
Definition idg_contacts version := match idg_gate version with
| Ssequence (Ssequence _ (Sifthenelse _ yes _)) _ => yes
| _ => Sskip end.
Definition idg_handlers version := match idg_gate version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.

Definition idg_action := ibr_field CCI._m CCI._MarioState CCI._action tuint.
Definition idg_tangible := Eunop Onotbool
  (Ebinop Oand (Etempvar CCI._t'18 tuint)
    (Ebinop Oshl (Econst_int (Int.repr 1) tint)
      (Econst_int (Int.repr 12) tint) tint) tuint) tint.
Definition idg_dialog_action := Int.repr 536875781. (* 0x20001305 *)
Definition idg_read_temps le := PTree.set CCI._t'18 (Vint idg_dialog_action) le.
Definition idg_after_temps le := PTree.set CCI._t'4 (Vint Int.zero) (idg_read_temps le).

(** Extract the actual guarded loop rather than providing a substitute body. *)
Lemma idg_source : forall version,
  idg_frontier version = Ssequence (idg_gate version) (idg_after version) /\
  idg_gate version = Ssequence
    (Ssequence (Sset CCI._t'18 idg_action)
      (Sifthenelse idg_tangible (idg_contacts version)
        (Sset CCI._t'4 (Econst_int Int.zero tint))))
    (Sifthenelse (Etempvar CCI._t'4 tint) (idg_handlers version) Sskip).
Proof. intros []; split; reflexivity. Qed.

Lemma idg_dialog_guard_is_false : forall ge e le m,
  eval_expr ge e (idg_read_temps le) m idg_tangible (Vint Int.zero).
Proof.
  intros. unfold idg_tangible.
  eapply eval_Eunop with (v1 := Vint (Int.repr 4096)).
  - eapply eval_Ebinop with (v1 := Vint idg_dialog_action) (v2 := Vint (Int.repr 4096)).
    + apply eval_Etempvar. apply PTree.gss.
    + eapply eval_Ebinop; [constructor|constructor|reflexivity].
    + reflexivity.
  - reflexivity.
Qed.

Lemma idg_construct_skipped_handlers : forall version e le m mb,
  le ! CCI._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 12 = Some (Vint idg_dialog_action) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (idg_gate version) E0 (idg_after_temps le) m Out_normal.
Proof.
  intros version e le m mb Hm Haction.
  rewrite (proj2 (idg_source version)).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := idg_after_temps le) (m1 := m).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := idg_read_temps le) (m1 := m).
    + apply exec_Sset. eapply ibc_field_read with (delta := 12) (chunk := Mint32);
        [exact Hm|exact (ias_selected_action_field version)|reflexivity|exact Haction].
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      * apply idg_dialog_guard_is_false.
      * reflexivity.
      * apply exec_Sset. constructor.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + apply eval_Etempvar. apply PTree.gss.
    + reflexivity.
    + apply exec_Sskip.
Qed.

Definition InkDialogInteractionGateBoundary : Prop :=
  forall version e le m mb k,
  le ! CCI._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 12 = Some (Vint idg_dialog_action) ->
  (exists fb,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      CCI._mario_process_interactions = Some fb /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb =
      Some (Internal (idg_body version))) /\
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (idg_body version) (idg_frontier version) k e le m) E0
    (State (idg_body version) (idg_after version) k e (idg_after_temps le) m).

Theorem idg_automatic_dialog_skips_handler_loop : InkDialogInteractionGateBoundary.
Proof.
  intros version e le m mb k Hm Haction. split.
  - exact (ccs_selected_consumer_resolves version CCStarDispatch).
  - rewrite (proj1 (idg_source version)).
    eapply star_left; [apply step_seq| |reflexivity].
    eapply star_trans.
    + eapply iap_normal_statement_steps. eapply idg_construct_skipped_handlers; eauto.
    + apply star_one. apply step_skip_seq.
    + reflexivity.
Qed.
