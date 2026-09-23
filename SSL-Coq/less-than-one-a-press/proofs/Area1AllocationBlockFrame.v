(** Block separation for the allocator's real initialization. Pointer
    temporaries may move within a block; this deliberately does NOT prove
    separation between two slots of the same Object-pool block. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop Ctypes
 Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import InkPlatformWriteFrame ObjectContactNecessity.
Import ListNotations.
Import Clightdefs.ClightNotations.

Fixpoint pab_safe_expr temps a := match a with
| Ecast a _ => pab_safe_expr temps a
| Ebinop Oadd a b _ => match classify_add (typeof a) (typeof b) with
   | add_case_pi _ _ => pab_safe_expr temps a | _ => false end
| _ => match fst (ipw_roots a) with
       | Some (IPWtemp id) => ipw_member id temps | _ => false end end.
Definition pab_temps le ob temps := forall id b ofs,
 In id temps -> le ! id = Some (Vptr b ofs) -> b <> ob.

Lemma pab_expr_safe : forall a temps ge e le m ob v,
 pab_safe_expr temps a = true -> pab_temps le ob temps ->
 eval_expr ge e le m a v -> ipw_value_safe ob v.
Proof.
 induction a; intros temps ge e le m ob v Hshape Hctx Hread;
   try solve [cbn [pab_safe_expr ipw_roots fst] in Hshape; discriminate].
 all: try solve [cbn [pab_safe_expr] in Hshape;
   destruct (fst (ipw_roots _)) as [[id|id]|] eqn:Hr; try discriminate;
   apply ipw_member_spec in Hshape; intros b ofs E;
   eapply (proj1 (ipw_root_sound ge e le m)); [exact Hread|exact Hr| |exact E];
   intros b' ofs' Ht; eapply Hctx; eauto].
 - destruct b; try solve [cbn [pab_safe_expr ipw_roots fst] in Hshape; discriminate].
   cbn [pab_safe_expr] in Hshape.
   destruct (classify_add (typeof a1) (typeof a2)) eqn:Hclass; try discriminate.
   inversion Hread; subst.
   + intros b ofs E. subst v.
     match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some (Vptr b ofs) |- _ =>
       destruct (ipw_add_preserves_block _ _ _ _ _ _ _ _ _ Hclass Hsem _ _ eq_refl) as [off Heq] end.
     eapply IHa1; eauto.
   + match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
 - cbn [pab_safe_expr] in Hshape. inversion Hread; subst.
   + intros b ofs E. subst v.
     match goal with Hcast : sem_cast _ _ _ _ = Some (Vptr b ofs) |- _ =>
       pose proof (ipw_cast_keeps_block _ _ _ _ _ _ Hcast) as E end.
     eapply IHa; eauto.
   + match goal with Hl : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Definition pab_write temps lhs :=
 (match access_mode (typeof lhs) with By_value _ => true | _ => false end) &&
 (match snd (ipw_roots lhs) with Some (IPWtemp id) => ipw_member id temps | _ => false end).

Lemma pab_write_frame : forall ge e le m lhs rhs t le' after out ob temps,
 pab_write temps lhs = true -> pab_temps le ob temps ->
 ocn_exec ge e le m (Sassign lhs rhs) t le' after out -> ipw_frame ob m after.
Proof.
 intros ge e le m lhs rhs t le' after out ob temps Hshape Hctx Hrun.
 unfold pab_write in Hshape. apply andb_true_iff in Hshape as [Hmode Hroot].
 destruct (snd (ipw_roots lhs)) as [[id|id]|] eqn:Hr; try discriminate.
 apply ipw_member_spec in Hroot. inversion Hrun; subst.
 match goal with Hl : eval_lvalue _ _ _ _ _ ?b _ _ |- _ =>
   assert (b <> ob) as Hdifferent by
     (eapply (proj2 (ipw_root_sound _ _ _ _)); [exact Hl|exact Hr|];
      intros b' ofs' Ht; eapply Hctx; eauto) end.
 match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
 - intros observed observed_offset. eapply Mem.load_store_other; [eassumption|left; congruence].
 - match goal with Hbad : access_mode _ = By_copy |- _ => rewrite Hbad in Hmode; discriminate end.
 - match goal with Hb : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hb; subst end.
   intros observed observed_offset. eapply Mem.load_store_other; [eassumption|left; congruence].
Qed.

Fixpoint pab_shape temps (call_ok : expr -> list expr -> bool) s := match s with
| Sskip | Sbreak | Scontinue | Sreturn _ => true
| Sset id a => if ipw_member id temps then pab_safe_expr temps a else true
| Sassign lhs _ => pab_write temps lhs
| Scall None fn args => call_ok fn args
| Ssequence a b | Sifthenelse _ a b | Sloop a b => pab_shape temps call_ok a && pab_shape temps call_ok b
| _ => false end.

Lemma pab_set_temps : forall le ob temps id v,
 pab_temps le ob temps ->
 (In id temps -> ipw_value_safe ob v) -> pab_temps (PTree.set id v le) ob temps.
Proof.
 intros le ob temps id v Hctx Hv j b ofs Hj Hread.
 rewrite PTree.gsspec in Hread. destruct (peq j id) as [->|Hne].
 - inversion Hread; subst. eapply Hv; eauto.
 - eapply Hctx; eauto.
Qed.

Theorem pab_checked_frame : forall ge e ob temps call_ok,
 (forall le m fn args t le' after out,
  pab_temps le ob temps -> call_ok fn args = true ->
  ocn_exec ge e le m (Scall None fn args) t le' after out -> ipw_frame ob m after) ->
 forall le m s t le' after out,
 ocn_exec ge e le m s t le' after out ->
 pab_shape temps call_ok s = true -> pab_temps le ob temps ->
 ipw_frame ob m after /\ pab_temps le' ob temps.
Proof.
 intros ge e ob temps call_ok Hcall le m s t le' after out Hrun.
 unfold ipw_frame in *.
 induction Hrun; cbn [pab_shape]; intros Hshape Hctx; try discriminate;
   try solve [split; [intros chunk ofs; reflexivity|exact Hctx]].
 - split; [eapply pab_write_frame; eauto; econstructor; eauto|exact Hctx].
 - split; [intros chunk ofs; reflexivity|]. apply pab_set_temps; [exact Hctx|].
   intros Hid. assert (ipw_member id temps = true) as Hmember by (apply ipw_member_spec; exact Hid).
   rewrite Hmember in Hshape. eapply pab_expr_safe; eauto.
 - destruct optid; try discriminate. split; [eapply Hcall; eauto; econstructor; eauto|exact Hctx].
 - apply andb_true_iff in Hshape as [Ha Hb].
   destruct (IHHrun1 Hcall Ha Hctx) as [Hf1 Hc1].
   destruct (IHHrun2 Hcall Hb Hc1) as [Hf2 Hc2].
   split; [intros; rewrite Hf2, Hf1; reflexivity|exact Hc2].
 - apply andb_true_iff in Hshape as [Ha Hb]. eauto.
 - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; eauto.
 - apply andb_true_iff in Hshape as [Ha Hb]. eauto.
 - apply andb_true_iff in Hshape as [Ha Hb].
   destruct (IHHrun1 Hcall Ha Hctx) as [Hf1 Hc1].
   destruct (IHHrun2 Hcall Hb Hc1) as [Hf2 Hc2].
   split; [intros; rewrite Hf2, Hf1; reflexivity|exact Hc2].
 - apply andb_true_iff in Hshape as [Ha Hb].
   destruct (IHHrun1 Hcall Ha Hctx) as [Hf1 Hc1].
   destruct (IHHrun2 Hcall Hb Hc1) as [Hf2 Hc2].
   destruct (IHHrun3 Hcall (andb_true_intro (conj Ha Hb)) Hc2) as [Hf3 Hc3].
   split; [intros; rewrite Hf3, Hf2, Hf1; reflexivity|exact Hc3].
Qed.
