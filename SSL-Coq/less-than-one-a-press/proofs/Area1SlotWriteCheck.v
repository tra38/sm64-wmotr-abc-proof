(** Bounded symbolic execution of write footprints. This checks the actual
    statements and loop tests, without reading or replacing game memory. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop Ctypes
 Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import Area1SlotExpressions
 OrdinaryArea1EntryMemory EyerokRank15LiveMovement ObjectContactNecessity.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition asw_outside (ob : block) slot chunk b ofs :=
 b <> ob \/ ofs + size_chunk chunk <= object_slot_offset slot \/
 object_slot_offset slot + object_size <= ofs.
Definition asw_frame ob slot before after := forall chunk b ofs,
 asw_outside ob slot chunk b ofs ->
 Mem.load chunk after b ofs = Mem.load chunk before b ofs.
Lemma asw_refl : forall ob slot m, asw_frame ob slot m m.
Proof. intros; intros chunk b ofs H; reflexivity. Qed.
Lemma asw_trans : forall ob slot a b c,
 asw_frame ob slot a b -> asw_frame ob slot b c -> asw_frame ob slot a c.
Proof. intros ob slot a b c H1 H2 chunk loc ofs H; rewrite H2,H1; auto. Qed.

Lemma ase_get_remove : forall id other ae,
 ase_get other (ase_remove id ae) =
 if Pos.eqb other id then None else ase_get other ae.
Proof.
 intros id other ae; unfold ase_remove; induction ae as [|[j v] rest IH]; cbn [filter ase_get fst].
 - destruct (Pos.eqb other id); reflexivity.
 - destruct (Pos.eqb id j) eqn:E; cbn.
   + apply Pos.eqb_eq in E; subst. rewrite IH.
     destruct (Pos.eqb other j); reflexivity.
   + destruct (Pos.eqb other j) eqn:F.
     * apply Pos.eqb_eq in F; subst. assert (Pos.eqb j id = false) by
         (apply Pos.eqb_neq; apply Pos.eqb_neq in E; congruence).
       rewrite H. reflexivity.
     * rewrite IH. destruct (Pos.eqb other id); reflexivity.
Qed.
Lemma ase_put_context : forall ob base ae le id value known,
 ase_context ob base ae le ->
 (forall x, known = Some x -> value = ase_denote ob base x) ->
 ase_context ob base (ase_put id known ae) (PTree.set id value le).
Proof.
 intros ob base ae le id value known Hctx Hv j x Hget.
 destruct known; cbn [ase_put ase_get] in Hget.
 - destruct (Pos.eqb j id) eqn:E.
   + apply Pos.eqb_eq in E; subst. inversion Hget; subst. rewrite PTree.gss. f_equal. auto.
   + rewrite ase_get_remove,E in Hget. rewrite PTree.gso; [apply Hctx; auto|].
     apply Pos.eqb_neq in E; congruence.
 - rewrite ase_get_remove in Hget. destruct (Pos.eqb j id) eqn:E; try discriminate.
   rewrite PTree.gso; [apply Hctx; auto|]. apply Pos.eqb_neq in E; congruence.
Qed.

Definition asw_write ce ae lhs := match access_mode (typeof lhs),snd (ase_eval ce ae lhs) with
| By_value chunk, Some delta =>
  Z.leb (Ptrofs.unsigned delta + size_chunk chunk) object_size
| _,_ => false end.
Lemma asw_slot_address : forall slot delta,
 (slot < object_pool_capacity)%nat -> 0 <= delta <= object_size ->
 Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr delta)) =
 object_slot_offset slot + delta.
Proof.
 intros slot delta Hslot Hdelta.
 pose proof (rank15_pool_slot_offset_in_pointer_range _ Hslot) as Hrange.
 unfold Ptrofs.add.
 rewrite (Ptrofs.unsigned_repr (object_slot_offset slot)) by (unfold object_size in Hrange; lia).
 rewrite (Ptrofs.unsigned_repr delta) by (change (0 <= delta <= 4294967295); unfold object_size in *; lia).
 apply Ptrofs.unsigned_repr. unfold object_size in *. lia.
Qed.
Lemma asw_actual_write : forall (ge : genv) e le m lhs rhs ob slot ae t le' after out,
 (slot < object_pool_capacity)%nat ->
 ase_context ob (Ptrofs.repr (object_slot_offset slot)) ae le ->
 asw_write ge ae lhs = true ->
 ocn_exec ge e le m (Sassign lhs rhs) t le' after out ->
 asw_frame ob slot m after.
Proof.
 intros ge e le m lhs rhs ob slot ae t le' after out Hslot Hctx Hcheck Hrun.
 unfold asw_write in Hcheck.
 destruct (access_mode (typeof lhs)) eqn:Hmode; try discriminate.
 destruct (snd (ase_eval ge ae lhs)) eqn:E; try discriminate.
 apply Z.leb_le in Hcheck.
 inversion Hrun; subst.
 match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
   destruct ((proj2 (ase_eval_sound _ _ _ _ _ _ _ Hctx)) _ _ _ _ Hl _ E)
     as (-> & -> & ->) end.
 match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
 - match goal with Hmode' : access_mode _ = By_value _ |- _ =>
     rewrite Hmode in Hmode'; inversion Hmode'; subst end.
   pose proof (Ptrofs.unsigned_range i) as Hnonnegative.
   match goal with Hstore : Mem.storev ?written _ _ _ = Some _ |- _ =>
     cbn [Mem.storev] in Hstore;
     rewrite <- (Ptrofs.repr_unsigned i) in Hstore;
     rewrite asw_slot_address in Hstore by
       (auto; pose proof (Ptrofs.unsigned_range i); pose proof (size_chunk_pos written); lia);
     intros observed b ofs Hout; eapply Mem.load_store_other; [exact Hstore|] end.
   destruct Hout as [Hb|[Hlo|Hhi]]; [left; exact Hb|right; left; lia|right; right; lia].
 - congruence.
Qed.

Inductive asw_exit := ASWnormal | ASWbreak | ASWreturn.
Definition asw_matches k out := match k with
| ASWnormal => out = Out_normal | ASWbreak => out = Out_break
| ASWreturn => exists v, out = Out_return v end.
Definition asw_value_eq_dec (a b : ase_value) : {a=b}+{a<>b}.
Proof. decide equality; first [apply Ptrofs.eq_dec|apply Int.eq_dec]. Defined.
Definition asw_env_eq_dec (a b : ase_env) : {a=b}+{a<>b}.
Proof. apply list_eq_dec. decide equality; first [apply asw_value_eq_dec|apply Pos.eq_dec]. Defined.
Definition asw_exit_eq_dec (a b : asw_exit) : {a=b}+{a<>b}.
Proof. decide equality. Defined.
Definition asw_result_eq_dec (a b : ase_env * asw_exit) : {a=b}+{a<>b}.
Proof. decide equality; first [apply asw_exit_eq_dec|apply asw_env_eq_dec]. Defined.
Definition asw_test ce ae a := match fst (ase_eval ce ae a) with
| Some (ASEint i) => if type_eq (typeof a) tint then Some (negb (Int.eq i Int.zero)) else None
| _ => None end.

Fixpoint asw_check fuel ce (call_ok : ase_env -> expr -> list expr -> bool) ae s :=
 match fuel with O => None | S fuel' =>
 match s with
 | Sskip => Some (ae,ASWnormal)
 | Sbreak => Some (ae,ASWbreak)
 | Sreturn _ => Some (ae,ASWreturn)
 | Sset id a => Some (ase_put id (fst (ase_eval ce ae a)) ae,ASWnormal)
 | Sassign lhs _ => if asw_write ce ae lhs then Some (ae,ASWnormal) else None
 | Scall None fn args => if call_ok ae fn args then Some (ae,ASWnormal) else None
 | Ssequence a b =>
   match asw_check fuel' ce call_ok ae a with
   | Some (next,ASWnormal) => asw_check fuel' ce call_ok next b
   | result => result end
 | Sifthenelse a yes no =>
   match asw_test ce ae a with
   | Some test => asw_check fuel' ce call_ok ae (if test then yes else no)
   | None => match asw_check fuel' ce call_ok ae yes,asw_check fuel' ce call_ok ae no with
      | Some x,Some y => if asw_result_eq_dec x y then Some x else None
      | _,_ => None end end
 | Sloop body incr =>
   match asw_check fuel' ce call_ok ae body with
   | Some (next,ASWbreak) => Some (next,ASWnormal)
   | Some (next,ASWreturn) => Some (next,ASWreturn)
   | Some (next,ASWnormal) =>
     match asw_check fuel' ce call_ok next incr with
     | Some (last,ASWnormal) => asw_check fuel' ce call_ok last (Sloop body incr)
     | _ => None end
   | None => None end
 | _ => None end end.

Lemma asw_test_sound : forall (ge : genv) e le m ob base ae a test v choice,
 ase_context ob base ae le -> asw_test ge ae a = Some test ->
 eval_expr ge e le m a v -> bool_val v (typeof a) m = Some choice -> choice = test.
Proof.
 intros ge e le m ob base ae a test v choice Hctx Hcheck Hread Hbool.
 unfold asw_test in Hcheck.
 destruct (fst (ase_eval ge ae a)) as [[i|ofs]|] eqn:E; try discriminate.
 destruct (type_eq (typeof a) tint); try discriminate.
 inversion Hcheck; subst. rewrite (proj1 (ase_eval_sound _ _ _ _ _ _ _ Hctx) _ _ Hread _ E) in Hbool.
 rewrite e0 in Hbool.
 change (Some (negb (Int.eq i Int.zero)) = Some choice) in Hbool. congruence.
Qed.

Theorem asw_check_sound : forall (ge : genv) e ob slot call_ok,
 (slot < object_pool_capacity)%nat ->
 (forall ae le m fn args t le' after out,
   ase_context ob (Ptrofs.repr (object_slot_offset slot)) ae le ->
   call_ok ae fn args = true ->
   ocn_exec ge e le m (Scall None fn args) t le' after out -> asw_frame ob slot m after) ->
 forall le m s t le' after out,
 ocn_exec ge e le m s t le' after out ->
 forall fuel ae last kind,
 asw_check fuel ge call_ok ae s = Some (last,kind) ->
 ase_context ob (Ptrofs.repr (object_slot_offset slot)) ae le ->
 asw_frame ob slot m after /\
 ase_context ob (Ptrofs.repr (object_slot_offset slot)) last le' /\ asw_matches kind out.
Proof.
 intros ge e ob slot call_ok Hslot Hcall le m s t le' after out Hrun.
 induction Hrun; intros fuel ae last kind Hcheck Hctx;
 destruct fuel; cbn [asw_check] in Hcheck; try discriminate.
 - inversion Hcheck; subst; cbn [asw_matches]. split; [apply asw_refl|auto].
 - destruct (asw_write ge ae a1) eqn:E; try discriminate. inversion Hcheck; subst; cbn [asw_matches].
   split; [eapply asw_actual_write; eauto; econstructor; eauto|auto].
 - inversion Hcheck; subst; cbn [asw_matches]. split; [apply asw_refl|]. split; [|reflexivity].
   eapply ase_put_context; [exact Hctx|]. intros x E.
   eapply (proj1 (ase_eval_sound _ _ _ _ _ _ _ Hctx)); eauto.
 - destruct optid; try discriminate. destruct (call_ok ae a al) eqn:E; try discriminate.
   inversion Hcheck; subst; cbn [asw_matches]. split; [eapply Hcall; eauto; econstructor; eauto|auto].
 - destruct (asw_check fuel ge call_ok ae s1) as [[middle how]|] eqn:E; try discriminate.
   destruct (IHHrun1 Hcall _ _ _ _ E Hctx) as (Hf & Hc & Ho).
   destruct how; cbn [asw_matches] in Ho.
   2: discriminate.
   2: destruct Ho as [v Ebad]; discriminate.
   destruct (IHHrun2 Hcall _ _ _ _ Hcheck Hc) as (Hf2 & Hc2 & Ho2).
   split; [eapply asw_trans; eauto|auto].
 - destruct (asw_check fuel ge call_ok ae s1) as [[middle how]|] eqn:E; try discriminate.
   destruct (IHHrun Hcall _ _ _ _ E Hctx) as (Hf & Hc & Ho).
   destruct how; [contradiction|inversion Hcheck; subst; auto|inversion Hcheck; subst; auto].
 - destruct (asw_test ge ae a) eqn:E.
   + assert (b = b0) as -> by (eapply asw_test_sound; eauto).
     eapply IHHrun; eauto.
   + destruct (asw_check fuel ge call_ok ae s1) as [[yes ky]|] eqn:Ey; try discriminate.
     destruct (asw_check fuel ge call_ok ae s2) as [[no kn]|] eqn:En; try discriminate.
     destruct (asw_result_eq_dec (yes,ky) (no,kn)); try discriminate.
     inversion e0; subst. inversion Hcheck; subst; cbn [asw_matches]. destruct b; eapply IHHrun; eauto.
 - inversion Hcheck; subst; cbn [asw_matches]. split; [apply asw_refl|]. split; [exact Hctx|eexists; reflexivity].
 - inversion Hcheck; subst; cbn [asw_matches]. split; [apply asw_refl|]. split; [exact Hctx|eexists; reflexivity].
 - inversion Hcheck; subst; cbn [asw_matches]. split; [apply asw_refl|auto].
 - destruct (asw_check fuel ge call_ok ae s1) as [[middle how]|] eqn:E; try discriminate.
   destruct (IHHrun Hcall _ _ _ _ E Hctx) as (Hf & Hc & Ho).
   destruct how; cbn [asw_matches] in Ho.
   + subst. first [solve [match goal with Hexit : out_normal_or_continue _ |- _ => inversion Hexit end] | solve [match goal with Hexit : out_break_or_return _ _ |- _ => inversion Hexit end]].
   + subst. match goal with Hexit : out_break_or_return _ _ |- _ => inversion Hexit; subst end. inversion Hcheck; subst; cbn [asw_matches]. split; [exact Hf|auto].
   + destruct Ho as [v ->]. match goal with Hexit : out_break_or_return _ _ |- _ => inversion Hexit; subst end. inversion Hcheck; subst; cbn [asw_matches].
     split; [exact Hf|]. split; [exact Hc|eexists; reflexivity].
 - destruct (asw_check fuel ge call_ok ae s1) as [[middle how]|] eqn:E; try discriminate.
   destruct (IHHrun1 Hcall _ _ _ _ E Hctx) as (Hf & Hc & Ho).
   destruct how; cbn [asw_matches] in Ho.
   + destruct (asw_check fuel ge call_ok middle s2) as [[next how]|] eqn:E2; try discriminate.
     destruct how; try discriminate.
     destruct (IHHrun2 Hcall _ _ _ _ E2 Hc) as (_ & _ & Ho2).
     cbn [asw_matches] in Ho2. subst. match goal with Hexit : out_break_or_return _ _ |- _ => inversion Hexit end.
   + subst. first [solve [match goal with Hexit : out_normal_or_continue _ |- _ => inversion Hexit end] | solve [match goal with Hexit : out_break_or_return _ _ |- _ => inversion Hexit end]].
   + destruct Ho as [v ->]. match goal with Hexit : out_normal_or_continue _ |- _ => inversion Hexit end.
 - destruct (asw_check fuel ge call_ok ae s1) as [[middle how]|] eqn:E; try discriminate.
   destruct (IHHrun1 Hcall _ _ _ _ E Hctx) as (Hf & Hc & Ho).
   destruct how; cbn [asw_matches] in Ho.
   + destruct (asw_check fuel ge call_ok middle s2) as [[next how]|] eqn:E2; try discriminate.
     destruct how; try discriminate.
     destruct (IHHrun2 Hcall _ _ _ _ E2 Hc) as (Hf2 & Hc2 & Ho2).
     destruct (IHHrun3 Hcall _ _ _ _ Hcheck Hc2) as (Hf3 & Hc3 & Ho3).
     split; [eapply asw_trans; [exact Hf|eapply asw_trans; eauto]|auto].
   + subst. first [solve [match goal with Hexit : out_normal_or_continue _ |- _ => inversion Hexit end] | solve [match goal with Hexit : out_break_or_return _ _ |- _ => inversion Hexit end]].
   + destruct Ho as [v ->]. match goal with Hexit : out_normal_or_continue _ |- _ => inversion Hexit end.
Qed.
