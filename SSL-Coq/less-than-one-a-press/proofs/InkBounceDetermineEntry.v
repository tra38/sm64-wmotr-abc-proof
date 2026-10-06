(** The completed generated interaction classifier supplies its own height
    guard.  Earlier angle calls may change memory; this proof uses the actual
    memory after them.  It does not assume that a saved guard read survives
    an arbitrary caller or that every earlier action starts synchronized. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBounceApproachGap
  InkBounceProducerEffect InkFloorResetSource InkFloorResetExecution InkBackwardSource InkBackwardExecution
  ObjectContactNecessity ObjectContactReadback ContactConsumerExecution
  Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ibde_not_above (le : temp_env) :=
  le ! BAG._interaction <> Some (Vint (Int.repr 64)).

(** A checked constant-only writer inventory. Callees may change memory but
    cannot modify this caller temporary unless it is their result target. *)
Definition ibde_literal (a : expr) : option int := match a with
| Econst_int n _ => Some n
| Ebinop Oshl (Econst_int n t1) (Econst_int k t2) _ =>
    if type_eq t1 tint then if type_eq t2 tint then
      Some (Int.shl n k) else None else None
| _ => None end.
Definition ibde_safe_literal a := match ibde_literal a with
| Some n => negb (Int.eq n (Int.repr 64)) | None => false end.
Fixpoint ibde_no_above_writer (s : statement) : bool := match s with
| Sskip | Sassign _ _ | Sreturn _ => true
| Sset id a => if Pos.eqb id BAG._interaction then ibde_safe_literal a else true
| Scall None _ _ => true
| Scall (Some id) _ _ => negb (Pos.eqb id BAG._interaction)
| Ssequence a b | Sifthenelse _ a b =>
    ibde_no_above_writer a && ibde_no_above_writer b
| _ => false end.

Lemma ibde_literal_read : forall ge e le m a n v,
  ibde_literal a = Some n -> eval_expr ge e le m a v -> v = Vint n.
Proof.
  intros ge e le m a n v Hliteral Hread.
  destruct a; cbn in Hliteral; try discriminate.
  - inversion Hliteral; subst. eapply ocn_const_int_value; eauto.
  - destruct b; try discriminate. destruct a1; try discriminate.
    destruct a2; try discriminate.
    destruct (type_eq t0 tint); try discriminate.
    destruct (type_eq t1 tint); try discriminate. subst t0 t1.
    inversion Hliteral; subst. inversion Hread; subst.
    + repeat match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
        apply ocn_const_int_value in H; subst end.
      match goal with H : sem_binary_operation _ Oshl _ _ _ _ _ = Some _ |- _ =>
        rename H into Hshift end.
      change ((if Int.ltu i0 Int.iwordsize then Some (Vint (Int.shl i i0))
        else None) = Some v) in Hshift.
      destruct (Int.ltu i0 Int.iwordsize); inversion Hshift; reflexivity.
    + match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ =>
        inversion H end.
Qed.

Lemma ibde_no_above_writer_preserves : forall ge e le m s t le' m' out,
  ocn_exec ge e le m s t le' m' out ->
  ibde_no_above_writer s = true -> ibde_not_above le -> ibde_not_above le'.
Proof.
  intros ge e le m s t le' m' out Hrun.
  induction Hrun; cbn; intros Hshape Hnot; try discriminate; try exact Hnot.
  - destruct (Pos.eqb id BAG._interaction) eqn:Hid.
    + apply Pos.eqb_eq in Hid. subst id.
      unfold ibde_safe_literal in Hshape.
      destruct (ibde_literal a) eqn:Hliteral; try discriminate.
      apply negb_true_iff in Hshape.
      pose proof (Int.eq_spec i (Int.repr 64)) as Hneq. rewrite Hshape in Hneq.
      assert (v = Vint i) by (eapply ibde_literal_read; eauto). subst v.
      unfold ibde_not_above. rewrite PTree.gss. congruence.
    + apply Pos.eqb_neq in Hid. unfold ibde_not_above in *.
      rewrite PTree.gso by congruence. exact Hnot.
  - destruct optid; cbn in Hshape; [|exact Hnot].
    apply negb_true_iff in Hshape.
    change (Pos.eqb i BAG._interaction = false) in Hshape.
    apply Pos.eqb_neq in Hshape.
    cbn [set_opttemp].
    unfold ibde_not_above in *. rewrite PTree.gso by congruence. exact Hnot.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; auto.
Qed.

Definition ibde_prefix version := ocn_prefix_items 3 (fn_body (ibag_determine_body version)).
Definition ibde_fallback version := ibk_head
  (rank12b_drop_sequences 3 (fn_body (ibag_determine_body version))).
Definition ibde_prepare version := match ibde_fallback version with
| Ssequence prepare _ => prepare | _ => Sskip end.
Definition ibde_test version := match ibde_fallback version with
| Ssequence _ (Sifthenelse test _ _) => test
| _ => Econst_int Int.zero tint end.
Definition ibde_velocity_read version := match ibde_fallback version with
| Ssequence _ (Sifthenelse _ (Ssequence read _) _) => read | _ => Sskip end.
Definition ibde_velocity_test version := match ibde_fallback version with
| Ssequence _ (Sifthenelse _ (Ssequence _ (Sifthenelse test _ _)) _) => test
| _ => Econst_int Int.zero tint end.
Definition ibde_below version := match ibde_fallback version with
| Ssequence _ (Sifthenelse _ (Ssequence _ (Sifthenelse _ _ below)) _) => below
| _ => Sskip end.
Definition ibde_return := Sreturn (Some (Etempvar BAG._interaction tuint)).

Lemma ibde_generated_classifier_shape : forall version,
  fn_vars (ibag_determine_body version) = [] /\
  fn_params (ibag_determine_body version) =
    [(BAG._m,tptr (Tstruct BAG._MarioState noattr));
     (BAG._o,tptr (Tstruct BAG._Object noattr))] /\
  fn_return (ibag_determine_body version) = tuint /\
  fn_body (ibag_determine_body version) = ocn_prepend (ibde_prefix version)
    (Ssequence (ibde_fallback version) ibde_return) /\
  forallb ibk_normal (ibde_prefix version) = true /\
  ibde_no_above_writer (ocn_prepend (ibde_prefix version) Sskip) = true /\
  ifr_keeps_temp BAG._m (ocn_prepend (ibde_prefix version) Sskip) = true /\
  ifr_keeps_temp BAG._o (ocn_prepend (ibde_prefix version) Sskip) = true /\
  ibde_fallback version = Ssequence (ibde_prepare version)
    (Sifthenelse (ibde_test version)
      (Ssequence (ibde_velocity_read version)
        (Sifthenelse (ibde_velocity_test version)
          (ibag_above_fragment version) (ibde_below version))) Sskip) /\
  ibk_normal (ibde_fallback version) = true /\
  cce_readonly_keep BAG._m (ibde_fallback version) = true /\
  cce_readonly_keep BAG._o (ibde_fallback version) = true /\
  ibde_no_above_writer (ibde_prepare version) = true /\
  ibde_no_above_writer (ibde_velocity_read version) = true /\
  ibde_no_above_writer (ibde_below version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ibde_entry_interaction_is_undef : forall version,
  (create_undef_temps (fn_temps (ibag_determine_body version))) ! BAG._interaction =
    Some Vundef.
Proof. intros []; reflexivity. Qed.

(** The fallback contains no memory writes or calls. Any returned 64 must
    therefore have passed its actual movement > actor guard in return memory.
    An earlier angle call is not given any memory frame. *)
Theorem ibde_fallback_above_uses_return_memory : forall version e le m mb mo ob oo
    movement_y actor_y t le' m' out,
  le ! BAG._m = Some (Vptr mb mo) -> le ! BAG._o = Some (Vptr ob oo) ->
  ibde_not_above le ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibde_fallback version) t le' m' out ->
  le' ! BAG._interaction = Some (Vint (Int.repr 64)) ->
  m' = m /\ Float32.cmp Cgt movement_y actor_y = true.
Proof.
  intros version e le m mb mo ob oo movement_y actor_y t le' m' out
    Hm Ho Hnot Hmovement Hactor Hrun Hresult.
  pose proof (ibde_generated_classifier_shape version) as Hshape.
  destruct Hshape as (_ & _ & _ & _ & _ & _ & _ & _ & Hbody & _ & HkeepM & HkeepO &
    Hprepare & Hvelocity & Hbelow).
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun HkeepM) as (_ & Hmemory & _).
  split; [exact Hmemory|].
  rewrite Hbody in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (ibde_prepare version) _ _ _ _ _
    ltac:(destruct version; reflexivity) Hrun)
    as (prepare_le & prepare_m & prepare_t & rest_t & _ & Hprep & Hrest).
  clear Hrun.
  assert (HprepM : prepare_m = m) by
    (eapply (proj1 (proj2 (cce_readonly_frame _ _ _ _ _ _ _ _ _ BAG._m Hprep
      ltac:(destruct version; reflexivity))))).
  assert (HprepKeepM : prepare_le ! BAG._m = le ! BAG._m) by
    (exact (proj2 (proj2 (cce_readonly_frame _ _ _ _ _ _ _ _ _ BAG._m Hprep
      ltac:(destruct version; reflexivity))))).
  assert (HprepKeepO : prepare_le ! BAG._o = le ! BAG._o) by
    (exact (proj2 (proj2 (cce_readonly_frame _ _ _ _ _ _ _ _ _ BAG._o Hprep
      ltac:(destruct version; reflexivity))))).
  pose proof (ibde_no_above_writer_preserves _ _ _ _ _ _ _ _ _ Hprep Hprepare Hnot) as HprepNot.
  clear Hprep.
  subst prepare_m.
  inversion Hrest; subst; clear Hrest. destruct b.
  - match goal with Hvel : ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
      destruct (ibk_split_sequence _ _ _ _ (ibde_velocity_read version) _ _ _ _ _
        ltac:(destruct version; reflexivity) Hvel)
        as (velocity_le & velocity_m & velocity_t & guard_t & _ & Hread & Hguard);
      clear Hvel end.
    destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ BAG._m Hread
      ltac:(destruct version; reflexivity)) as (_ & Hvm & Hvmario).
    destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ BAG._o Hread
      ltac:(destruct version; reflexivity)) as (_ & _ & Hvactor).
    pose proof (ibde_no_above_writer_preserves _ _ _ _ _ _ _ _ _ Hread Hvelocity HprepNot)
      as HvNot. subst velocity_m.
    clear Hread.
    inversion Hguard; subst; clear Hguard. destruct b.
    + match goal with Habove : ClightBigstep.exec_stmt _ _ _ _ _ (ibag_above_fragment _) _ _ _ _ |- _ =>
        unfold ibag_above_fragment in Habove;
        cce_unroll_loop_free_exec end.
      all: try solve [unfold ibde_not_above in HvNot;
        repeat rewrite PTree.gso in Hresult by discriminate; contradiction].
      match goal with Hr : eval_expr _ ?read_env ?read_locals ?read_memory ifr_y_cell ?v |- _ =>
        assert (v = Vsingle movement_y) by
          (eapply (ibag_actual_movement_read version read_env read_locals read_memory
            mb mo movement_y v); [congruence|exact Hmovement|exact Hr]); subst v end.
      match goal with Hr : eval_expr _ ?read_env ?read_locals ?read_memory (ibp_object_y _) ?v |- _ =>
        assert (v = Vsingle actor_y) by
          (eapply (ibp_object_y_read version read_env read_locals read_memory ob oo actor_y v);
            [rewrite PTree.gso by discriminate; congruence|
            exact Hactor|exact Hr]); subst v end.
      match goal with Hexpr : eval_expr ?g ?env ?locals ?mem ibag_above_test ?v,
        Hbool : bool_val ?v _ ?mem = Some true |- _ =>
        change (bool_val v tint mem = Some true) in Hbool;
        eapply (ocn_float_test_is_the_actual_comparison g env locals mem
          BAG._t'16 BAG._t'17 true movement_y actor_y true)
      end.
      * rewrite PTree.gso by discriminate. apply PTree.gss.
      * apply PTree.gss.
      * unfold ocn_test_value, ibag_above_test. eauto.
    + match goal with HbelowRun : ClightBigstep.exec_stmt _ _ _ _ _ (ibde_below _) _ _ _ _ |- _ =>
        pose proof (ibde_no_above_writer_preserves _ _ _ _ _ _ _ _ _
          HbelowRun Hbelow HvNot) as Hno end.
      unfold ibde_not_above in Hno. contradiction.
  - match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hskip; subst end. unfold ibde_not_above in HprepNot. contradiction.
Qed.

Theorem ibde_completed_above_classifier_reads_actual_return_heights :
  forall version m mb mo ob oo movement_y actor_y t m',
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ibag_determine_body version)) [Vptr mb mo;Vptr ob oo]
    t m' (Vint (Int.repr 64)) ->
  Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  Float32.cmp Cgt movement_y actor_y = true.
Proof.
  intros version m mb mo ob oo movement_y actor_y t m' Hcall Hmovement Hactor.
  destruct (ibde_generated_classifier_shape version) as
    (Hvars & Hparams & Hreturn & Hbody & Hnormal & Hsafe & HkeepM & HkeepO &
     HfallbackShape & HfallbackNormal & HreadonlyM & HreadonlyO &
     Hprepare & Hvelocity & Hbelow).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    rewrite Hparams in Hb; cbn in Hb; inversion Hb; subst temps end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (cut_le & cut_m & pre & suffix & _ & Hprefix & Hsuffix) end.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ BAG._m Hprefix HkeepM) as Hm.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ BAG._o Hprefix HkeepO) as Ho.
  cbn in Hm, Ho. repeat rewrite PTree.gso in Hm by discriminate.
  rewrite PTree.gss in Hm. rewrite PTree.gss in Ho.
  pose proof (ibde_no_above_writer_preserves _ _ _ _ _ _ _ _ _ Hprefix Hsafe
    ltac:(unfold ibde_not_above; repeat rewrite PTree.gso by discriminate;
      rewrite ibde_entry_interaction_is_undef; discriminate)) as Hnot.
  destruct (ibk_split_sequence _ _ _ _ (ibde_fallback version) _ _ _ _ _ HfallbackNormal Hsuffix)
    as (return_le & return_m & fallback_t & return_t & _ & Hfallback & Hret).
  unfold ibde_return in Hret. inversion Hret; subst; clear Hret.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar BAG._interaction _) ?v |- _ =>
    inversion Hr; subst; clear Hr end.
  all: try solve [match goal with Hl : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ =>
    inversion Hl end].
  match goal with Hvalue : outcome_result_value _ _ _ _ |- _ =>
    rewrite Hreturn in Hvalue; cbn in Hvalue;
    destruct Hvalue as [_ Hcast]; destruct v; cbn in Hcast; try discriminate;
    inversion Hcast; subst end.
  match goal with Hcast : sem_cast (Vint ?returned_i) tuint tuint _ = Some (Vint _) |- _ =>
    change (Some (Vint returned_i) = Some (Vint (Int.repr 64))) in Hcast;
    inversion Hcast; subst returned_i end.
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ BAG._m Hfallback
    HreadonlyM) as (_ & Hmemory & _). try subst return_m.
  rewrite Hmemory in Hmovement, Hactor.
  exact (proj2 (ibde_fallback_above_uses_return_memory version empty_env cut_le cut_m
    mb mo ob oo movement_y actor_y _ _ _ _ Hm Ho Hnot Hmovement Hactor Hfallback
    ltac:(assumption))).
Qed.
