(** Backward to an actual display reset after an ordinary floor snap.
    The incoming floor height is not assumed controller-reachable. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyEntry InkCopyCaller InkFloorResetSource
  ObjectContactNecessity ContactConsumerExecution SecretContactExecution
  EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

(** Callees can change memory, but not an unassigned caller temporary.
    This is a temporary-only theorem: no outside-call memory frame is assumed. *)
Fixpoint ifr_keeps_temp (keep : ident) (s : statement) : bool := match s with
| Sskip | Sassign _ _ | Sreturn _ => true
| Sset id _ => negb (Pos.eqb id keep)
| Scall None _ _ => true
| Scall (Some id) _ _ => negb (Pos.eqb id keep)
| Ssequence first rest | Sifthenelse _ first rest =>
    ifr_keeps_temp keep first && ifr_keeps_temp keep rest
| _ => false end.

Lemma ifr_execution_keeps_temp : forall ge e le m s t le' m' out keep,
  ocn_exec ge e le m s t le' m' out ->
  ifr_keeps_temp keep s = true -> le' ! keep = le ! keep.
Proof.
  intros ge e le m s t le' m' out keep Hrun.
  induction Hrun; cbn; intro Hshape; try discriminate; try reflexivity.
  - apply negb_true_iff in Hshape. apply Pos.eqb_neq in Hshape.
    apply PTree.gso. congruence.
  - destruct optid; cbn in Hshape; [|reflexivity].
    apply negb_true_iff in Hshape. apply Pos.eqb_neq in Hshape.
    apply PTree.gso. congruence.
  - apply andb_true_iff in Hshape as [Ha Hb].
    rewrite (IHHrun2 Hb), (IHHrun1 Ha). reflexivity.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; auto.
Qed.

Lemma ifr_prefix_properties : forall version kind,
  forallb ibk_normal (ifr_prefix version kind) = true /\
  ifr_keeps_temp IFR._m (ocn_prepend (ifr_prefix version kind) Sskip) = true /\
  ifr_keeps_temp IFR._marioObj (ocn_prepend (ifr_prefix version kind) Sskip) = true /\
  ibk_normal (ifr_snap version kind) = true /\
  ibk_normal (ifr_copy_call version kind) = true /\
  ibk_normal (ifr_reset_tail version kind) = true.
Proof. intros [] []; repeat split; reflexivity. Qed.

Definition InkFloorResetObjectPrelude : Prop :=
  forall version kind m mb mo ob oo t m' result,
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) =
    Some (Vptr ob oo) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifr_body version kind)) [Vptr mb mo] t m' result ->
  exists cut_le cut_m final_le pre suf out,
    t = pre ++ suf /\
    cut_le ! IFR._m = Some (Vptr mb mo) /\
    cut_le ! IFR._marioObj = Some (Vptr ob oo) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
      cut_le cut_m (ifr_after_prefix version kind) suf final_le m' out.

Theorem ifr_actual_call_remembers_entry_object : InkFloorResetObjectPrelude.
Proof.
  unfold InkFloorResetObjectPrelude.
  intros version kind m mb mo ob oo t m' result Hobject Hcall.
  destruct (ifr_source_cuts version kind) as (Hvars & Hbody & _).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IFR._m = Some (Vptr mb mo)) as Hm
      by (destruct version, kind; cbn in Hbind; inversion Hbind; reflexivity) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_sequence _ _ _ _ (Sset IFR._marioObj ibk_object_read)
      _ _ _ _ _ eq_refl Hr) as (cache_le & cache_m & cache_t & rest_t & Htrace & Hcache & Hrest) end.
  inversion Hcache; subst; clear Hcache.
  match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?object |- _ =>
    assert (object = Vptr ob oo) by (eapply ibcc_actual_object_read; eauto); subst object end.
  destruct (ifr_prefix_properties version kind) as (Hnormal & HkeepM & HkeepO & _).
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (cut_le & cut_m & pre & suf & Hresttrace & Hprefix & Hsuffix).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepM) as HmSame.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepO) as HoSame.
  rewrite PTree.gso in HmSame by discriminate. rewrite PTree.gss in HoSame.
  match type of Hsuffix with ocn_exec _ _ _ _ _ _ ?final_le _ ?out =>
    exists cut_le, cut_m, final_le, pre, suf, out end.
  repeat split; try assumption; congruence.
Qed.

(** An actual stationary call either takes the moving-ground branch or the
    reset branch. We do not silently apply the no-step reset to both. *)
Theorem ifr_actual_stationary_choice : forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifr_after_prefix version IFRStationary) t le' m' out ->
  exists moving branch_le branch_m branch_trace return_trace,
    t = branch_trace ++ return_trace /\
    ocn_test_value (Clight.globalenv (selected_clight_target version)) e le m
      (Etempvar IFR._takeStep tuint) moving /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (if moving then ifr_moving_branch version else ifr_reset_tail version IFRStationary)
      branch_trace branch_le branch_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e branch_le branch_m
      (Sreturn (Some (Etempvar IFR._stepResult tuint))) return_trace le' m' out.
Proof.
  intros version e le m t le' m' out Hrun.
  rewrite ifr_stationary_split_source in Hrun.
  assert (ibk_normal (Sifthenelse (Etempvar IFR._takeStep tuint)
    (ifr_moving_branch version) (ifr_reset_tail version IFRStationary)) = true)
    as Hnormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (branch_le & branch_m & branch_trace & return_trace & Htrace & Hbranch & Hreturn).
  inversion Hbranch; subst. do 5 eexists. repeat split; try eassumption.
  unfold ocn_test_value. eauto.
Qed.

Lemma ifr_selected_floor_field : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IBM._MarioState IFR._floorHeight 112 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IFR._floorHeight 112 = true).
  rewrite <- rank15_selected_header_environment_exact. destruct version; vm_compute; reflexivity.
Qed.

(** Shared index rule for the actual position-array expressions. *)
Lemma ifr_array_index_location : forall ge e le m base n b ofs loc offset bf,
  typeof base = tarray tfloat 3 ->
  (forall v, eval_expr ge e le m base v -> v = Vptr b ofs) ->
  eval_lvalue ge e le m (Ederef (Ebinop Oadd base
    (Econst_int (Int.repr n) tint) (tptr tfloat)) tfloat) loc offset bf ->
  loc = b /\ offset = Ptrofs.add ofs
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr n))) /\ bf = Full.
Proof.
  intros ge e le m base n b ofs loc offset bf Htype Hbase Hl.
  inversion Hl; subst.
  match goal with Hb : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hb; subst; clear Hb end.
  - match goal with Hb : eval_expr _ _ _ _ base _ |- _ => apply Hbase in Hb; subst end.
    match goal with Hc : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hc; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn [typeof] in Hsem; rewrite Htype in Hsem; cbn in Hsem; inversion Hsem; subst end.
    repeat split; reflexivity.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Lemma ifr_state_position_value : forall version e le m mb mo answer,
  le ! IFR._m = Some (Vptr mb mo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ibcc_destination answer -> answer = Vptr mb (Ptrofs.add mo (Ptrofs.repr 60)).
Proof.
  intros. eapply ibcc_aggregate_field with (base := ibcc_state)
    (tag := IBM._MarioState) (field := IBM._pos) (ty := tarray tfloat 3) (delta := 60).
  - reflexivity.
  - intros. eapply ibcc_deref_struct; eauto.
  - exact (proj1 (ibcc_selected_fields version)).
  - left; reflexivity.
  - eassumption.
Qed.

Lemma ifr_state_y_location : forall version e le m mb mo b ofs bf,
  le ! IFR._m = Some (Vptr mb mo) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    ifr_y_cell b ofs bf ->
  b = mb /\ ofs = Ptrofs.add mo (Ptrofs.repr 64) /\ bf = Full.
Proof.
  intros version e le m mb mo b ofs bf Hm Hl.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_destination v -> v = Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))) as Hbase
    by (intros; eapply ifr_state_position_value; eauto).
  destruct (ifr_array_index_location _ _ _ _ ibcc_destination _ _ _ _ _ _
    eq_refl Hbase Hl) as (-> & -> & ->).
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1))) with (Ptrofs.repr 4).
  rewrite Ptrofs.add_assoc. repeat split; reflexivity.
Qed.

Lemma ifr_floor_read_value : forall version e le m mb mo height answer,
  le ! IFR._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 112))) =
    Some (Vsingle height) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ifr_floor_read answer -> answer = Vsingle height.
Proof.
  intros version e le m mb mo height answer Hm Hload Hread.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ibcc_state v -> v = Vptr mb mo) as Hbase by (intros; eapply ibcc_deref_struct; eauto).
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibcc_field_location _ _ _ _ ibcc_state IBM._MarioState
      IFR._floorHeight tfloat _ _ _ _ _ _ eq_refl Hbase
      (ifr_selected_floor_field version) Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn [typeof access_mode] in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 112))) = Some answer)
      in Hr; congruence end.
Qed.

Theorem ifr_snap_writes_floor_height : forall version kind e le m mb mo height t le' m' out,
  le ! IFR._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 112))) =
    Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifr_snap version kind) t le' m' out ->
  Mem.store Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64)))
    (Vsingle height) = Some m' /\
  le' = PTree.set (ifr_floor_temp kind) (Vsingle height) le /\
  t = E0 /\ out = Out_normal.
Proof.
  intros version kind e le m mb mo height t le' m' out Hm Hfloor Hrun.
  destruct (ifr_source_cuts version kind) as (_ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ ifr_floor_read ?value |- _ =>
    assert (value = Vsingle height) by (eapply ifr_floor_read_value; eauto); subst value end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  assert ((PTree.set (ifr_floor_temp kind) (Vsingle height) le) ! IFR._m = Some (Vptr mb mo))
    as HmNow by (rewrite PTree.gso; [exact Hm|destruct kind; discriminate]).
  match goal with Hl : eval_lvalue _ _ _ _ ifr_y_cell _ _ _ |- _ =>
    destruct (ifr_state_y_location _ _ _ _ _ _ _ _ _ HmNow Hl) as (-> & -> & ->) end.
  match goal with He : eval_expr _ _ _ _ (Etempvar _ _) ?value |- _ =>
    assert (value = Vsingle height) by (eapply ocn_temp_value; [exact He|apply PTree.gss]); subst value end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  repeat split; try reflexivity; assumption.
Qed.
