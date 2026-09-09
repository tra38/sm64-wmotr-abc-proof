(** One complete ground-step call really reaches the refresh checkpoint.
    Its preceding quarter steps retain their actual, unframed memory effects. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkGroundBackwardSource
  InkGroundDisplayBackward InkBackwardSource InkBackwardExecution InkFloorResetSource
  ObjectContactNecessity ContactConsumerExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Fixpoint igb_no_return (s : statement) : bool := match s with
| Sskip | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _
| Sbreak | Scontinue => true
| Ssequence a b | Sifthenelse _ a b | Sloop a b => igb_no_return a && igb_no_return b
| _ => false end.

Lemma igb_no_return_outcome : forall ge e le m s t le' m' out,
  ocn_exec ge e le m s t le' m' out -> igb_no_return s = true ->
  match out with Out_return _ => False | _ => True end.
Proof.
  intros ge e le m s t le' m' out Hrun.
  induction Hrun; cbn; intro Hshape; try discriminate; try exact I.
  - apply andb_true_iff in Hshape as [Ha Hb]. exact (IHHrun2 Hb).
  - apply andb_true_iff in Hshape as [Ha Hb]. exact (IHHrun Ha).
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b;
      [exact (IHHrun Ha)|exact (IHHrun Hb)].
  - apply andb_true_iff in Hshape as [Ha Hb]. inversion H; subst; [exact I|exact (IHHrun Ha)].
  - apply andb_true_iff in Hshape as [Ha Hb]. inversion H0; subst; [exact I|exact (IHHrun2 Hb)].
  - apply andb_true_iff in Hshape as [Ha Hb]. apply IHHrun3. apply andb_true_iff. auto.
Qed.

Lemma igb_loop_normal : forall ge e le m first second t le' m' out,
  ocn_exec ge e le m (Sloop first second) t le' m' out ->
  igb_no_return (Sloop first second) = true -> out = Out_normal.
Proof.
  intros ge e le m first second t le' m' out Hrun Hshape.
  pose proof (igb_no_return_outcome _ _ _ _ _ _ _ _ _ Hrun Hshape) as HnoReturn.
  remember (Sloop first second) as s eqn:Hs in Hrun.
  induction Hrun; inversion Hs; subst.
  - inversion H; subst; [reflexivity|contradiction].
  - inversion H0; subst; [reflexivity|contradiction].
  - apply IHHrun3; assumption || reflexivity.
Qed.

Lemma igb_first_finishes_normally : forall version ge e le m t le' m' out,
  ocn_exec ge e le m (igb_first version) t le' m' out -> out = Out_normal.
Proof.
  intros version ge e le m t le' m' out Hrun.
  destruct version; cbn [igb_first igb_body ibk_head fn_body] in Hrun;
    destruct (ibk_split_sequence _ _ _ _ (Sset IFR._i (Econst_int (Int.repr 0) tint))
      _ _ _ _ _ eq_refl Hrun) as (loop_le & loop_m & pre & rest & Htrace & Hset & Hloop).
  all: eapply igb_loop_normal; [exact Hloop|reflexivity].
Qed.

Lemma igb_entry_keeps_argument : forall version m mb mo e le m',
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (igb_body version) [Vptr mb mo] m e le m' ->
  le ! IFR._m = Some (Vptr mb mo) /\ e ! IFR._vec3f_copy = None.
Proof.
  intros version m mb mo e le m' Hentry.
  destruct (igb_source_cuts version) as (Hvars & Hparams & _).
  inversion Hentry; subst.
  split.
  - match goal with Hbind : bind_parameter_temps _ _ _ = Some _ |- _ =>
      rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; apply PTree.gss end.
  - match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
      rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
    match goal with Halloc : alloc_variables _ _ _ [] _ _ |- _ =>
      inversion Halloc; subst end.
    rewrite PTree.gso by discriminate. apply PTree.gempty.
Qed.

Lemma igb_split_after_first : forall version ge e le m rest t le' m' out,
  ocn_exec ge e le m (Ssequence (igb_first version) rest) t le' m' out ->
  exists middle memory pre suffix, t = pre ++ suffix /\
    ocn_exec ge e le m (igb_first version) pre middle memory Out_normal /\
    ocn_exec ge e middle memory rest suffix le' m' out.
Proof.
  intros version ge e le m rest t le' m' out Hrun. inversion Hrun; subst.
  - eauto 8.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (igb_first version) _ _ _ _ |- _ =>
      pose proof (igb_first_finishes_normally _ _ _ _ _ _ _ _ _ Hr) end. contradiction.
Qed.

Definition igb_prefix version := Ssequence (igb_first version) (igb_sound version).

Definition InkGroundCallRefreshCut : Prop :=
  forall version m mb mo t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (igb_body version))
    [Vptr mb mo] t m' result ->
  exists e entry_le entry_m cut_le cut_m copy_le copy_m last_le last_m pre copy_trace suffix out,
    t = pre ++ (copy_trace ++ suffix) /\
    function_entry2 ge (igb_body version) [Vptr mb mo] m e entry_le entry_m /\
    ocn_exec ge e entry_le entry_m (igb_prefix version) pre cut_le cut_m Out_normal /\
    cut_le ! IFR._m = Some (Vptr mb mo) /\ e ! IFR._vec3f_copy = None /\
    ocn_exec ge e cut_le cut_m (igb_refresh version) copy_trace copy_le copy_m Out_normal /\
    ocn_exec ge e copy_le copy_m (igb_tail version) suffix last_le last_m out /\
    outcome_result_value out (fn_return (igb_body version)) result last_m /\
    Mem.free_list last_m (blocks_of_env ge e) = Some m' /\
    (forall ob oo height, mb <> ob -> Mem.valid_block cut_m ob ->
      Mem.load Mint32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) = Some (Vptr ob oo) ->
      Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) = Some (Vsingle height) ->
      igb_refresh_witness version cut_m mb mo ob oo height copy_trace copy_m).

Theorem igb_completed_ground_call_reaches_display_refresh : InkGroundCallRefreshCut.
Proof.
  unfold InkGroundCallRefreshCut.
  intros version m mb mo t m' result Hcall.
  destruct (igb_source_cuts version) as (_ & _ & Hshape & _ & HsoundNormal & HrefreshNormal).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (igb_entry_keeps_argument _ _ _ _ _ _ _ Hentry) as [Hm Hlocal] end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hshape in Hbody;
    destruct (igb_split_after_first _ _ _ _ _ _ _ _ _ _ Hbody)
      as (first_le & first_m & first_trace & rest_trace & Htrace & Hfirst & Hrest) end.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HsoundNormal Hrest)
    as (cut_le & cut_m & sound_trace & following_trace & HrestTrace & Hsound & Hfollowing).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HrefreshNormal Hfollowing)
    as (copy_le & copy_m & copy_trace & suffix & HfollowingTrace & Hcopy & Hsuffix).
  assert (cce_keeps_temp IFR._m (igb_first version) = true /\
    cce_keeps_temp IFR._m (igb_sound version) = true) as [HkeepFirst HkeepSound]
    by (destruct version; split; reflexivity).
  pose proof (cce_argument_temporary_is_preserved _ _ _ _ _ _ _ _ _ _ Hfirst HkeepFirst) as HfirstM.
  pose proof (cce_argument_temporary_is_preserved _ _ _ _ _ _ _ _ _ _ Hsound HkeepSound) as HsoundM.
  assert (cut_le ! IFR._m = Some (Vptr mb mo)) as HcutM by congruence.
  match goal with
  | Hentry : function_entry2 _ _ _ _ ?env ?entry_le ?entry_m,
    Hlast : ocn_exec _ _ _ _ _ _ ?last_le ?last_m ?out |- _ =>
      exists env, entry_le, entry_m, cut_le, cut_m, copy_le, copy_m, last_le, last_m,
        (first_trace ++ sound_trace), copy_trace, suffix, out
  end.
  split.
  - rewrite Htrace, HrestTrace, HfollowingTrace. apply app_assoc.
  - split; [assumption|]. split.
    + unfold igb_prefix. eapply exec_Sseq_1; eauto.
    + repeat match goal with |- _ /\ _ => split; [assumption|] end.
      intros ob oo height Hseparate Hvalid Hobject Hheight.
      eapply igb_refresh_reads_current_movement_height; eauto.
Qed.
