(** A completed ordinary air-step call reaches its actual display refresh.

    The real quarter steps, terrain helper, gravity and vertical wind remain
    one unframed execution prefix.  This does not bound flight height, invent
    an actor-placement restriction, or cover every action/history.  It exposes
    the copy that forgets an earlier movement/display split, even if the
    preceding quarter step found no floor. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_mario_step jp_mario_step.
From LessThanOneAPress.Proofs Require Import GameTypes InkGroundBackwardSource
  InkGroundCallBackward InkGroundDisplayBackward InkBackwardSource InkBackwardExecution
  InkCopyCaller InkFloorResetSource InkFloorResetExecution ObjectContactNecessity
  ContactConsumerExecution SecretContactExecution Area2Rank12BContact
  UpperElevatorQueryResolution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iaf_body version := match version with
| VersionUS => us_mario_step.f_perform_air_step
| VersionJP => jp_mario_step.f_perform_air_step end.
Definition iaf_item version index :=
  ibk_head (rank12b_drop_sequences index (fn_body (iaf_body version))).
Definition iaf_before_loop version := map (iaf_item version) [0%nat;1%nat].
Definition iaf_loop version := iaf_item version 2.
Definition iaf_after_loop version := map (iaf_item version) [3%nat;4%nat;5%nat;6%nat].
Definition iaf_refresh version := iaf_item version 7.
Definition iaf_tail version := rank12b_drop_sequences 8 (fn_body (iaf_body version)).
Definition iaf_prefix version := ocn_prepend (iaf_before_loop version)
  (Ssequence (iaf_loop version) (ocn_prepend (iaf_after_loop version) Sskip)).

Definition iaf_object := Ederef (Etempvar IFR._t'8 (tptr (Tstruct IFR._Object noattr)))
  (Tstruct IFR._Object noattr).
Definition iaf_graphics := Efield (Efield iaf_object IFR._header
  (Tstruct IFR._ObjectNode noattr)) IFR._gfx (Tstruct IFR._GraphNodeObject noattr).
Definition iaf_display := Efield iaf_graphics IFR._pos (tarray tfloat 3).
Definition iaf_copy := Scall None
  (Evar IFR._vec3f_copy (Tfunction [tptr tfloat;tptr tfloat] (tptr tvoid) cc_default))
  [iaf_display;ibcc_destination].

Lemma iaf_source_cuts : forall version,
  fn_vars (iaf_body version) = [(IFR._intendedPos,tarray tfloat 3)] /\
  fn_params (iaf_body version) =
    [(IFR._m,tptr (Tstruct IFR._MarioState noattr));(IFR._stepArg,tuint)] /\
  fn_body (iaf_body version) = ocn_prepend (iaf_before_loop version)
    (Ssequence (iaf_loop version)
      (ocn_prepend (iaf_after_loop version)
        (Ssequence (iaf_refresh version) (iaf_tail version)))) /\
  iaf_refresh version = Ssequence (Sset IFR._t'8 ibk_object_read) iaf_copy /\
  forallb ibk_normal (iaf_before_loop version) = true /\
  forallb ibk_normal (iaf_after_loop version) = true /\
  ibk_normal (iaf_refresh version) = true /\
  cce_keeps_temp IFR._m (iaf_prefix version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma iaf_selected_body_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IFR._perform_air_step = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (iaf_body version)).
Proof.
  intro version.
  exact (upper_elevator_selected_query_body_resolves version UEQRPerformAirStep).
Qed.

Lemma iaf_loop_finishes_normally : forall version ge e le m t le' m' out,
  ocn_exec ge e le m (iaf_loop version) t le' m' out -> out = Out_normal.
Proof.
  intros version ge e le m t le' m' out Hrun.
  destruct version; cbn [iaf_loop iaf_item iaf_body ibk_head rank12b_drop_sequences fn_body] in Hrun;
    destruct (ibk_split_sequence _ _ _ _ (Sset IFR._i (Econst_int (Int.repr 0) tint))
      _ _ _ _ _ eq_refl Hrun)
      as (loop_le & loop_m & pre & rest & Htrace & Hset & Hloop).
  all: eapply igb_loop_normal; [exact Hloop|reflexivity].
Qed.

Lemma iaf_split_after_loop : forall version ge e le m rest t le' m' out,
  ocn_exec ge e le m (Ssequence (iaf_loop version) rest) t le' m' out ->
  exists middle memory pre suffix, t = pre ++ suffix /\
    ocn_exec ge e le m (iaf_loop version) pre middle memory Out_normal /\
    ocn_exec ge e middle memory rest suffix le' m' out.
Proof.
  intros version ge e le m rest t le' m' out Hrun. inversion Hrun; subst.
  - eauto 8.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (iaf_loop version) _ _ _ _ |- _ =>
      pose proof (iaf_loop_finishes_normally _ _ _ _ _ _ _ _ _ Hr) end.
    contradiction.
Qed.

Lemma iaf_append_normal_prefix : forall ge e items rest le m middle memory
  pre suffix le' m',
  ocn_exec ge e le m (ocn_prepend items Sskip) pre middle memory Out_normal ->
  ocn_exec ge e middle memory rest suffix le' m' Out_normal ->
  ocn_exec ge e le m (ocn_prepend items rest) (pre ++ suffix) le' m' Out_normal.
Proof.
  intros ge e items. induction items as [|head tail IH];
    intros rest le m middle memory pre suffix le' m' Hprefix Hsuffix.
  - cbn [ocn_prepend] in Hprefix |- *.
    inversion Hprefix; subst. exact Hsuffix.
  - cbn [ocn_prepend] in Hprefix |- *.
    inversion Hprefix; subst; try contradiction.
    match goal with Hrest : ClightBigstep.exec_stmt _ _ _ _ _
      (ocn_prepend tail Sskip) _ _ _ Out_normal |- _ =>
        pose proof (IH _ _ _ _ _ _ _ _ _ Hrest Hsuffix) as Hcombined end.
    rewrite <- app_assoc. eapply exec_Sseq_1; eauto.
Qed.

Lemma iaf_entry_keeps_argument : forall version m mb mo step_arg e le m',
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (iaf_body version) [Vptr mb mo;Vint step_arg] m e le m' ->
  le ! IFR._m = Some (Vptr mb mo) /\ e ! IFR._vec3f_copy = None.
Proof.
  intros version m mb mo step_arg e le m' Hentry.
  destruct (iaf_source_cuts version) as (Hvars & Hparams & _).
  inversion Hentry; subst.
  split.
  - match goal with Hbind : bind_parameter_temps _ _ _ = Some _ |- _ =>
      rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
        rewrite PTree.gso by discriminate; apply PTree.gss end.
  - match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
      rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
    match goal with Halloc : alloc_variables _ _ _ [] _ _ |- _ =>
      inversion Halloc; subst end.
    rewrite PTree.gso by discriminate. apply PTree.gempty.
Qed.

Lemma iaf_display_address : forall version e le m ob oo answer,
  le ! IFR._t'8 = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m iaf_display answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)).
Proof.
  intros version e le m ob oo answer Hobject Hread.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & Hpos).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iaf_object v -> v = Vptr ob oo) as Hobj
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m (Efield iaf_object IFR._header (Tstruct IFR._ObjectNode noattr)) v ->
    v = Vptr ob oo) as Hhead.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _ iaf_object IFR._Object
      IFR._header (Tstruct IFR._ObjectNode noattr) ob oo 0 v
      eq_refl Hobj Hheader (or_intror eq_refl) Hr) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iaf_graphics v -> v = Vptr ob oo) as Hgraph.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _
      (Efield iaf_object IFR._header (Tstruct IFR._ObjectNode noattr)) IFR._ObjectNode
      IFR._gfx (Tstruct IFR._GraphNodeObject noattr) ob oo 0 v
      eq_refl Hhead Hgfx (or_intror eq_refl) Hr) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  eapply ibcc_aggregate_field with (base := iaf_graphics)
    (tag := IFR._GraphNodeObject) (field := IFR._pos) (ty := tarray tfloat 3)
    (delta := 32); eauto; reflexivity.
Qed.

Lemma iaf_copy_arguments : forall version e le m mb mo ob oo args,
  le ! IFR._m = Some (Vptr mb mo) -> le ! IFR._t'8 = Some (Vptr ob oo) ->
  eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
    [iaf_display;ibcc_destination] [tptr tfloat;tptr tfloat] args ->
  args = [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32));Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))].
Proof.
  intros version e le m mb mo ob oo args Hm Hobject Hargs.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ iaf_display ?value |- _ =>
    assert (value = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)))
      by (eapply iaf_display_address; eauto); subst value end.
  match goal with H : eval_expr _ _ _ _ ibcc_destination ?value |- _ =>
    assert (value = Vptr mb (Ptrofs.add mo (Ptrofs.repr 60)))
      by (eapply ifr_state_position_value; eauto); subst value end.
  repeat match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst; clear H end.
  reflexivity.
Qed.

Lemma iaf_refresh_calls_selected_copy : forall version e le m mb mo ob oo t le' m' out,
  e ! IFR._vec3f_copy = None -> le ! IFR._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iaf_refresh version) t le' m' out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m (Internal (ibk_copy_body version))
    [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32));Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))]
    t m' result.
Proof.
  intros version e le m mb mo ob oo t le' m' out Hlocal Hm Hobject Hrun.
  destruct (iaf_source_cuts version) as (_ & _ & _ & Hshape & _). rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IFR._t'8 ibk_object_read) _ _ _ _ _ eq_refl Hrun)
    as (copy_le & copy_m & pre & rest & Htrace & Hread & Hcopy).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply ibcc_actual_object_read; eauto); subst v end.
  destruct (ibk_selected_copy_resolves version) as (b & Hsymbol & Hfunction).
  inversion Hcopy; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hr : eval_exprlist ?ge ?env ?temps ?memory _ _ ?args |- _ =>
    assert (args = [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32));
      Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))]) as Hargs by
      (eapply (iaf_copy_arguments version env temps memory mb mo ob oo);
        [rewrite PTree.gso by discriminate; exact Hm|apply PTree.gss|exact Hr]); subst args end.
  eauto.
Qed.

Definition InkAirCallRefreshCut : Prop :=
  forall version m mb mo step_arg t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (iaf_body version))
    [Vptr mb mo;Vint step_arg] t m' result ->
  exists e entry_le entry_m cut_le cut_m copy_le copy_m last_le last_m pre copy_trace suffix out,
    t = pre ++ (copy_trace ++ suffix) /\
    function_entry2 ge (iaf_body version) [Vptr mb mo;Vint step_arg] m e entry_le entry_m /\
    ocn_exec ge e entry_le entry_m (iaf_prefix version) pre cut_le cut_m Out_normal /\
    cut_le ! IFR._m = Some (Vptr mb mo) /\ e ! IFR._vec3f_copy = None /\
    ocn_exec ge e cut_le cut_m (iaf_refresh version) copy_trace copy_le copy_m Out_normal /\
    ocn_exec ge e copy_le copy_m (iaf_tail version) suffix last_le last_m out /\
    outcome_result_value out (fn_return (iaf_body version)) result last_m /\
    Mem.free_list last_m (blocks_of_env ge e) = Some m' /\
    (forall ob oo,
      Mem.load Mint32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) = Some (Vptr ob oo) ->
      exists copy_result, ClightBigstep.Clight2.eval_funcall ge cut_m
        (Internal (ibk_copy_body version))
        [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32));Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))]
        copy_trace copy_m copy_result).

Theorem iaf_completed_air_call_reaches_display_refresh : InkAirCallRefreshCut.
Proof.
  unfold InkAirCallRefreshCut. cbn zeta.
  intros version m mb mo step_arg t m' result Hcall.
  destruct (iaf_source_cuts version) as (_ & _ & Hshape & _ & Hbefore & Hafter & Hrefresh & Hkeep).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (iaf_entry_keeps_argument _ _ _ _ _ _ _ _ Hentry) as [Hm Hlocal] end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hshape in Hbody;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hbefore Hbody)
      as (before_le & before_m & before_t & rest_t & Htrace & Hinitial & Hrest) end.
  destruct (iaf_split_after_loop _ _ _ _ _ _ _ _ _ _ Hrest)
    as (loop_le & loop_m & loop_t & after_t & HrestTrace & Hloop & HafterRun).
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hafter HafterRun)
    as (cut_le & cut_m & after_loop_t & following_t & HafterTrace & HafterLoop & Hfollowing).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hrefresh Hfollowing)
    as (copy_le & copy_m & copy_trace & suffix & HfollowingTrace & Hcopy & Hsuffix).
  assert (ocn_exec (Clight.globalenv (selected_clight_target version)) e le1 m1
    (iaf_prefix version) (before_t ++ (loop_t ++ after_loop_t)) cut_le cut_m Out_normal)
    as Hprefix.
  { unfold iaf_prefix.
    eapply iaf_append_normal_prefix; [exact Hinitial|].
    eapply exec_Sseq_1; eauto. }
  pose proof (cce_argument_temporary_is_preserved _ _ _ _ _ _ _ _ _ _ Hprefix Hkeep) as HprefixM.
  assert (cut_le ! IFR._m = Some (Vptr mb mo)) as HcutM by congruence.
  match goal with
  | Hentry : function_entry2 _ _ _ _ ?env ?entry_le ?entry_m,
    Hlast : ocn_exec _ _ _ _ (iaf_tail version) _ ?last_le ?last_m ?out |- _ =>
      exists env, entry_le, entry_m, cut_le, cut_m, copy_le, copy_m, last_le, last_m,
        (before_t ++ (loop_t ++ after_loop_t)), copy_trace, suffix, out
  end.
  split.
  - rewrite Htrace, HrestTrace, HafterTrace, HfollowingTrace.
    repeat rewrite app_assoc. reflexivity.
  - repeat match goal with |- _ /\ _ => split; [assumption|] end.
    intros ob oo Hobject. eapply iaf_refresh_calls_selected_copy; eauto.
Qed.
