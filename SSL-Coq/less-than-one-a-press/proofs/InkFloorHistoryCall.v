(** These cuts are extracted from completed selected calls, retaining local
    allocations and every preceding helper's real memory effects. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkFloorHistorySource
  InkBackwardSource InkBackwardExecution InkCopyCaller InkFloorResetExecution
  ObjectContactNecessity ContactConsumerExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Lemma ifh_quarter_entry_arguments : forall version ge m mb mo nb no e le entry_m,
  function_entry2 ge (ifh_quarter_body version) [Vptr mb mo; Vptr nb no] m e le entry_m ->
  le ! IFH._m = Some (Vptr mb mo) /\
  le ! IFH._nextPos = Some (Vptr nb no) /\
  e ! IFH._vec3f_set = None /\ e ! IFH._vec3f_copy = None.
Proof.
  intros version ge m mb mo nb no e le entry_m Hentry.
  destruct (ifh_quarter_source_cuts version) as (Hparams & Hvars & _).
  inversion Hentry; subst.
  assert (le ! IFH._m = Some (Vptr mb mo) /\ le ! IFH._nextPos = Some (Vptr nb no))
    as [Hm Hnext].
  { match goal with Hbind : bind_parameter_temps _ _ _ = Some le |- _ =>
      rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; subst le end.
    split; [rewrite PTree.gso by discriminate; apply PTree.gss|apply PTree.gss]. }
  repeat split; try assumption.
  all: match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  all: repeat match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: repeat rewrite PTree.gso by discriminate; apply PTree.gempty.
Qed.

Definition InkGroundQuarterCallHistoryCut : Prop :=
  forall version m mb mo nb no t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (ifh_quarter_body version))
    [Vptr mb mo; Vptr nb no] t m' result ->
  exists e entry_le entry_m cut_le cut_m last_le last_m pre rest out,
    t = pre ++ rest /\
    function_entry2 ge (ifh_quarter_body version) [Vptr mb mo; Vptr nb no]
      m e entry_le entry_m /\
    ocn_exec ge e entry_le entry_m (ocn_prepend (ifh_quarter_prefix version) Sskip)
      pre cut_le cut_m Out_normal /\
    cut_le ! IFH._m = Some (Vptr mb mo) /\
    cut_le ! IFH._nextPos = Some (Vptr nb no) /\
    e ! IFH._vec3f_set = None /\ e ! IFH._vec3f_copy = None /\
    ocn_exec ge e cut_le cut_m (ifh_quarter_tail version) rest last_le last_m out /\
    outcome_result_value out (fn_return (ifh_quarter_body version)) result last_m /\
    Mem.free_list last_m (blocks_of_env ge e) = Some m'.

Theorem ifh_completed_quarter_call_reaches_queried_floor_cut : InkGroundQuarterCallHistoryCut.
Proof.
  unfold InkGroundQuarterCallHistoryCut.
  intros version m mb mo nb no t m' result Hcall.
  destruct (ifh_quarter_source_cuts version) as (_ & _ & Hbody & Hnormal & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (ifh_quarter_entry_arguments _ _ _ _ _ _ _ _ _ _ He)
      as (Hm & Hnext & HsetLocal & HcopyLocal) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (cut_le & cut_m & pre & rest & Htrace & Hprefix & Htail) end.
  assert (ifr_keeps_temp IFH._m (ocn_prepend (ifh_quarter_prefix version) Sskip) = true /\
    ifr_keeps_temp IFH._nextPos (ocn_prepend (ifh_quarter_prefix version) Sskip) = true)
    as [HkeepM HkeepNext] by (destruct version; split; reflexivity).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepM) as HmSame.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepNext) as HnextSame.
  match goal with He : function_entry2 _ _ _ _ ?env ?el ?em,
    Hlast : ocn_exec _ _ _ _ _ _ ?ll ?lm ?o |- _ =>
    exists env, el, em, cut_le, cut_m, ll, lm, pre, rest, o end.
  repeat apply conj; try assumption; congruence.
Qed.

(** Unlike an arbitrary temporary at a detached assignment, these locals
    carry the original Mario argument through both actual wall calls. *)
Definition InkGeometryFloorQueryHistoryCut : Prop :=
  forall version m mb mo t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (ibk_geometry_body version))
    [Vptr mb mo] t m' result ->
  exists entry_le query_le query_m after_le after_m final_le pre query_trace suffix out,
    t = pre ++ (query_trace ++ suffix) /\
    function_entry2 ge (ibk_geometry_body version) [Vptr mb mo] m empty_env entry_le m /\
    ocn_exec ge empty_env entry_le m (ocn_prepend (ifh_geometry_walls version) Sskip)
      pre query_le query_m Out_normal /\
    query_le ! IBM._m = Some (Vptr mb mo) /\
    ocn_exec ge empty_env query_le query_m (ifh_geometry_query version)
      query_trace after_le after_m Out_normal /\
    ocn_exec ge empty_env after_le after_m (ifh_geometry_after_query version)
      suffix final_le m' out.

Theorem ifh_completed_geometry_call_reaches_primary_floor_query : InkGeometryFloorQueryHistoryCut.
Proof.
  unfold InkGeometryFloorQueryHistoryCut.
  intros version m mb mo t m' result Hcall.
  destruct (ifh_geometry_source_cuts version) as (Hbody & Hnormal & _ & _ & _ & HqueryNormal).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    pose proof He as Hentry; inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    assert (fn_vars (ibk_geometry_body version) = []) as Hvars
      by (destruct version; reflexivity);
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?el |- _ =>
    assert (el ! IBM._m = Some (Vptr mb mo)) as Hm by
      (assert (fn_params (ibk_geometry_body version) =
        [(IBM._m, tptr (Tstruct IBM._MarioState noattr))]) as Hp
        by (destruct version; reflexivity);
       rewrite Hp in Hbind; cbn in Hbind; inversion Hbind; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (query_le & query_m & pre & rest & Htrace & Hprefix & Hrest) end.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HqueryNormal Hrest)
    as (after_le & after_m & query_trace & suffix & Hresttrace & Hquery & Hsuffix).
  assert (ifr_keeps_temp IBM._m (ocn_prepend (ifh_geometry_walls version) Sskip) = true)
    as Hkeep by (destruct version; reflexivity).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix Hkeep) as HmSame.
  match type of Hentry with function_entry2 _ _ _ _ _ ?el _ =>
    match type of Hsuffix with ocn_exec _ _ _ _ _ _ ?fl _ ?o =>
      exists el, query_le, query_m, after_le, after_m, fl, pre, query_trace, suffix, o end end.
  repeat apply conj; try assumption; congruence.
Qed.
