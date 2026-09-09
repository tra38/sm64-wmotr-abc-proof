(** Necessary predecessors of the Ink retry in ACTUAL Clight execution.
    This does not assume a clean controller path to those predecessors. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  ObjectContactNecessity ContactConsumerExecution SecretContactExecution
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

(** A structural termination-outcome fact, NOT a memory-frame assumption:
    callees may have effects, but these completed statements do not return
    from their enclosing function. *)
Fixpoint ibk_normal (s : statement) : bool := match s with
| Sskip | Sassign _ _ | Sset _ _ | Scall _ _ _ => true
| Ssequence a b | Sifthenelse _ a b => ibk_normal a && ibk_normal b
| _ => false end.

Lemma ibk_normal_outcome : forall ge e le m s t le' m' out,
  ibk_normal s = true -> ocn_exec ge e le m s t le' m' out -> out = Out_normal.
Proof.
  intros ge e le m s t le' m' out Hshape Hrun.
  induction Hrun; cbn in Hshape; try discriminate; try reflexivity.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. exfalso. apply H. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; auto.
Qed.

Lemma ibk_split_sequence : forall ge e le m first rest t le' m' out,
  ibk_normal first = true ->
  ocn_exec ge e le m (Ssequence first rest) t le' m' out ->
  exists middle memory pre suf, t = pre ++ suf /\
    ocn_exec ge e le m first pre middle memory Out_normal /\
    ocn_exec ge e middle memory rest suf le' m' out.
Proof.
  intros ge e le m first rest t le' m' out Hshape Hrun.
  inversion Hrun; subst.
  - eauto 8.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ first _ _ _ _ |- _ =>
      pose proof (ibk_normal_outcome _ _ _ _ _ _ _ _ _ Hshape Hr) end.
    contradiction.
Qed.

Lemma ibk_split_prefix : forall ge e items rest le m t le' m' out,
  forallb ibk_normal items = true ->
  ocn_exec ge e le m (ocn_prepend items rest) t le' m' out ->
  exists middle memory pre suf, t = pre ++ suf /\
    ocn_exec ge e le m (ocn_prepend items Sskip) pre middle memory Out_normal /\
    ocn_exec ge e middle memory rest suf le' m' out.
Proof.
  intros ge e items. induction items as [|head tail IH];
    intros rest le m t le' m' out Hshape Hrun.
  - exists le, m, E0, t. split; [reflexivity|].
    split; [apply exec_Sskip|exact Hrun].
  - cbn in Hshape. apply andb_true_iff in Hshape as [Hhead Htail].
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hhead Hrun)
      as (first_le & first_m & first_t & rest_t & Htrace & Hfirst & Hrest).
    destruct (IH _ _ _ _ _ _ _ Htail Hrest)
      as (middle & memory & pre & suf & Hresttrace & Hprefix & Hsuffix).
    exists middle, memory, (first_t ++ pre), suf. split.
    + subst. apply app_assoc.
    + split; [cbn [ocn_prepend]; eapply exec_Sseq_1; eauto|exact Hsuffix].
Qed.

Lemma ibk_generated_prefixes_finish_normally : forall version,
  forallb ibk_normal (ibk_before_retry version) = true /\
  ibk_normal (ibk_choice version) = true /\
  ibk_normal (ibk_copy_prefix version) = true /\
  forallb ibk_normal (ibk_copy_before_y version) = true /\
  ibk_normal (ibk_copy_y version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

(** The prefix, actual floor read, chosen branch and suffix belong to ONE
    completed geometry call. We do not replace the floor read with an assumed
    floor result or with the floor cached on entry to the frame. *)
Definition InkGeometryBackwardCut : Prop :=
  forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ibk_geometry_body version)) t le' m' out ->
  exists cut_le cut_m middle_le middle_m floor choice pre branch suf,
    t = pre ++ (branch ++ suf) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ocn_prepend (ibk_before_retry version) Sskip) pre cut_le cut_m Out_normal /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e cut_le cut_m
      ibk_floor_read floor /\
    ocn_test_value (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBM._t'41 floor cut_le) cut_m ibk_null_guard choice /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBM._t'41 floor cut_le) cut_m
      (if choice then ibk_retry version else Sskip)
      branch middle_le middle_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      middle_le middle_m (ibk_after_retry version) suf le' m' out.

Theorem ibk_actual_geometry_has_ordered_retry_cut : InkGeometryBackwardCut.
Proof.
  unfold InkGeometryBackwardCut.
  intros version e le m t le' m' out Hrun.
  destruct (ibk_geometry_cuts_are_generated version) as (Hbody & Hchoice & _).
  destruct (ibk_generated_prefixes_finish_normally version) as (Hprefix & Hnormal & _).
  rewrite Hbody in Hrun.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hprefix Hrun)
    as (cut_le & cut_m & pre & rest & Htrace & Hpre & Hrest).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (middle_le & middle_m & branch & suf & Hresttrace & Hbranch & Hsuf).
  rewrite Hchoice in Hbranch.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hbranch.
  cce_unroll_loop_free_exec.
  all: do 4 eexists; eexists; eexists; do 3 eexists;
    repeat split; try eassumption; try (subst; reflexivity).
  all: unfold ocn_test_value; eauto.
  all: try contradiction.
  all: apply exec_Sskip.
Qed.

(** Non-null means a real pointer here, not a potentially non-pointer value
    supplied by an unproved memory projection. An invalid comparison cannot
    be used, since the theorem assumes a successful defined evaluation. *)
Theorem ibk_nonnull_floor_cannot_take_retry : forall ge e le m block offset,
  le ! IBM._t'41 = Some (Vptr block offset) ->
  ~ ocn_test_value ge e le m ibk_null_guard true.
Proof.
  intros ge e le m block offset Hfloor [answer [Hexpr Hbool]].
  unfold ibk_null_guard in Hexpr. inversion Hexpr; subst.
  - match goal with Htemp : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vptr block offset) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hcast : eval_expr _ _ _ _ (Ecast _ _) _ |- _ =>
      inversion Hcast; subst end.
    match goal with Hconst : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hconst; subst end.
    match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
      cbn in Hcast; inversion Hcast; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some answer |- _ =>
      change (option_map Val.of_bool
        (Val.cmpu_bool (Mem.valid_pointer m) Ceq (Vptr block offset)
          (Vint Int.zero)) = Some answer) in Hsem;
      cbn [Val.cmpu_bool] in Hsem;
      repeat match type of Hsem with context [if ?test then _ else _] =>
        destruct test eqn:?; cbn in Hsem; try discriminate end;
      inversion Hsem; subst; discriminate
    end.
    all: match goal with Hl : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion Hl end.
  - match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
Qed.

(** The copy callsite resolves to the real internal vector-copy body; an
    unspecified outside-call effect is not substituted for it. *)
Theorem ibk_retry_copy_calls_real_body : forall version e le m t le' m' out,
  e ! IBM._vec3f_copy = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_copy_call version) t le' m' out ->
  exists args result,
    eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
      (ibk_copy_args version) [tptr tfloat; tptr tfloat] args /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ibk_copy_body version)) args t m' result /\
    le' = le /\ out = Out_normal.
Proof.
  intros version e le m t le' m' out Hlocal Hrun.
  destruct (ibk_selected_copy_resolves version) as (b & Hsymbol & Hfunction).
  destruct (ibk_geometry_cuts_are_generated version) as (_ & _ & _ & _ & Hcall).
  rewrite Hcall in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  match goal with Hexpr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply sce_function_name_value; eauto);
    subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
      b = Some fd) in Hfind; rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  eauto 8.
Qed.

Definition InkTakenRetryBackwardCut : Prop :=
  forall version e le m t le' m' out,
  e ! IBM._vec3f_copy = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' m' out ->
  exists object args result copy_memory copy_trace query_trace,
    t = copy_trace ++ query_trace /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e le m
      ibk_object_read object /\
    eval_exprlist (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBM._t'45 object le) m
      (ibk_copy_args version) [tptr tfloat; tptr tfloat] args /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ibk_copy_body version)) args copy_trace copy_memory result /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBM._t'45 object le) copy_memory (ibk_second_query version)
      query_trace le' m' out.

(** The object read, resolved internal copy, and second floor query are parts
    of the SAME taken branch. The source-object identity and the callee's
    address arguments are still actual reads, not assumed Mario addresses. *)
Theorem ibk_taken_retry_has_real_copy_predecessor : InkTakenRetryBackwardCut.
Proof.
  unfold InkTakenRetryBackwardCut.
  intros version e le m t le' m' out Hlocal Hrun.
  destruct (ibk_geometry_cuts_are_generated version)
    as (_ & _ & Hretry & Hcopy & _).
  destruct (ibk_generated_prefixes_finish_normally version)
    as (_ & _ & Hnormal & _).
  rewrite Hretry in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (copy_le & copy_m & copy_t & query_t & Htrace & Hcopyrun & Hquery).
  rewrite Hcopy in Hcopyrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hcopyrun.
  cce_unroll_loop_free_exec.
  match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _
      (ibk_copy_call version) _ _ _ _ |- _ =>
    destruct (ibk_retry_copy_calls_real_body _ _ _ _ _ _ _ _ Hlocal Hcall)
      as (args & result & Hargs & Hbody & Hle & Hout); subst end.
  do 6 eexists. repeat split; eassumption.
Qed.

(** Backward through the actual Y assignment: it writes exactly the single
    read from src[1], with no addition, animation adjustment or height bonus.
    Reading after X is intentional: proving preservation back to call entry
    requires the destinations to be disjoint from that source cell. *)
Theorem ibk_y_stage_reads_the_value_it_writes :
  forall version ge e le m t le' m' out,
  ocn_exec ge e le m (ibk_copy_y version) t le' m' out ->
  exists destination value,
    eval_expr ge e le m (Evar IBV._dest (tptr tfloat)) destination /\
    eval_expr ge e (PTree.set IBV._t'3 destination le) m ibk_source_y value /\
    ocn_exec ge e
      (PTree.set IBV._t'4 value (PTree.set IBV._t'3 destination le)) m
      ibk_y_store t le' m' out.
Proof.
  intros version ge e le m t le' m' out Hrun.
  rewrite (proj2 (ibk_copy_y_cut_is_generated version)) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec. eauto 8.
Qed.

Definition InkCopyBackwardCut : Prop :=
  forall version ge e le m t le' m' out,
  ocn_exec ge e le m (fn_body (ibk_copy_body version)) t le' m' out ->
  exists y_le y_m after_le after_m destination value pre store suf,
    t = pre ++ (store ++ suf) /\
    ocn_exec ge e le m (ocn_prepend (ibk_copy_before_y version) Sskip)
      pre y_le y_m Out_normal /\
    eval_expr ge e y_le y_m (Evar IBV._dest (tptr tfloat)) destination /\
    eval_expr ge e (PTree.set IBV._t'3 destination y_le) y_m ibk_source_y value /\
    ocn_exec ge e
      (PTree.set IBV._t'4 value (PTree.set IBV._t'3 destination y_le)) y_m
      ibk_y_store store after_le after_m Out_normal /\
    ocn_exec ge e after_le after_m (ibk_copy_after_y version) suf le' m' out.

Theorem ibk_copy_body_has_ordered_y_predecessor : InkCopyBackwardCut.
Proof.
  unfold InkCopyBackwardCut.
  intros version ge e le m t le' m' out Hrun.
  rewrite (proj1 (ibk_copy_y_cut_is_generated version)) in Hrun.
  destruct (ibk_generated_prefixes_finish_normally version)
    as (_ & _ & _ & Hprefix & Hy).
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hprefix Hrun)
    as (y_le & y_m & pre & rest & Htrace & Hpre & Hrest).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hy Hrest)
    as (after_le & after_m & store & suf & Hresttrace & Hstore & Hsuf).
  destruct (ibk_y_stage_reads_the_value_it_writes _ _ _ _ _ _ _ _ _ Hstore)
    as (destination & value & Hdest & Hread & Hwrite).
  do 9 eexists. repeat split; try eassumption. subst. reflexivity.
Qed.

Theorem ibk_y_store_preserves_the_read_single : forall ge e le m t le' m' out height,
  le ! IBV._t'4 = Some (Vsingle height) ->
  ocn_exec ge e le m ibk_y_store t le' m' out ->
  exists block offset,
    eval_lvalue ge e le m ibk_destination_y block offset Full /\
    Mem.store Mfloat32 m block (Ptrofs.unsigned offset) (Vsingle height) = Some m' /\
    t = E0 /\ le' = le /\ out = Out_normal.
Proof.
  intros ge e le m t le' m' out height Hvalue Hrun.
  unfold ibk_y_store in Hrun. inversion Hrun; subst.
  match goal with Hexpr : eval_expr _ _ _ _ (Etempvar _ _) ?value |- _ =>
    assert (value = Vsingle height) by (eapply ocn_temp_value; eauto); subst value end.
  match goal with Hcast : sem_cast _ _ _ _ = Some ?value |- _ =>
    change (Some (Vsingle height) = Some value) in Hcast;
    inversion Hcast; subst value end.
  match goal with Hlv : eval_lvalue _ _ _ _ ibk_destination_y _ _ _ |- _ =>
    pose proof Hlv as Hlocation; unfold ibk_destination_y in Hlv;
    inversion Hlv; subst end.
  match goal with Hstore : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Hstore; subst; try discriminate end.
  all: try match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  eauto 8.
Qed.

Definition InkBackwardExecutionBoundary : Prop :=
  InkGeometryBackwardCut /\ InkTakenRetryBackwardCut /\ InkCopyBackwardCut /\
  (forall ge e le m block offset,
    le ! IBM._t'41 = Some (Vptr block offset) ->
    ~ ocn_test_value ge e le m ibk_null_guard true) /\
  (forall ge e le m t le' m' out height,
    le ! IBV._t'4 = Some (Vsingle height) ->
    ocn_exec ge e le m ibk_y_store t le' m' out ->
    exists block offset,
      eval_lvalue ge e le m ibk_destination_y block offset Full /\
      Mem.store Mfloat32 m block (Ptrofs.unsigned offset) (Vsingle height) = Some m' /\
      t = E0 /\ le' = le /\ out = Out_normal).

Theorem ibk_backward_execution_boundary_checked : InkBackwardExecutionBoundary.
Proof.
  split; [exact ibk_actual_geometry_has_ordered_retry_cut|].
  split; [exact ibk_taken_retry_has_real_copy_predecessor|].
  split; [exact ibk_copy_body_has_ordered_y_predecessor|].
  split; [exact ibk_nonnull_floor_cannot_take_retry|].
  exact ibk_y_store_preserves_the_read_single.
Qed.
