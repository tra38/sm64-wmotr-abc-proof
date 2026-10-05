(** Reached signed Fire Fly Guy size writes and its finite positive prefix.

    The read matches below describe the values at the actual two store cuts.
    They do not grant arbitrary sizes, identify every live actor, or discharge
    the action-entry and intervening receiver-preservation obligations. The
    source cuts come from the actual generated US/JP helper and hitbox setter. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_obj_behaviors_2 jp_obj_behaviors_2
  us_object_helpers jp_object_helpers.
From LessThanOneAPress.Proofs Require Import GameTypes InkCopyCaller
  InkFloorResetExecution InkRawCopyExpressions InkBackwardExecution InkControllerSource
  ObjectContactNecessity ObjectContactReadback ContactConsumerExecution
  EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module FGP := us_obj_behaviors_2.
Module FGH := us_object_helpers.

Definition ifgp_body version := match version with
| VersionUS => us_obj_behaviors_2.f_obj_grow_then_shrink
| VersionJP => jp_obj_behaviors_2.f_obj_grow_then_shrink end.
Definition ifgp_hitbox_body version := match version with
| VersionUS => us_object_helpers.f_obj_set_hitbox
| VersionJP => jp_object_helpers.f_obj_set_hitbox end.
Definition ifgp_growth version := match fn_body (ifgp_body version) with
| Ssequence (Ssequence _ (Ssequence _ (Sifthenelse _ growth _))) _ => growth
| _ => Sskip end.
Definition ifgp_scale_stage version := match ifgp_growth version with
| Ssequence stage _ => stage | _ => Sskip end.
Definition ifgp_velocity_stage version := match ifgp_growth version with
| Ssequence _ (Ssequence stage _) => stage | _ => Sskip end.
Definition ifgp_timer_tail version := match ifgp_growth version with
| Ssequence _ (Ssequence _ tail) => tail | _ => Sskip end.

Definition ifgp_object temporary := Ederef
  (Etempvar temporary (tptr (Tstruct FGP._Object noattr)))
  (Tstruct FGP._Object noattr).
Definition ifgp_header temporary := Efield (ifgp_object temporary)
  FGP._header (Tstruct FGP._ObjectNode noattr).
Definition ifgp_graphics temporary := Efield (ifgp_header temporary)
  FGP._gfx (Tstruct FGP._GraphNodeObject noattr).
Definition ifgp_scales temporary := Efield (ifgp_graphics temporary)
  FGP._scale (tarray tfloat 3).
Definition ifgp_scale_cell temporary := Ederef
  (Ebinop Oadd (ifgp_scales temporary) (Econst_int Int.zero tint)
    (tptr tfloat)) tfloat.
Definition ifgp_scale_sum := Ebinop Oadd
  (Etempvar FGP._t'16 tfloat) (Etempvar FGP._t'17 tfloat) tfloat.
Definition ifgp_scale_store := Sassign (ifgp_scale_cell FGP._t'14) ifgp_scale_sum.
Definition ifgp_delta := Float32.of_bits (Int.repr 1008981770).
Definition ifgp_velocity_difference := Ecast
  (Ebinop Osub (Etempvar FGP._t'13 tfloat)
    (Econst_single ifgp_delta tfloat) tfloat) tfloat.
Definition ifgp_velocity_cell := Ederef
  (Etempvar FGP._scaleVel (tptr tfloat)) tfloat.
Definition ifgp_velocity_store := Sassign ifgp_velocity_cell
  (Etempvar FGP._t'1 tfloat).
Definition ifgp_scale_reads version := ocn_prefix_items 4 (ifgp_scale_stage version).
Definition ifgp_velocity_reads version := match ifgp_velocity_stage version with
| Ssequence reads _ => reads | _ => Sskip end.

Fixpoint ifgp_call_free (s : statement) : bool := match s with
| Sskip | Sset _ _ | Sassign _ _ => true
| Ssequence a b | Sifthenelse _ a b => ifgp_call_free a && ifgp_call_free b
| _ => false end.
Lemma ifgp_call_free_trace : forall ge e le m s t le' m' out,
  ocn_exec ge e le m s t le' m' out ->
  ifgp_call_free s = true -> t = E0.
Proof.
  intros ge e le m s t le' m' out Hrun.
  induction Hrun; cbn; intro Hshape; try discriminate; try reflexivity.
  - apply andb_true_iff in Hshape as [Ha Hb].
    rewrite (IHHrun1 Ha), (IHHrun2 Hb). reflexivity.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; auto.
Qed.

Theorem ifgp_growth_stores_are_generated : forall version,
  ifgp_scale_stage version =
    ocn_prepend (ifgp_scale_reads version) ifgp_scale_store /\
  forallb ibk_normal (ifgp_scale_reads version) = true /\
  ifgp_velocity_stage version =
    Ssequence (ifgp_velocity_reads version) ifgp_velocity_store /\
  ibk_normal (ifgp_velocity_reads version) = true /\
  ifgp_growth version = Ssequence (ifgp_scale_stage version)
    (Ssequence (ifgp_velocity_stage version) (ifgp_timer_tail version)).
Proof. intros []; repeat split; reflexivity. Qed.

Definition ifgp_first_clause version := match fn_body (ifgp_body version) with
| Ssequence clause _ => clause | _ => Sskip end.
Definition ifgp_global_read version := match ifgp_first_clause version with
| Ssequence read _ => read | _ => Sskip end.
Definition ifgp_timer_read version := match ifgp_first_clause version with
| Ssequence _ (Ssequence read _) => read | _ => Sskip end.
Definition ifgp_timer_test version := match ifgp_first_clause version with
| Ssequence _ (Ssequence _ (Sifthenelse test _ _)) => test
| _ => Econst_int Int.zero tint end.
Definition ifgp_recovery version := match ifgp_first_clause version with
| Ssequence _ (Ssequence _ (Sifthenelse _ _ recovery)) => recovery
| _ => Sskip end.
Theorem ifgp_helper_choice_is_generated : forall version,
  fn_vars (ifgp_body version) = [] /\
  fn_body (ifgp_body version) = Ssequence (ifgp_first_clause version)
    (Sreturn (Some (Econst_int Int.zero tint))) /\
  ifgp_first_clause version = Ssequence (ifgp_global_read version)
    (Ssequence (ifgp_timer_read version)
      (Sifthenelse (ifgp_timer_test version) (ifgp_growth version)
        (ifgp_recovery version))) /\
  ibk_normal (ifgp_global_read version) = true /\
  ibk_normal (ifgp_timer_read version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

(** A completed actual helper supplies its reached timer choice. We retain
    both alternatives rather than assuming that every call grows. *)
Theorem ifgp_actual_body_reaches_timer_choice : forall version e le m
    t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ifgp_body version)) t le' m' out ->
  exists choice_le choice_m growing branch_t branch_le branch_m branch_out,
    ocn_test_value (Clight.globalenv (selected_clight_target version)) e
      choice_le choice_m (ifgp_timer_test version) growing /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      choice_le choice_m
      (if growing then ifgp_growth version else ifgp_recovery version)
      branch_t branch_le branch_m branch_out.
Proof.
  intros version e le m t le' m' out Hrun.
  destruct (ifgp_helper_choice_is_generated version)
    as (_ & Hbody & Hclause & Hglobal & Htimer).
  rewrite Hbody in Hrun.
  assert (Hfirst : exists clause_t clause_le clause_m clause_out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ifgp_first_clause version) clause_t clause_le clause_m clause_out).
  { inversion Hrun; subst; eauto 8. }
  destruct Hfirst as (clause_t & clause_le & clause_m & clause_out & Hfirst).
  rewrite Hclause in Hfirst.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hglobal Hfirst)
    as (read_le & read_m & global_t & rest_t & Htrace & Hread & Hrest).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Htimer Hrest)
    as (choice_le & choice_m & timer_t & choice_t & Htrace2 & Hread2 & Hchoice).
  inversion Hchoice; subst.
  do 7 eexists. split; [unfold ocn_test_value; eauto|eassumption].
Qed.

Theorem ifgp_completed_helper_reaches_timer_choice : forall version m
    velocity_pointer shoot_scale end_scale t m' result,
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifgp_body version))
    [velocity_pointer; Vsingle shoot_scale; Vsingle end_scale] t m' result ->
  exists choice_le choice_m growing branch_t branch_le branch_m branch_out,
    ocn_test_value (Clight.globalenv (selected_clight_target version)) empty_env
      choice_le choice_m (ifgp_timer_test version) growing /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
      choice_le choice_m
      (if growing then ifgp_growth version else ifgp_recovery version)
      branch_t branch_le branch_m branch_out.
Proof.
  intros version m velocity_pointer shoot_scale end_scale t m' result Hcall.
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite (proj1 (ifgp_helper_choice_is_generated version)) in Halloc;
    inversion Halloc; subst; clear Halloc end.
  eapply ifgp_actual_body_reaches_timer_choice; eauto.
Qed.

Lemma ifgp_selected_scale_fields : forall version,
  let ce := genv_cenv (Clight.globalenv (selected_clight_target version)) in
  ibcc_field_ok ce FGP._Object FGP._header 0 = true /\
  ibcc_field_ok ce FGP._ObjectNode FGP._gfx 0 = true /\
  ibcc_field_ok ce FGP._GraphNodeObject FGP._scale 44 = true.
Proof.
  intro version. cbn zeta.
  change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
      FGP._Object FGP._header 0 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
      FGP._ObjectNode FGP._gfx 0 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
      FGP._GraphNodeObject FGP._scale 44 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Lemma ifgp_scales_value : forall version e le m temporary ob oo answer,
  le ! temporary = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ifgp_scales temporary) answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 44)).
Proof.
  intros version e le m temporary ob oo answer Htemp Hread.
  destruct (ifgp_selected_scale_fields version) as (Hobj & Hheader & Hscale).
  assert (Hh : forall value,
    eval_expr (Clight.globalenv (selected_clight_target version)) e le m
      (ifgp_header temporary) value -> value = Vptr ob oo).
  { intros value Hv. unfold ifgp_header in Hv.
    pose proof (ibcc_aggregate_field _ _ _ _ (ifgp_object temporary)
      FGP._Object FGP._header (Tstruct FGP._ObjectNode noattr) ob oo 0 value
      eq_refl ltac:(intros; eapply ibcc_deref_struct; eauto) Hobj
      ltac:(right; reflexivity) Hv) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (Hg : forall value,
    eval_expr (Clight.globalenv (selected_clight_target version)) e le m
      (ifgp_graphics temporary) value -> value = Vptr ob oo).
  { intros value Hv. unfold ifgp_graphics in Hv.
    pose proof (ibcc_aggregate_field _ _ _ _ (ifgp_header temporary)
      FGP._ObjectNode FGP._gfx (Tstruct FGP._GraphNodeObject noattr) ob oo 0 value
      eq_refl Hh Hheader ltac:(right; reflexivity) Hv) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  unfold ifgp_scales in Hread.
  exact (ibcc_aggregate_field _ _ _ _ (ifgp_graphics temporary)
    FGP._GraphNodeObject FGP._scale (tarray tfloat 3) ob oo 44 answer
    eq_refl Hg Hscale (or_introl eq_refl) Hread).
Qed.

Lemma ifgp_scale_location : forall version e le m temporary ob oo b ofs bf,
  le ! temporary = Some (Vptr ob oo) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (ifgp_scale_cell temporary) b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr 44) /\ bf = Full.
Proof.
  intros version e le m temporary ob oo b ofs bf Htemp Hl.
  unfold ifgp_scale_cell in Hl.
  destruct (ifr_array_index_location _ _ _ _ (ifgp_scales temporary) 0 ob
    (Ptrofs.add oo (Ptrofs.repr 44)) b ofs bf eq_refl
    ltac:(intros; eapply ifgp_scales_value; eauto) Hl) as (-> & -> & ->).
  change (ptrofs_of_int Signed (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. repeat split; reflexivity.
Qed.

Lemma ifgp_scale_sum_value : forall ge e le m scale velocity answer,
  le ! FGP._t'16 = Some (Vsingle scale) ->
  le ! FGP._t'17 = Some (Vsingle velocity) ->
  eval_expr ge e le m ifgp_scale_sum answer ->
  answer = Vsingle (Float32.add scale velocity).
Proof.
  intros ge e le m scale velocity answer Hscale Hvelocity Hr.
  unfold ifgp_scale_sum in Hr. inversion Hr; subst.
  - match goal with H : eval_expr _ _ _ _ (Etempvar FGP._t'16 _) ?v |- _ =>
      assert (v = Vsingle scale) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Etempvar FGP._t'17 _) ?v |- _ =>
      assert (v = Vsingle velocity) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn in H; inversion H; reflexivity end.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

(** This proves the actual reached scale store, including its real graphics
    address. No assumption identifies negative scale with its absolute value. *)
Theorem ifgp_actual_scale_store : forall version e le m ob oo scale velocity
    t le' m' out,
  le ! FGP._t'14 = Some (Vptr ob oo) ->
  le ! FGP._t'16 = Some (Vsingle scale) ->
  le ! FGP._t'17 = Some (Vsingle velocity) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ifgp_scale_store t le' m' out ->
  Mem.store Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 44)))
    (Vsingle (Float32.add scale velocity)) = Some m' /\
  le' = le /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m ob oo scale velocity t le' m' out Ho Hs Hv Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt, ifgp_scale_store in Hrun.
  inversion Hrun; subst; clear Hrun.
  match goal with H : eval_lvalue _ _ _ _ (ifgp_scale_cell _) _ _ _ |- _ =>
    destruct (ifgp_scale_location _ _ _ _ _ _ _ _ _ _ Ho H) as (-> & -> & ->) end.
  match goal with H : eval_expr _ _ _ _ ifgp_scale_sum ?v |- _ =>
    assert (v = Vsingle (Float32.add scale velocity))
      by (eapply ifgp_scale_sum_value; eauto); subst v end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ =>
    cbn in H; inversion H; subst end.
  repeat split; try reflexivity; assumption.
Qed.

Lemma ifgp_velocity_difference_value : forall ge e le m velocity answer,
  le ! FGP._t'13 = Some (Vsingle velocity) ->
  eval_expr ge e le m ifgp_velocity_difference answer ->
  answer = Vsingle (Float32.sub velocity ifgp_delta).
Proof.
  intros ge e le m velocity answer Hv Hr.
  unfold ifgp_velocity_difference in Hr. inversion Hr; subst.
  - match goal with H : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
      inversion H; subst; clear H end.
    + match goal with H : eval_expr _ _ _ _ (Etempvar FGP._t'13 _) ?v |- _ =>
        assert (v = Vsingle velocity) by (eapply ocn_temp_value; eauto); subst v end.
      match goal with H : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ =>
        inversion H; subst; clear H;
        try match goal with Hl : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ =>
          inversion Hl end end.
      match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
        cbn in H; inversion H; subst; clear H end.
      repeat match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
        cbn in H; inversion H; subst; clear H end.
      reflexivity.
    + match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
  - match goal with H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
Qed.

Theorem ifgp_actual_velocity_store : forall version e le m vb vo velocity
    t le' m' out,
  le ! FGP._scaleVel = Some (Vptr vb vo) ->
  le ! FGP._t'1 = Some (Vsingle (Float32.sub velocity ifgp_delta)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ifgp_velocity_store t le' m' out ->
  Mem.store Mfloat32 m vb (Ptrofs.unsigned vo)
    (Vsingle (Float32.sub velocity ifgp_delta)) = Some m' /\
  le' = le /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m vb vo velocity t le' m' out Hp Hv Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt, ifgp_velocity_store in Hrun.
  inversion Hrun; subst; clear Hrun.
  match goal with H : eval_lvalue _ _ _ _ ifgp_velocity_cell _ _ _ |- _ =>
    unfold ifgp_velocity_cell in H; inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ (Etempvar FGP._scaleVel _) ?v |- _ =>
    assert (v = Vptr vb vo) as Hpointer by (eapply ocn_temp_value; eauto);
    inversion Hpointer; subst; clear Hpointer end.
  match goal with H : eval_expr _ _ _ _ (Etempvar FGP._t'1 _) ?v |- _ =>
    assert (v = Vsingle (Float32.sub velocity ifgp_delta))
      by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ =>
    cbn in H; inversion H; subst end.
  repeat split; try reflexivity; assumption.
Qed.

(** The two stores are extracted from one actual executed growth branch.
    No read agreement between them is supplied by this decomposition. *)
Theorem ifgp_executed_growth_reaches_both_stores : forall version e le m
    t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifgp_growth version) t le' m' out ->
  exists scale_le scale_m scale_after_le scale_after_m velocity_le velocity_m
    velocity_after_le velocity_after_m,
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      scale_le scale_m ifgp_scale_store E0 scale_after_le scale_after_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      velocity_le velocity_m ifgp_velocity_store E0
      velocity_after_le velocity_after_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      velocity_after_le velocity_after_m (ifgp_timer_tail version)
      t le' m' out.
Proof.
  intros version e le m t le' m' out Hrun.
  destruct (ifgp_growth_stores_are_generated version)
    as (Hscale & Hreads & Hvelocity & HvelocityReads & Hgrowth).
  rewrite Hgrowth in Hrun.
  assert (HnormalScale : ibk_normal (ifgp_scale_stage version) = true)
    by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HnormalScale Hrun)
    as (scale_after_le & scale_after_m & scale_t & rest_t & Htrace & HscaleRun & Hrest).
  rewrite Hscale in HscaleRun.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hreads HscaleRun)
    as (scale_le & scale_m & reads_t & store_t & HscaleTrace & HscaleReads & HscaleStore).
  assert (HnormalVelocity : ibk_normal (ifgp_velocity_stage version) = true)
    by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HnormalVelocity Hrest)
    as (velocity_after_le & velocity_after_m & velocity_t & tail_t &
      HrestTrace & HvelocityRun & Htail).
  rewrite Hvelocity in HvelocityRun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HvelocityReads HvelocityRun)
    as (velocity_le & velocity_m & velocity_reads_t & velocity_store_t &
      HvelocityTrace & HvelocityReadsRun & HvelocityStore).
  assert (scale_t = E0 /\ rest_t = t) as [HscaleE HrestT].
  { assert (HscaleEmpty : scale_t = E0).
    { eapply ifgp_call_free_trace; [exact HscaleRun|].
      destruct version; reflexivity. }
    split; [exact HscaleEmpty|].
    rewrite HscaleEmpty in Htrace. simpl in Htrace. symmetry; exact Htrace. }
  assert (velocity_t = E0).
  { eapply ifgp_call_free_trace; [exact HvelocityRun|].
    destruct version; reflexivity. }
  rewrite HscaleE in HscaleTrace.
  rewrite HrestT in HrestTrace.
  rewrite H in HvelocityTrace, HrestTrace.
  symmetry in HscaleTrace. apply app_eq_nil in HscaleTrace as [-> ->].
  symmetry in HvelocityTrace. apply app_eq_nil in HvelocityTrace as [-> ->].
  simpl in HrestTrace. subst tail_t.
  exists scale_le, scale_m, scale_after_le, scale_after_m, velocity_le,
    velocity_m, velocity_after_le, velocity_after_m.
  repeat split; assumption.
Qed.

Definition ifgp_f32 bits := Float32.of_bits (Int.repr bits).
Definition ifgp_prefix_scale_bits : list Z :=
  [1069547520; 1070050836; 1070470266; 1070805810; 1071057468;
   1071225240; 1071309126; 1071309126].
Definition ifgp_prefix_velocity_bits : list Z :=
  [1031127695; 1028443340; 1025758986; 1022739087; 1017370378;
   1008981770; 0; 3156465418].
Definition ifgp_entry_pairs := combine
  (map ifgp_f32 (firstn 7 ifgp_prefix_scale_bits))
  (map ifgp_f32 (firstn 7 ifgp_prefix_velocity_bits)).
Definition ifgp_next_pairs := combine
  (map ifgp_f32 (skipn 1 ifgp_prefix_scale_bits))
  (map ifgp_f32 (skipn 1 ifgp_prefix_velocity_bits)).
Definition ifgp_prefix_step pair :=
  (Float32.add (fst pair) (snd pair), Float32.sub (snd pair) ifgp_delta).
Theorem ifgp_positive_prefix_bits_checked :
  map (fun pair =>
    (Int.unsigned (Float32.to_bits (fst (ifgp_prefix_step pair))),
     Int.unsigned (Float32.to_bits (snd (ifgp_prefix_step pair))))) ifgp_entry_pairs =
  combine (skipn 1 ifgp_prefix_scale_bits) (skipn 1 ifgp_prefix_velocity_bits).
Proof. vm_compute; reflexivity. Qed.

Definition ifgp_height_expression := Ebinop Omul
  (Etempvar FGH._t'7 tfloat) (Etempvar FGH._t'8 tshort) tfloat.
Definition ifgp_height_store := Sassign
  (ics_field FGH._obj FGH._Object FGH._hitboxHeight tfloat)
  ifgp_height_expression.
Fixpoint ifgp_find_field_store field statement := match statement with
| Sassign (Efield _ name _) _ => if Pos.eqb field name then Some statement else None
| Ssequence a b | Sifthenelse _ a b =>
    match ifgp_find_field_store field a with Some s => Some s
    | None => ifgp_find_field_store field b end
| _ => None end.
Theorem ifgp_height_store_is_generated : forall version,
  ifgp_find_field_store FGH._hitboxHeight (fn_body (ifgp_hitbox_body version)) =
    Some ifgp_height_store.
Proof. intros []; reflexivity. Qed.

Definition ifgp_height_stage version := match fn_body (ifgp_hitbox_body version) with
| Ssequence _ (Ssequence _ (Ssequence height _)) => height
| _ => Sskip end.
Definition ifgp_before_height version := ocn_prefix_items 2
  (fn_body (ifgp_hitbox_body version)).
Definition ifgp_after_height version := match fn_body (ifgp_hitbox_body version) with
| Ssequence _ (Ssequence _ (Ssequence _ tail)) => tail
| _ => Sskip end.
Definition ifgp_height_reads version := ocn_prefix_items 2 (ifgp_height_stage version).
Theorem ifgp_height_cuts_are_generated : forall version,
  fn_vars (ifgp_hitbox_body version) = [] /\
  fn_body (ifgp_hitbox_body version) =
    ocn_prepend (ifgp_before_height version)
      (Ssequence (ifgp_height_stage version) (ifgp_after_height version)) /\
  forallb ibk_normal (ifgp_before_height version) = true /\
  ifgp_height_stage version =
    ocn_prepend (ifgp_height_reads version) ifgp_height_store /\
  forallb ibk_normal (ifgp_height_reads version) = true /\
  ibk_normal (ifgp_height_stage version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem ifgp_completed_hitbox_reaches_height_store : forall version m
    object_pointer hitbox_pointer t m' result,
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifgp_hitbox_body version)) [object_pointer; hitbox_pointer]
    t m' result ->
  exists store_le store_m store_t store_after_le store_after_m,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
      store_le store_m ifgp_height_store store_t store_after_le
      store_after_m Out_normal.
Proof.
  intros version m object_pointer hitbox_pointer t m' result Hcall.
  destruct (ifgp_height_cuts_are_generated version)
    as (Hvars & Hbody & Hbefore & Hstage & Hreads & Hnormal).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hbefore Hr)
      as (height_le & height_m & before_t & height_t & Htrace & Hpre & Hrest) end.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (height_after_le & height_after_m & stage_t & tail_t & Htrace2 & HstageRun & Htail).
  rewrite Hstage in HstageRun.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hreads HstageRun)
    as (store_le & store_m & read_t & store_t & Htrace3 & Hread & Hstore).
  do 5 eexists. exact Hstore.
Qed.

Lemma ifgp_selected_height_field : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    FGH._Object FGH._hitboxHeight 508 = true.
Proof.
  intro version. change (ibcc_field_ok
    (prog_comp_env (selected_clight_target version))
      FGH._Object FGH._hitboxHeight 508 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Theorem ifgp_actual_hitbox_height_store : forall version e le m ob oo scale_y
    t le' m' out,
  le ! FGH._obj = Some (Vptr ob oo) ->
  le ! FGH._t'7 = Some (Vsingle scale_y) ->
  le ! FGH._t'8 = Some (Vint (Int.repr 60)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ifgp_height_store t le' m' out ->
  Mem.store Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508)))
    (Vsingle (Float32.mul scale_y (Float32.of_int (Int.repr 60)))) = Some m' /\
  le' = le /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m ob oo scale_y t le' m' out Ho Hs Hh Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt, ifgp_height_store in Hrun.
  inversion Hrun; subst; clear Hrun.
  unfold ics_field in H1.
  destruct (ibcc_field_location _ _ _ _
    (Ederef (Etempvar FGH._obj (tptr (Tstruct FGH._Object noattr)))
      (Tstruct FGH._Object noattr)) FGH._Object FGH._hitboxHeight
    tfloat ob oo 508 _ _ _ eq_refl
    ltac:(intros; eapply ibcc_deref_struct; eauto)
    (ifgp_selected_height_field version) H1) as (-> & -> & ->).
  match goal with H : eval_expr _ _ _ _ ifgp_height_expression _ |- _ =>
    unfold ifgp_height_expression in H; inversion H; subst; clear H end.
  - match goal with H : eval_expr _ _ _ _ (Etempvar FGH._t'7 _) ?v |- _ =>
      assert (v = Vsingle scale_y) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Etempvar FGH._t'8 _) ?v |- _ =>
      assert (v = Vint (Int.repr 60)) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn in H; inversion H; subst; clear H end.
    match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
      cbn in H; inversion H; subst end.
    match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ =>
      inversion H; subst; try discriminate end.
    match goal with H : access_mode _ = By_value _ |- _ =>
      cbn in H; inversion H; subst end.
    repeat split; try reflexivity; assumption.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

(** Scale Y uses the previous X value; the certificate includes every prefix
    value, rather than identifying it with the new X at the radius store. *)
Theorem ifgp_positive_prefix_height_ceiling_checked :
  forallb (fun scale_y => Float32.cmp Cle
    (Float32.mul scale_y (Float32.of_int (Int.repr 60)))
    (ifgp_f32 1120744242))
    (map ifgp_f32 ifgp_prefix_scale_bits) = true.
Proof. vm_compute; reflexivity. Qed.
