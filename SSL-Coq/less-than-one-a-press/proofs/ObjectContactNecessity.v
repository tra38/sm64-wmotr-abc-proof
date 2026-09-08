(** Hardest obligation 2: necessary checks in the ACTUAL object-contact body.
    No elevator/pole crossing, floor ownership, finite-coordinate hypothesis,
    or harmless sqrtf effect is assumed here. The theorem follows a successful
    execution of the selected US/JP body to its real comparison checkpoints.
    Connecting a star award to this call and projecting the call's reads into
    the reported collision sample remain separate live-execution obligations. *)
From Coq Require Import Bool List Lia ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes CollisionRegions
  Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ocn_exec := ClightBigstep.Clight2.exec_stmt.

(** Only these syntactic prefixes can precede the checked tests. Calls can
    have effects, but a completed call statement itself cannot return from
    the enclosing function. This is NOT a frame specification for a call. *)
Fixpoint ocn_normal_prefix (s : statement) : bool := match s with
| Sskip | Sset _ _ | Scall _ _ _ => true
| Ssequence a b => ocn_normal_prefix a && ocn_normal_prefix b
| _ => false end.

Lemma ocn_normal_prefix_outcome : forall ge e le m s t le' m' out,
  ocn_normal_prefix s = true -> ocn_exec ge e le m s t le' m' out ->
  out = Out_normal.
Proof.
  intros ge e le m s t le' m' out Hshape Hrun.
  induction Hrun; cbn in Hshape; try discriminate; try reflexivity.
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    exfalso. apply H. auto.
Qed.

Fixpoint ocn_prefix_items (n : nat) (s : statement) : list statement :=
  match n, s with
  | S rest, Ssequence a b => a :: ocn_prefix_items rest b
  | _, _ => [] end.
Fixpoint ocn_prepend (items : list statement) (tail : statement) : statement :=
  match items with [] => tail | a :: rest => Ssequence a (ocn_prepend rest tail) end.

Lemma ocn_successful_prefix_decomposition : forall ge e items tail le m t le' m' out,
  forallb ocn_normal_prefix items = true ->
  ocn_exec ge e le m (ocn_prepend items tail) t le' m' out ->
  exists middle memory prefix_trace suffix_trace,
    t = prefix_trace ++ suffix_trace /\
    ocn_exec ge e le m (ocn_prepend items Sskip)
      prefix_trace middle memory Out_normal /\
    ocn_exec ge e middle memory tail suffix_trace le' m' out.
Proof.
  intros ge e items. induction items as [|head rest IH];
    intros tail le m t le' m' out Hshape Hrun.
  - exists le, m, E0, t. split; [reflexivity |].
    split; [apply exec_Sskip | exact Hrun].
  - cbn in Hshape. apply andb_true_iff in Hshape as [Hhead Hrest].
    cbn [ocn_prepend] in Hrun. inversion Hrun; subst.
    + match goal with
      | Hr : ClightBigstep.exec_stmt _ _ _ _ _ (ocn_prepend rest tail) _ _ _ _ |- _ =>
          destruct (IH _ _ _ _ _ _ _ Hrest Hr)
            as (middle & memory & pre & suf & Htrace & Hprefix & Hsuffix)
      end.
      exists middle, memory, (t1 ++ pre), suf. split.
      * subst. apply app_assoc.
      * split; [cbn [ocn_prepend]; eapply exec_Sseq_1; eauto | exact Hsuffix].
    + match goal with
      | Hr : ClightBigstep.exec_stmt _ _ _ _ _ head _ _ _ _ |- _ =>
          pose proof (ocn_normal_prefix_outcome _ _ _ _ _ _ _ _ _ Hhead Hr)
      end. contradiction.
Qed.

Definition ocn_before_radius version := ocn_prefix_items 7 (fn_body (rank12b_body version)).
Definition ocn_before_vertical version := ocn_prefix_items 2 (rank12b_inside_radius version).
Definition ocn_vertical_tail version := rank12b_drop_sequences 2 (rank12b_inside_radius version).
Definition ocn_after_vertical version := rank12b_drop_sequences 2 (ocn_vertical_tail version).
Definition ocn_above_test := Ebinop Ogt (Etempvar RC._sp3C tfloat)
  (Etempvar RC._sp1C tfloat) tint.
Definition ocn_below_test := Ebinop Olt (Etempvar RC._sp20 tfloat)
  (Etempvar RC._sp38 tfloat) tint.

Theorem ocn_generated_contact_checkpoints : forall version,
  fn_body (rank12b_body version) =
    ocn_prepend (ocn_before_radius version) (rank12b_after_sqrt version) /\
  forallb ocn_normal_prefix (ocn_before_radius version) = true /\
  rank12b_inside_radius version =
    ocn_prepend (ocn_before_vertical version) (ocn_vertical_tail version) /\
  forallb ocn_normal_prefix (ocn_before_vertical version) = true /\
  ocn_vertical_tail version =
    Ssequence (Sifthenelse ocn_above_test rank12b_return_zero Sskip)
      (Ssequence (Sifthenelse ocn_below_test rank12b_return_zero Sskip)
        (ocn_after_vertical version)).
Proof. intros []; repeat split; reflexivity. Qed.

Definition ocn_test_value ge e le m test answer : Prop :=
  exists value, eval_expr ge e le m test value /\
    bool_val value (typeof test) m = Some answer.

Lemma ocn_const_int_value : forall ge e le m n ty value,
  eval_expr ge e le m (Econst_int n ty) value -> value = Vint n.
Proof.
  intros ge e le m n ty value Hexpr. inversion Hexpr; subst; try reflexivity.
  match goal with Hl : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ =>
    inversion Hl end.
Qed.

Lemma ocn_return_zero_outcome : forall ge e le m t le' m' out,
  ocn_exec ge e le m rank12b_return_zero t le' m' out ->
  out = Out_return (Some (Vint Int.zero, tint)).
Proof.
  intros ge e le m t le' m' out Hrun.
  unfold rank12b_return_zero in Hrun. inversion Hrun; subst.
  match goal with Hexpr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hexpr; subst; reflexivity end.
Qed.

Lemma ocn_rejecting_guard_must_pass : forall ge e le m test tail t le' m',
  ocn_exec ge e le m
    (Ssequence (Sifthenelse test rank12b_return_zero Sskip) tail)
    t le' m' (Out_return (Some (Vint Int.one, tint))) ->
  ocn_test_value ge e le m test false /\
  ocn_exec ge e le m tail t le' m' (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros ge e le m test tail t le' m' Hrun.
  inversion Hrun; subst.
  - match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
      inversion Hg; subst end.
    destruct b; cbn beta iota in *.
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ rank12b_return_zero _ _ _ _ |- _ =>
        pose proof (ocn_return_zero_outcome _ _ _ _ _ _ _ _ Hr); discriminate end.
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion Hr; subst end.
      split; [unfold ocn_test_value; eauto | assumption].
  - match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
      inversion Hg; subst end.
    destruct b; cbn beta iota in *.
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ rank12b_return_zero _ _ _ _ |- _ =>
        pose proof (ocn_return_zero_outcome _ _ _ _ _ _ _ _ Hr) as Hbad;
        discriminate Hbad end.
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion Hr end.
Qed.

Lemma ocn_successful_radius_tail : forall version ge e le m t le' m',
  ocn_exec ge e le m (rank12b_after_sqrt version) t le' m'
    (Out_return (Some (Vint Int.one, tint))) ->
  ocn_test_value ge e le m rank12b_radius_test true /\
  ocn_exec ge e le m (rank12b_inside_radius version) t le' m'
    (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros version ge e le m t le' m' Hrun.
  rewrite (proj1 (rank12b_generated_radius_tail_is_exact version)) in Hrun.
  inversion Hrun; subst.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ rank12b_return_zero _ _ _ _ |- _ =>
      pose proof (ocn_return_zero_outcome _ _ _ _ _ _ _ _ Hr) as Hbad;
      discriminate Hbad end.
  - match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
      inversion Hg; subst end.
    destruct b; cbn beta iota in *.
    + split; [unfold ocn_test_value; eauto | assumption].
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion Hr end.
Qed.

Definition ocn_ordered_contact_checkpoints version environment locals memory
    trace final_locals final_memory radius_locals radius_memory vertical_locals
    vertical_memory input_trace height_trace registration_trace : Prop :=
    trace = input_trace ++ (height_trace ++ registration_trace) /\
    ocn_exec (Clight.globalenv (selected_clight_target version))
      environment locals memory (ocn_prepend (ocn_before_radius version) Sskip)
      input_trace radius_locals radius_memory Out_normal /\
    ocn_test_value (Clight.globalenv (selected_clight_target version))
      environment radius_locals radius_memory rank12b_radius_test true /\
    ocn_exec (Clight.globalenv (selected_clight_target version))
      environment radius_locals radius_memory
      (ocn_prepend (ocn_before_vertical version) Sskip)
      height_trace vertical_locals vertical_memory Out_normal /\
    ocn_test_value (Clight.globalenv (selected_clight_target version))
      environment vertical_locals vertical_memory ocn_above_test false /\
    ocn_test_value (Clight.globalenv (selected_clight_target version))
      environment vertical_locals vertical_memory ocn_below_test false /\
    ocn_exec (Clight.globalenv (selected_clight_target version))
      environment vertical_locals vertical_memory (ocn_after_vertical version)
      registration_trace final_locals final_memory
      (Out_return (Some (Vint Int.one, tint))).

(** The witnesses are actual, ordered subexecutions of ONE successful call.
    In particular, the vertical checks are at the same memory/local snapshot;
    neither walls nor floor membership is assumed as a substitute for them. *)
Theorem ocn_success_requires_ordered_contact_tests :
  forall version environment locals memory trace final_locals final_memory,
  ocn_exec (Clight.globalenv (selected_clight_target version))
    environment locals memory (fn_body (rank12b_body version))
    trace final_locals final_memory (Out_return (Some (Vint Int.one, tint))) ->
  exists radius_locals radius_memory vertical_locals vertical_memory
      input_trace height_trace registration_trace,
    ocn_ordered_contact_checkpoints version environment locals memory trace
      final_locals final_memory radius_locals radius_memory vertical_locals
      vertical_memory input_trace height_trace registration_trace.
Proof.
  intros version environment locals memory trace final_locals final_memory Hrun.
  destruct (ocn_generated_contact_checkpoints version)
    as (Hbody & Hprefix & Hinside & Hheights & Hvertical).
  rewrite Hbody in Hrun.
  destruct (ocn_successful_prefix_decomposition _ _ _ _ _ _ _ _ _ _ Hprefix Hrun)
    as (rl & rm & it & rest & Htrace & Hinput & Hradius).
  destruct (ocn_successful_radius_tail _ _ _ _ _ _ _ _ Hradius) as [Hr Hinside_run].
  rewrite Hinside in Hinside_run.
  destruct (ocn_successful_prefix_decomposition _ _ _ _ _ _ _ _ _ _ Hheights Hinside_run)
    as (vl & vm & ht & rt & Hrest & Hheight & Hguards).
  rewrite Hvertical in Hguards.
  destruct (ocn_rejecting_guard_must_pass _ _ _ _ _ _ _ _ _ Hguards) as [Ha Hnext].
  destruct (ocn_rejecting_guard_must_pass _ _ _ _ _ _ _ _ _ Hnext) as [Hb Hregister].
  exists rl, rm, vl, vm, it, ht, rt.
  unfold ocn_ordered_contact_checkpoints. subst.
  repeat split; try assumption; reflexivity.
Qed.

(** The remaining readback boundary is six explicit LOCAL values at the
    derived checkpoints, not an assumed collision outcome or gate crossing.
    Establishing it from live Object reads includes sqrtf's numeric result
    and the pre-/post-call height history. No external effect is silently
    assigned by this definition. *)
Definition ocn_samples_match_phase phase radius_locals vertical_locals : Prop :=
  radius_locals ! RC._collisionRadius = Some (Vsingle
    (Float32.add (hitbox_radius (collision_mario_hitbox phase))
      (hitbox_radius (collision_target_hitbox phase)))) /\
  radius_locals ! RC._distance = Some (Vsingle (horizontal_distance
    (collision_mario_position phase) (collision_target_position phase))) /\
  vertical_locals ! RC._sp3C = Some (Vsingle (hitbox_bottom
    (collision_mario_position phase) (collision_mario_hitbox phase))) /\
  vertical_locals ! RC._sp1C = Some (Vsingle (hitbox_top
    (collision_target_position phase) (collision_target_hitbox phase))) /\
  vertical_locals ! RC._sp20 = Some (Vsingle (hitbox_top
    (collision_mario_position phase) (collision_mario_hitbox phase))) /\
  vertical_locals ! RC._sp38 = Some (Vsingle (hitbox_bottom
    (collision_target_position phase) (collision_target_hitbox phase))).

Lemma ocn_temp_value : forall ge e le m id ty value expected,
  eval_expr ge e le m (Etempvar id ty) value ->
  le ! id = Some expected -> value = expected.
Proof.
  intros ge e le m id ty value expected Hexpr Hread.
  inversion Hexpr; subst; try congruence.
  match goal with Hl : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ =>
    inversion Hl end.
Qed.

Lemma ocn_float_test_is_the_actual_comparison : forall ge e le m left right
    (greater : bool) a b answer,
  le ! left = Some (Vsingle a) -> le ! right = Some (Vsingle b) ->
  ocn_test_value ge e le m
    (Ebinop (if greater then Ogt else Olt)
      (Etempvar left tfloat) (Etempvar right tfloat) tint) answer ->
  Float32.cmp (if greater then Cgt else Clt) a b = answer.
Proof.
  intros ge e le m left right greater a b answer Hl Hr [value [Hexpr Hbool]].
  inversion Hexpr; subst.
  - match goal with
    | Ha : eval_expr _ _ _ _ (Etempvar left _) ?va,
      Hb : eval_expr _ _ _ _ (Etempvar right _) ?vb |- _ =>
      assert (va = Vsingle a) by (eapply ocn_temp_value; eauto);
      assert (vb = Vsingle b) by (eapply ocn_temp_value; eauto); subst
    end.
    destruct greater; cbn beta iota in *.
    + match goal with Hsem : sem_binary_operation _ Ogt _ _ _ _ _ = Some value |- _ =>
        change (Some (Val.of_bool (Float32.cmp Cgt a b)) = Some value) in Hsem;
        injection Hsem as Hvalue; rewrite <- Hvalue in Hbool
      end.
      destruct (Float32.cmp Cgt a b); cbn in Hbool;
        vm_compute in Hbool; congruence.
    + match goal with Hsem : sem_binary_operation _ Olt _ _ _ _ _ = Some value |- _ =>
        change (Some (Val.of_bool (Float32.cmp Clt a b)) = Some value) in Hsem;
        injection Hsem as Hvalue; rewrite <- Hvalue in Hbool
      end.
      destruct (Float32.cmp Clt a b); cbn in Hbool;
        vm_compute in Hbool; congruence.
  - match goal with Hlvalue : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ =>
      inversion Hlvalue end.
Qed.

Theorem ocn_actual_tests_imply_reported_overlap : forall version environment
    radius_locals radius_memory vertical_locals vertical_memory phase,
  ocn_samples_match_phase phase radius_locals vertical_locals ->
  ocn_test_value (Clight.globalenv (selected_clight_target version))
    environment radius_locals radius_memory rank12b_radius_test true ->
  ocn_test_value (Clight.globalenv (selected_clight_target version))
    environment vertical_locals vertical_memory ocn_above_test false ->
  ocn_test_value (Clight.globalenv (selected_clight_target version))
    environment vertical_locals vertical_memory ocn_below_test false ->
  hitboxes_overlap (collision_mario_position phase) (collision_mario_hitbox phase)
    (collision_target_position phase) (collision_target_hitbox phase) = true.
Proof.
  intros version environment rl rm vl vm phase
    (Hradius & Hdistance & HbottomA & HtopB & HtopA & HbottomB) Hr Ha Hb.
  pose proof (ocn_float_test_is_the_actual_comparison _ _ _ _ _ _ true _ _ _
    Hradius Hdistance Hr) as R.
  pose proof (ocn_float_test_is_the_actual_comparison _ _ _ _ _ _ true _ _ _
    HbottomA HtopB Ha) as A.
  pose proof (ocn_float_test_is_the_actual_comparison _ _ _ _ _ _ false _ _ _
    HtopA HbottomB Hb) as B.
  cbn beta iota in R, A, B.
  change Cgt with (swap_comparison Clt) in R, A.
  rewrite Float32.cmp_swap in R.
  rewrite Float32.cmp_swap in A.
  unfold hitboxes_overlap. rewrite R, A, B. reflexivity.
Qed.

Definition ObjectContactReadbackObligation version environment locals memory
    trace final_locals final_memory phase : Prop :=
  forall rl rm vl vm it ht rt,
    ocn_ordered_contact_checkpoints version environment locals memory trace
      final_locals final_memory rl rm vl vm it ht rt ->
    ocn_samples_match_phase phase rl vl.

Theorem ocn_successful_body_requires_reported_overlap :
  forall version environment locals memory trace final_locals final_memory phase,
  ocn_exec (Clight.globalenv (selected_clight_target version))
    environment locals memory (fn_body (rank12b_body version))
    trace final_locals final_memory (Out_return (Some (Vint Int.one, tint))) ->
  ObjectContactReadbackObligation version environment locals memory trace
    final_locals final_memory phase ->
  hitboxes_overlap (collision_mario_position phase) (collision_mario_hitbox phase)
    (collision_target_position phase) (collision_target_hitbox phase) = true.
Proof.
  intros version environment locals memory trace final_locals final_memory phase Hrun Hread.
  destruct (ocn_success_requires_ordered_contact_tests _ _ _ _ _ _ _ Hrun)
    as (rl & rm & vl & vm & it & ht & rt & Hchecks).
  pose proof (Hread _ _ _ _ _ _ _ Hchecks) as Hsamples.
  destruct Hchecks as (_ & _ & Hr & _ & Ha & Hb & _).
  eapply ocn_actual_tests_imply_reported_overlap; eauto.
Qed.

Definition ocn_other_phase_facts phase : Prop :=
  object_ref_equal (collision_mario_ref phase) (collision_player_ref phase) /\
  collision_area phase = pyramid_area_id /\
  collision_after_platform_displacement phase = true /\
  collision_before_behavior_update phase = true /\
  collision_instant_warp_pending phase = false /\
  Int.lt (collision_mario_count_before phase) (Int.repr 4) = true /\
  Int.lt (collision_target_count_before phase) (Int.repr 4) = true /\
  collision_pair_registered phase = true.

(** This constructs the exact predicate consumed by StarCollection/HiddenStar;
    its geometric member is DERIVED from the real body, not supplied as data.
    The other phase facts and six-value readback are visibly still required. *)
Theorem ocn_successful_body_supplies_collision_phase_overlap :
  forall version environment locals memory trace final_locals final_memory phase,
  ocn_exec (Clight.globalenv (selected_clight_target version))
    environment locals memory (fn_body (rank12b_body version))
    trace final_locals final_memory (Out_return (Some (Vint Int.one, tint))) ->
  ObjectContactReadbackObligation version environment locals memory trace
    final_locals final_memory phase ->
  ocn_other_phase_facts phase -> collision_phase_overlap phase.
Proof.
  intros version environment locals memory trace final_locals final_memory phase Hrun Hread Hother.
  pose proof (ocn_successful_body_requires_reported_overlap _ _ _ _ _ _ _ _ Hrun Hread) as Hgeometry.
  destruct Hother as (Hplayer & Harea & Hafter & Hbefore & Hwarp & Hmc & Htc & Hpair).
  unfold collision_phase_overlap.
  exact (conj Hplayer (conj Harea (conj Hafter (conj Hbefore (conj Hwarp
    (conj Hmc (conj Htc (conj Hgeometry Hpair)))))))).
Qed.
