(** The actual contact call, from Object memory to the horizontal test.
    The source reads X/Z and both radii BEFORE sqrtf. Its numeric return is
    explicit below; no memory-preservation effect is assigned to that call.
    This is not a reachability claim for the supplied live Object readings. *)
From Coq Require Import Bool List ZArith Reals Lra.
From Flocq Require Import BinarySingleNaN Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop
  Ctypes Errors Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes CollisionRegions
  Area2Rank12BContact ObjectContactNecessity ContactConsumerExecution
  EyerokRank15LiveMovement InkCopyCaller SelectedClightTarget Area2Rank9ACoinFlight
  PyramidTopPU.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Float32.cmp Float32.compare.

Lemma ocr_deref_unique : forall ty m b ofs bf v w,
  deref_loc ty m b ofs bf v -> deref_loc ty m b ofs bf w -> v = w.
Proof.
  intros ty m b ofs bf v w Hv Hw.
  inversion Hv; inversion Hw; subst; try congruence.
  repeat match goal with H : load_bitfield _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end; congruence.
Qed.

(** Expressions read one fixed memory; unlike calls, they have no effects. *)
Lemma ocr_expression_lvalue_unique : forall ge e le m,
  (forall a v, eval_expr ge e le m a v ->
    forall w, eval_expr ge e le m a w -> v = w) /\
  (forall a b ofs bf, eval_lvalue ge e le m a b ofs bf ->
    forall c off cf, eval_lvalue ge e le m a c off cf ->
      b = c /\ ofs = off /\ bf = cf).
Proof.
  intros ge e le m. apply eval_expr_lvalue_ind;
    intros; match goal with
    | H : eval_expr _ _ _ _ _ ?w |- _ = ?w => inversion H; subst; clear H
    | H : eval_lvalue _ _ _ _ _ ?c ?off ?cf |-
        _ = ?c /\ _ = ?off /\ _ = ?cf => inversion H; subst; clear H
    end;
    try solve [match goal with H : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion H end];
    try solve [match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H end];
    try congruence;
    repeat match goal with
    | IH : forall w, eval_expr ?ge ?e ?le ?m ?a w -> ?v = w,
      H : eval_expr ?ge ?e ?le ?m ?a ?w |- _ =>
        let E := fresh "Heq" in pose proof (IH _ H) as E;
        clear H; inversion E; subst; clear E
    | IH : forall c off cf, eval_lvalue ?ge ?e ?le ?m ?a c off cf ->
        ?b = c /\ ?ofs = off /\ ?bf = cf,
      H : eval_lvalue ?ge ?e ?le ?m ?a ?c ?off ?cf |- _ =>
        destruct (IH _ _ _ H) as [? [? ?]]; clear H; subst
    end;
    try congruence; try solve [repeat split; congruence];
    eauto using ocr_deref_unique.
  all: repeat match goal with
    | IH : forall w, eval_expr ?ge ?e ?le ?m ?a w -> ?v = w,
      H : eval_expr ?ge ?e ?le ?m ?a ?w |- _ => specialize (IH _ H)
    end.
  all: subst; try congruence; try (repeat split; congruence).
Qed.

Lemma ocr_expr_unique : forall ge e le m a v w,
  eval_expr ge e le m a v -> eval_expr ge e le m a w -> v = w.
Proof. intros. eapply (proj1 (ocr_expression_lvalue_unique ge e le m)); eauto. Qed.

Fixpoint ocr_readonly_prefix (s : statement) : bool := match s with
| Sskip | Sset _ _ => true
| Ssequence a b => ocr_readonly_prefix a && ocr_readonly_prefix b
| _ => false end.

Lemma ocr_readonly_normal : forall s,
  ocr_readonly_prefix s = true -> ocn_normal_prefix s = true.
Proof.
  induction s; cbn; try discriminate; auto.
  rewrite !andb_true_iff. intuition.
Qed.

Lemma ocr_readonly_unique : forall ge e le m s t le' m' out,
  ocn_exec ge e le m s t le' m' out -> ocr_readonly_prefix s = true ->
  forall u lu mu ou, ocn_exec ge e le m s u lu mu ou ->
    t = u /\ le' = lu /\ m' = mu /\ out = ou.
Proof.
  intros ge e le m s t le' m' out Hrun.
  induction Hrun; cbn; intros Hshape u lu mu ou Hother;
    try discriminate; inversion Hother; subst; try (repeat split; reflexivity).
  - match goal with Hv : eval_expr _ _ _ _ _ ?v,
      Hw : eval_expr _ _ _ _ _ ?w |- _ =>
      assert (v = w) by (eapply ocr_expr_unique; eauto); subst end.
    repeat split; reflexivity.
  - apply andb_true_iff in Hshape as [Ha Hb].
    match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ s1 _ _ _ Out_normal |- _ =>
      destruct (IHHrun1 Ha _ _ _ _ Hfirst) as [? [? [? ?]]]; subst end.
    match goal with Hlast : ClightBigstep.exec_stmt _ _ _ _ _ s2 _ _ _ _ |- _ =>
      destruct (IHHrun2 Hb _ _ _ _ Hlast) as [? [? [? ?]]]; subst end.
    repeat split; reflexivity.
  - apply andb_true_iff in Hshape as [Ha Hb].
    match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ s1 _ _ _ ?bad,
      Hbad : ?bad <> Out_normal |- _ =>
      exfalso; apply Hbad; eapply ocn_normal_prefix_outcome;
        [apply ocr_readonly_normal; exact Ha|exact Hfirst] end.
  - apply andb_true_iff in Hshape as [Ha Hb].
    exfalso. apply H. eapply ocn_normal_prefix_outcome;
      [apply ocr_readonly_normal; exact Ha|exact Hrun].
  - apply andb_true_iff in Hshape as [Ha Hb].
    exfalso. apply H. eapply ocn_normal_prefix_outcome;
      [apply ocr_readonly_normal; exact Ha|exact Hrun].
Qed.

Definition ocr_field temp field := Efield
  (Ederef (Etempvar temp (tptr (Tstruct RC._Object noattr)))
    (Tstruct RC._Object noattr)) field tfloat.
Definition ocr_index n := Ebinop Oadd (Econst_int (Int.repr 6) tint)
  (Econst_int (Int.repr n) tint) tint.
Definition ocr_position version temp n :=
  rank15_raw_float_expression version temp (ocr_index n).
Definition ocr_sum_squares := Ebinop Oadd
  (Ebinop Omul (Etempvar RC._dx tfloat) (Etempvar RC._dx tfloat) tfloat)
  (Ebinop Omul (Etempvar RC._dz tfloat) (Etempvar RC._dz tfloat) tfloat) tfloat.
Definition ocr_sqrt_call := Scall (Some RC._t'1)
  (Evar RC._sqrtf (Tfunction [tfloat] tfloat cc_default)) [ocr_sum_squares].
Definition ocr_input_prefix version :=
  ocn_prepend (ocn_prefix_items 6 (fn_body (rank12b_body version))) Sskip.
Definition ocr_calculation (version : GameVersion) :=
  Ssequence ocr_sqrt_call (Sset RC._distance (Etempvar RC._t'1 tfloat)).

Lemma ocr_generated_prefix : forall version,
  fn_body (rank12b_body version) =
    ocn_prepend (ocn_prefix_items 6 (fn_body (rank12b_body version)))
      (Ssequence (ocr_calculation version) (rank12b_after_sqrt version)) /\
  ocr_readonly_prefix (ocr_input_prefix version) = true /\
  forallb ocn_normal_prefix
    (ocn_prefix_items 6 (fn_body (rank12b_body version))) = true /\
  ocn_normal_prefix (ocr_calculation version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ocr_selected_fields : forall version,
  let ce := prog_comp_env (selected_clight_target version) in
  ibcc_field_ok ce RC._Object RC._hitboxRadius 504 = true /\
  ibcc_field_ok ce RC._Object RC._hitboxDownOffset 520 = true.
Proof.
  intros version. cbn zeta. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; split; reflexivity.
Qed.

Lemma ocr_field_read : forall (ge : genv) e le m temp field delta b ofs value,
  ibcc_field_ok ge RC._Object field delta = true ->
  le ! temp = Some (Vptr b ofs) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) =
    Some (Vsingle value) ->
  eval_expr ge e le m (ocr_field temp field) (Vsingle value).
Proof.
  intros ge e le m temp field delta b ofs value Hfield Htemp Hload.
  destruct (ibcc_field_ok_sound _ _ _ _ Hfield) as (co & Hco & Hoff).
  eapply eval_Elvalue.
  - unfold ocr_field. eapply eval_Efield_struct with (co := co).
    + eapply eval_Elvalue; [apply eval_Ederef; apply eval_Etempvar; exact Htemp|].
      apply deref_loc_copy. reflexivity.
    + reflexivity.
    + exact Hco.
    + exact Hoff.
  - eapply deref_loc_value with (chunk := Mfloat32); [reflexivity|exact Hload].
Qed.

Definition ocr_object_inputs memory block offset position hitbox : Prop :=
  Mem.load Mfloat32 memory block
    (Ptrofs.unsigned (rank15_raw_address offset (Int.repr 6))) = Some (Vsingle (vec_x position)) /\
  Mem.load Mfloat32 memory block
    (Ptrofs.unsigned (rank15_raw_address offset (Int.repr 7))) = Some (Vsingle (vec_y position)) /\
  Mem.load Mfloat32 memory block
    (Ptrofs.unsigned (rank15_raw_address offset (Int.repr 8))) = Some (Vsingle (vec_z position)) /\
  Mem.load Mfloat32 memory block
    (Ptrofs.unsigned (Ptrofs.add offset (Ptrofs.repr 504))) = Some (Vsingle (hitbox_radius hitbox)) /\
  Mem.load Mfloat32 memory block
    (Ptrofs.unsigned (Ptrofs.add offset (Ptrofs.repr 520))) = Some (Vsingle (hitbox_down_offset hitbox)).

Definition ocr_input_locals le ap ah bp bh :=
  PTree.set RC._collisionRadius (Vsingle (Float32.add (hitbox_radius ah) (hitbox_radius bh)))
  (PTree.set RC._t'15 (Vsingle (hitbox_radius bh))
  (PTree.set RC._t'14 (Vsingle (hitbox_radius ah))
  (PTree.set RC._dz (Vsingle (Float32.sub (vec_z ap) (vec_z bp)))
  (PTree.set RC._t'17 (Vsingle (vec_z bp))
  (PTree.set RC._t'16 (Vsingle (vec_z ap))
  (PTree.set RC._sp30 (Vsingle (Float32.sub (hitbox_bottom ap ah) (hitbox_bottom bp bh)))
  (PTree.set RC._dx (Vsingle (Float32.sub (vec_x ap) (vec_x bp)))
  (PTree.set RC._t'19 (Vsingle (vec_x bp))
  (PTree.set RC._t'18 (Vsingle (vec_x ap))
  (PTree.set RC._sp38 (Vsingle (hitbox_bottom bp bh))
  (PTree.set RC._t'21 (Vsingle (hitbox_down_offset bh))
  (PTree.set RC._t'20 (Vsingle (vec_y bp))
  (PTree.set RC._sp3C (Vsingle (hitbox_bottom ap ah))
  (PTree.set RC._t'23 (Vsingle (hitbox_down_offset ah))
  (PTree.set RC._t'22 (Vsingle (vec_y ap)) le))))))))))))))).

Lemma ocr_index_evaluates : forall ge e le m n,
  eval_expr ge e le m (ocr_index n) (Vint (Int.add (Int.repr 6) (Int.repr n))).
Proof. intros. eapply eval_Ebinop; [constructor|constructor|reflexivity]. Qed.

Theorem ocr_input_prefix_executes_from_memory :
  forall version e le m ab ao ap ah bb bo bp bh,
  le ! RC._a = Some (Vptr ab ao) -> le ! RC._b = Some (Vptr bb bo) ->
  ocr_object_inputs m ab ao ap ah -> ocr_object_inputs m bb bo bp bh ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ocr_input_prefix version) E0 (ocr_input_locals le ap ah bp bh) m Out_normal.
Proof.
  intros version e le m ab ao ap ah bb bo bp bh Ha Hb
    (Hax & Hay & Haz & Har & Hao) (Hbx & Hby & Hbz & Hbr & Hbo).
  destruct (ocr_selected_fields version) as [Hradius Hdown].
  assert (forall locals temp n block offset value,
    locals ! temp = Some (Vptr block offset) ->
    Mem.load Mfloat32 m block (Ptrofs.unsigned
      (rank15_raw_address offset (Int.add (Int.repr 6) (Int.repr n)))) = Some (Vsingle value) ->
    eval_expr (Clight.globalenv (selected_clight_target version)) e locals m
      (ocr_position version temp n) (Vsingle value)) as Hposition.
  { intros. eapply rank15_raw_float_read; eauto using ocr_index_evaluates. }
  replace (ocr_input_prefix version) with
    (ocn_prepend
      [Ssequence (Sset RC._t'22 (ocr_position version RC._a 1))
        (Ssequence (Sset RC._t'23 (ocr_field RC._a RC._hitboxDownOffset))
          (Sset RC._sp3C (Ebinop Osub (Etempvar RC._t'22 tfloat) (Etempvar RC._t'23 tfloat) tfloat)));
       Ssequence (Sset RC._t'20 (ocr_position version RC._b 1))
        (Ssequence (Sset RC._t'21 (ocr_field RC._b RC._hitboxDownOffset))
          (Sset RC._sp38 (Ebinop Osub (Etempvar RC._t'20 tfloat) (Etempvar RC._t'21 tfloat) tfloat)));
       Ssequence (Sset RC._t'18 (ocr_position version RC._a 0))
        (Ssequence (Sset RC._t'19 (ocr_position version RC._b 0))
          (Sset RC._dx (Ebinop Osub (Etempvar RC._t'18 tfloat) (Etempvar RC._t'19 tfloat) tfloat)));
       Sset RC._sp30 (Ebinop Osub (Etempvar RC._sp3C tfloat) (Etempvar RC._sp38 tfloat) tfloat);
       Ssequence (Sset RC._t'16 (ocr_position version RC._a 2))
        (Ssequence (Sset RC._t'17 (ocr_position version RC._b 2))
          (Sset RC._dz (Ebinop Osub (Etempvar RC._t'16 tfloat) (Etempvar RC._t'17 tfloat) tfloat)));
       Ssequence (Sset RC._t'14 (ocr_field RC._a RC._hitboxRadius))
        (Ssequence (Sset RC._t'15 (ocr_field RC._b RC._hitboxRadius))
          (Sset RC._collisionRadius (Ebinop Oadd (Etempvar RC._t'14 tfloat) (Etempvar RC._t'15 tfloat) tfloat)))] Sskip)
    by (destruct version; reflexivity).
  unfold ocn_prepend, ocr_input_locals, hitbox_bottom.
  repeat first
    [ apply exec_Sskip
    | eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    | apply exec_Sset
    | eapply Hposition; [repeat (rewrite PTree.gso by discriminate); eassumption|eassumption]
    | eapply ocr_field_read; [eassumption|repeat (rewrite PTree.gso by discriminate); eassumption|eassumption]
    | eapply eval_Ebinop; [apply eval_Etempvar; rank15_temporary|apply eval_Etempvar; rank15_temporary|reflexivity] ].
Qed.

Definition ocr_squared_distance ap bp :=
  let dx := Float32.sub (vec_x ap) (vec_x bp) in
  let dz := Float32.sub (vec_z ap) (vec_z bp) in
  Float32.add (Float32.mul dx dx) (Float32.mul dz dz).

Lemma ocr_squared_distance_evaluates : forall ge e le m ap ah bp bh,
  eval_expr ge e (ocr_input_locals le ap ah bp bh) m ocr_sum_squares
    (Vsingle (ocr_squared_distance ap bp)).
Proof.
  intros. unfold ocr_sum_squares, ocr_squared_distance, ocr_input_locals.
  eapply eval_Ebinop.
  - eapply eval_Ebinop; [apply eval_Etempvar; rank15_temporary|
      apply eval_Etempvar; rank15_temporary|reflexivity].
  - eapply eval_Ebinop; [apply eval_Etempvar; rank15_temporary|
      apply eval_Etempvar; rank15_temporary|reflexivity].
  - reflexivity.
Qed.

Lemma ocr_squared_argument_is_exact : forall ge e le m ap ah bp bh args,
  eval_exprlist ge e (ocr_input_locals le ap ah bp bh) m
    [ocr_sum_squares] [tfloat] args ->
  args = [Vsingle (ocr_squared_distance ap bp)].
Proof.
  intros ge e le m ap ah bp bh args Hargs. inversion Hargs; subst.
  match goal with Hexpr : eval_expr _ _ _ _ ocr_sum_squares ?v |- _ =>
    assert (v = Vsingle (ocr_squared_distance ap bp))
      by (eapply ocr_expr_unique; [exact Hexpr|apply ocr_squared_distance_evaluates]);
    subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Hnil : eval_exprlist _ _ _ _ [] [] _ |- _ =>
    inversion Hnil; subst end. reflexivity.
Qed.

Definition ocr_distance_locals le ap ah bp bh value :=
  PTree.set RC._distance value
    (PTree.set RC._t'1 value (ocr_input_locals le ap ah bp bh)).

(** Extract the ONE reached square-root call. Neither its result nor its
    memory effect is assumed. In particular its argument uses entry memory,
    while the subsequent comparison may run in the call's changed memory. *)
Theorem ocr_calculation_exposes_actual_sqrt :
  forall version e le m ap ah bp bh t le' m' out,
  e ! RC._sqrtf = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e
    (ocr_input_locals le ap ah bp bh) m (ocr_calculation version) t le' m' out ->
  exists function_block fd result,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      RC._sqrtf = Some function_block /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
      function_block = Some fd /\
    type_of_fundef fd = Tfunction [tfloat] tfloat cc_default /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m fd
      [Vsingle (ocr_squared_distance ap bp)] t m' result /\
    le' = ocr_distance_locals le ap ah bp bh result /\ out = Out_normal.
Proof.
  intros version e le m ap ah bp bh t le' m' out Hlocal Hrun.
  unfold ocr_calculation, ocr_sqrt_call, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ _ |- _ =>
    inversion Hcall; subst; clear Hcall end.
  all: try contradiction.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  match goal with Hargs : eval_exprlist _ _ _ _ [ocr_sum_squares] [tfloat] _ |- _ =>
    apply ocr_squared_argument_is_exact in Hargs; subst end.
  match goal with Hname : eval_expr _ _ _ _ (Evar RC._sqrtf _) _ |- _ =>
    inversion Hname; subst; clear Hname end.
  match goal with Hlv : eval_lvalue _ _ _ _ (Evar RC._sqrtf _) _ _ _ |- _ =>
    inversion Hlv; subst; clear Hlv; try congruence end.
  match goal with Hderef : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hderef; subst; clear Hderef; try discriminate end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ ?value,
    Hcopy : eval_expr _ _ _ _ (Etempvar RC._t'1 tfloat) ?copied |- _ =>
    assert (copied = value) by (eapply ocn_temp_value; [exact Hcopy|apply PTree.gss]);
    subst copied end.
  match goal with Hfind : Genv.find_symbol _ RC._sqrtf = Some ?block,
    Hcall : ClightBigstep.eval_funcall _ _ _ ?fd _ _ _ ?result |- _ =>
    exists block, fd, result end.
  repeat split; try assumption; try reflexivity.
  unfold Eapp. rewrite app_nil_r. assumption.
Qed.

Lemma ocr_gate_comparison_false : forall gate target position,
  rank12b_in_gate_xz gate position ->
  Float32.cmp Cgt
    (Float32.add (hitbox_radius mario_standard_hitbox_f32)
      (hitbox_radius (rank12b_target_hitbox target)))
    (horizontal_distance position (rank12b_target_position target)) = false.
Proof.
  intros gate target position Hg.
  destruct (rank12b_every_gate_position_is_horizontally_far gate target position Hg)
    as [Fd Hdistance].
  assert (Fr : rank9cf_finite (Float32.add (hitbox_radius mario_standard_hitbox_f32)
    (hitbox_radius (rank12b_target_hitbox target)))) by (destruct target; reflexivity).
  assert (Hradius : (rank9cf_real (Float32.add (hitbox_radius mario_standard_hitbox_f32)
    (hitbox_radius (rank12b_target_hitbox target))) < 256)%R)
    by (destruct target; vm_compute; lra).
  unfold Float32.cmp, Float32.compare. rewrite Bcompare_correct by assumption.
  rewrite Rcompare_Lt by (unfold rank9cf_real in Hradius, Hdistance; lra). reflexivity.
Qed.

Lemma ocr_gate_tail_result :
  forall version gate target position e le m t le' m' out,
  rank12b_in_gate_xz gate position ->
  le ! RC._collisionRadius = Some (Vsingle
    (Float32.add (hitbox_radius mario_standard_hitbox_f32)
      (hitbox_radius (rank12b_target_hitbox target)))) ->
  le ! RC._distance = Some (Vsingle
    (horizontal_distance position (rank12b_target_position target))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (rank12b_after_sqrt version) t le' m' out ->
  t = E0 /\ le' = le /\ m' = m /\ out = Out_return (Some (Vint Int.zero, tint)).
Proof.
  intros version gate target position e le m t le' m' out Hg Hr Hd Hrun.
  assert (eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    rank12b_radius_test (Vint Int.zero)) as Htest.
  { eapply eval_Ebinop; [apply eval_Etempvar; exact Hr|apply eval_Etempvar; exact Hd|].
    change (Some (Val.of_bool (Float32.cmp Cgt
      (Float32.add (hitbox_radius mario_standard_hitbox_f32)
        (hitbox_radius (rank12b_target_hitbox target)))
      (horizontal_distance position (rank12b_target_position target)))) = Some (Vint Int.zero)).
    rewrite (ocr_gate_comparison_false gate target position Hg). reflexivity. }
  rewrite (proj1 (rank12b_generated_radius_tail_is_exact version)) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  inversion Hrun; subst;
    match goal with Hif : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
      inversion Hif; subst; clear Hif end;
    match goal with Hread : eval_expr _ _ _ _ rank12b_radius_test ?v |- _ =>
      assert (v = Vint Int.zero) by (eapply ocr_expr_unique; [exact Hread|exact Htest]);
      subst v end;
    match goal with Hbool : bool_val (Vint Int.zero) _ _ = Some ?b |- _ =>
      change (Some false = Some b) in Hbool; inversion Hbool; subst b end;
    match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hskip; subst; clear Hskip end; try contradiction.
  match goal with Hreturn : ClightBigstep.exec_stmt _ _ _ _ _ rank12b_return_zero _ _ _ _ |- _ =>
    unfold rank12b_return_zero in Hreturn; inversion Hreturn; subst end.
  match goal with Hvalue : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hvalue; subst end.
  repeat split; reflexivity.
Qed.

(** The prefix, square-root call, and suffix below are parts of the supplied
    execution, with matching memory at every adjacent endpoint. *)
Theorem ocr_body_has_same_run_distance_cut :
  forall version e le m ab ao ap ah bb bo bp bh t le' m' out,
  e ! RC._sqrtf = None ->
  le ! RC._a = Some (Vptr ab ao) -> le ! RC._b = Some (Vptr bb bo) ->
  ocr_object_inputs m ab ao ap ah -> ocr_object_inputs m bb bo bp bh ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (rank12b_body version)) t le' m' out ->
  exists function_block fd value call_trace call_memory suffix_trace,
    t = call_trace ++ suffix_trace /\
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      RC._sqrtf = Some function_block /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
      function_block = Some fd /\
    type_of_fundef fd = Tfunction [tfloat] tfloat cc_default /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m fd
      [Vsingle (ocr_squared_distance ap bp)] call_trace call_memory value /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (ocr_distance_locals le ap ah bp bh value) call_memory
      (rank12b_after_sqrt version) suffix_trace le' m' out.
Proof.
  intros version e le m ab ao ap ah bb bo bp bh t le' m' out
    Hlocal Ha Hb Hain Hbin Hrun.
  destruct (ocr_generated_prefix version) as (Hbody & Hreadonly & Hnormal & _).
  rewrite Hbody in Hrun.
  destruct (ocn_successful_prefix_decomposition _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & rest & Htrace & Hprefix & Hrest).
  pose proof (ocr_input_prefix_executes_from_memory version e le m
    ab ao ap ah bb bo bp bh Ha Hb Hain Hbin) as Hconstructed.
  destruct (ocr_readonly_unique _ _ _ _ _ _ _ _ _ Hprefix Hreadonly
    _ _ _ _ Hconstructed) as (Hpre & Hmiddle & Hmemory & _).
  subst pre middle memory.
  destruct (InkBackwardExecution.ibk_split_sequence _ _ _ _ (ocr_calculation version) _ _ _ _ _
    eq_refl Hrest) as (ready & after & call_trace & suffix_trace & Hrest_trace & Hcall & Hsuffix).
  destruct (ocr_calculation_exposes_actual_sqrt _ _ _ _ _ _ _ _ _ _ _ _ Hlocal Hcall)
    as (function_block & fd & value & Hsymbol & Hfunction & Htype & Hactual & Hready & _).
  subst ready. exists function_block, fd, value, call_trace, after, suffix_trace.
  repeat split; try assumption. rewrite Htrace. exact Hrest_trace.
Qed.

Definition ocr_sqrt_numeric_effect version memory argument : Prop :=
  forall function_block fd trace after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    RC._sqrtf = Some function_block ->
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
    function_block = Some fd ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) memory fd
    [Vsingle argument] trace after result ->
  result = Vsingle (Float32.sqrt argument).

(** Only the reached sqrtf's numerical result is needed for horizontal
    rejection. Its memory need NOT be unchanged. A separate reward writer
    inside an unspecified outside effect is not ruled out by this theorem. *)
Theorem ocr_gate_body_rejects_from_entry_reads :
  forall version gate target position e le m ab ao bb bo t le' m' out,
  ocr_sqrt_numeric_effect version m
    (ocr_squared_distance position (rank12b_target_position target)) ->
  rank12b_in_gate_xz gate position -> e ! RC._sqrtf = None ->
  le ! RC._a = Some (Vptr ab ao) -> le ! RC._b = Some (Vptr bb bo) ->
  ocr_object_inputs m ab ao position mario_standard_hitbox_f32 ->
  ocr_object_inputs m bb bo (rank12b_target_position target) (rank12b_target_hitbox target) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (rank12b_body version)) t le' m' out ->
  out = Out_return (Some (Vint Int.zero, tint)).
Proof.
  intros version gate target position e le m ab ao bb bo t le' m' out
    Hsqrt Hg Hlocal Ha Hb Hain Hbin Hrun.
  destruct (ocr_body_has_same_run_distance_cut version e le m
    ab ao position mario_standard_hitbox_f32 bb bo
    (rank12b_target_position target) (rank12b_target_hitbox target)
    t le' m' out Hlocal Ha Hb Hain Hbin Hrun)
    as (function_block & fd & value & ct & cm & st & Htrace & Hsymbol & Hfunction & Htype & Hcall & Hsuffix).
  assert (value = Vsingle (horizontal_distance position (rank12b_target_position target))) as Hvalue.
  { exact (Hsqrt _ _ _ _ _ Hsymbol Hfunction Hcall). }
  subst value.
  destruct (ocr_gate_tail_result version gate target position e
    (ocr_distance_locals le position mario_standard_hitbox_f32
      (rank12b_target_position target) (rank12b_target_hitbox target)
      (Vsingle (horizontal_distance position (rank12b_target_position target)))) cm st le' m' out
    Hg ltac:(unfold ocr_distance_locals, ocr_input_locals; rank15_temporary)
    ltac:(unfold ocr_distance_locals; apply PTree.gss) Hsuffix) as (_ & _ & _ & Hout).
  exact Hout.
Qed.

Lemma ocr_call_entry_reads : forall version m ab ao bb bo e le after,
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (rank12b_body version) [Vptr ab ao; Vptr bb bo] m e le after ->
  e = empty_env /\ after = m /\
  le ! RC._a = Some (Vptr ab ao) /\ le ! RC._b = Some (Vptr bb bo).
Proof.
  intros version m ab ao bb bo e le after Hentry.
  assert (fn_vars (rank12b_body version) = []) as Hvars by (destruct version; reflexivity).
  inversion Hentry; subst; clear Hentry.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  repeat split; try reflexivity.
  all: match goal with Hbind : bind_parameter_temps _ _ _ = Some _ |- _ =>
    destruct version; cbn in Hbind; inversion Hbind; reflexivity end.
Qed.

Theorem ocr_gate_call_returns_zero :
  forall version gate target position m ab ao bb bo t m' result,
  ocr_sqrt_numeric_effect version m
    (ocr_squared_distance position (rank12b_target_position target)) ->
  rank12b_in_gate_xz gate position ->
  ocr_object_inputs m ab ao position mario_standard_hitbox_f32 ->
  ocr_object_inputs m bb bo (rank12b_target_position target) (rank12b_target_hitbox target) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (rank12b_body version)) [Vptr ab ao; Vptr bb bo] t m' result ->
  result = Vint Int.zero.
Proof.
  intros version gate target position m ab ao bb bo t m' result Hsqrt Hg Hain Hbin Hcall.
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (ocr_call_entry_reads _ _ _ _ _ _ _ _ _ Hentry) as (? & ? & Ha & Hb);
    subst end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body (rank12b_body _)) _ _ _ ?out |- _ =>
    assert (out = Out_return (Some (Vint Int.zero, tint)))
      by (eapply ocr_gate_body_rejects_from_entry_reads; eauto; reflexivity);
    subst out end.
  match goal with Hresult : outcome_result_value _ _ _ _ |- _ =>
    rename Hresult into Hreturn_value end.
  replace (fn_return (rank12b_body version)) with tint in Hreturn_value
    by (destruct version; reflexivity).
  cbn in Hreturn_value. destruct Hreturn_value as [_ Hvalue].
  change (Some (Vint Int.zero) = Some result) in Hvalue. congruence.
Qed.
