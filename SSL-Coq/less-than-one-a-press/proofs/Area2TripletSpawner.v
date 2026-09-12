(** Fresh Area-2 triplet spawner during elevator confinement.
    The distance theorem covers fractional binary32 coordinates, not samples.
    The execution theorem uses the complete generated US/JP native body.
    Engine scheduling and the external sqrtf boundary are kept separate. *)
From Coq Require Import Bool Lia List ZArith Reals Lra.
From Flocq Require Import BinarySingleNaN Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_behavior_data jp_behavior_data
  us_behavior_script jp_behavior_script us_object_collision jp_object_collision
  us_spawn_object jp_spawn_object.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts Area2Rank12BContact
  Area2Rank11GoombaInstaller Area2GoombaDeath Area2Rank9ACoinFlight
  ObjectContactReadback ObjectContactNecessity ReadOnlyClightPaths InkCopyCaller InkFloorCallEffects
  EyerokRank15LiveMovement
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module TS := us_obj_behaviors_2.
Module TB := us_behavior_script.
Module TD := us_object_helpers.

(** The actual stock macro coordinates are checked by the existing roster. *)
Theorem ts_stock_parent :
  Rank11Area2GoombaRosterSourceShape /\
  rank11_area2_triplet_spawners = [[63;3181;0;3587;0]].
Proof. split; [exact rank11_area2_goomba_roster_source_shape_checked|reflexivity]. Qed.

Definition ts_float z := Float32.of_int (Int.repr z).
Definition ts_distance dx dy dz := Float32.sqrt
  (Float32.add (Float32.add (Float32.mul dx dx) (Float32.mul dy dy))
    (Float32.mul dz dz)).
Definition ts_squared_expression := Ebinop Oadd
  (Ebinop Oadd
    (Ebinop Omul (Etempvar TD._dx tfloat) (Etempvar TD._dx tfloat) tfloat)
    (Ebinop Omul (Etempvar TD._dy tfloat) (Etempvar TD._dy tfloat) tfloat) tfloat)
  (Ebinop Omul (Etempvar TD._dz tfloat) (Etempvar TD._dz tfloat) tfloat) tfloat.
Definition ts_distance_body version := match version with
| VersionUS => us_object_helpers.f_dist_between_objects
| VersionJP => jp_object_helpers.f_dist_between_objects end.

(** Tie the arithmetic expression and its evaluation order to the actual
    helper. This is a source receipt, not an assumed sqrtf call contract. *)
Theorem ts_real_distance_calculation : forall version,
  fn_body (ts_distance_body version) =
    ocn_prepend (ocn_prefix_items 3 (fn_body (ts_distance_body version)))
      (Ssequence (Scall (Some TD._t'1)
        (Evar TD._sqrtf (Tfunction [tfloat] tfloat cc_default))
        [ts_squared_expression])
        (Sreturn (Some (Etempvar TD._t'1 tfloat)))) /\
  forallb ocr_readonly_prefix (ocn_prefix_items 3 (fn_body (ts_distance_body version))) = true.
Proof. intros []; split; reflexivity. Qed.

Theorem ts_squared_expression_evaluates : forall ge e le m dx dy dz,
  le ! TD._dx = Some (Vsingle dx) -> le ! TD._dy = Some (Vsingle dy) ->
  le ! TD._dz = Some (Vsingle dz) ->
  eval_expr ge e le m ts_squared_expression
    (Vsingle (Float32.add (Float32.add (Float32.mul dx dx) (Float32.mul dy dy))
      (Float32.mul dz dz))).
Proof.
  intros ge e le m dx dy dz Hx Hy Hz. unfold ts_squared_expression.
  repeat (eapply eval_Ebinop || (apply eval_Etempvar; eassumption) || reflexivity).
Qed.
Definition ts_in_base x z :=
  rank9cf_finite x /\ rank9cf_finite z /\
  (-511 <= rank9cf_real x <= 512)%R /\
  (-255 <= rank9cf_real z <= 768)%R.

Lemma ts_stable_from_bits : forall z bits,
  rank9cf_real (Float32.of_bits (Int.repr bits)) = IZR z ->
  rank12b_stable z.
Proof.
  intros z bits H. unfold rank12b_stable. rewrite <- H.
  unfold rank9cf_round, rank9cf_real. apply round_generic;
    [apply valid_rnd_round_mode|apply generic_format_B2R].
Qed.

Lemma ts_endpoints :
  rank12b_stable 7123561 /\ rank12b_stable 7946761 /\
  rank12b_stable 15070322 /\ rank12b_stable 16777216 /\
  rank12b_stable 285212672.
Proof.
  repeat split; eapply ts_stable_from_bits.
  - instantiate (1 := 1255761106). vm_compute; field.
  - instantiate (1 := 1257407506). vm_compute; field.
  - instantiate (1 := 1264972914). vm_compute; field.
  - instantiate (1 := 1266679808). vm_compute; field.
  - instantiate (1 := 1300758528). vm_compute; field.
Qed.

(** dy is the already rounded vertical difference used by the real helper.
    Its generous bound includes the entire stock elevator journey. This
    theorem does not assert that a live distance field already has this value. *)
Theorem ts_every_base_position_is_out_of_range : forall x z dy,
  ts_in_base x z -> rank9cf_finite dy ->
  (-16384 <= rank9cf_real dy <= 16384)%R ->
  let distance := ts_distance (Float32.sub (ts_float 3181) x) dy
    (Float32.sub (ts_float 3587) z) in
  rank9cf_finite distance /\ (3882 <= rank9cf_real distance <= 32768)%R /\
  Float32.cmp Clt distance (ts_float 3000) = false.
Proof.
  intros x z dy (Fx & Fz & Hx & Hz) Fy Hy distance.
  destruct (rank9cf_integer_exact 3181 ltac:(lia)) as [Rpx Fpx].
  destruct (rank9cf_integer_exact 3587 ltac:(lia)) as [Rpz Fpz].
  destruct (rank12b_sub_range (ts_float 3181) x 2669 3692
    Fpx Fx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(change
      (rank9cf_real (ts_float 3181) = 3181)%R in Rpx; lra)) as [Fdx Hdx].
  destruct (rank12b_sub_range (ts_float 3587) z 2819 3842
    Fpz Fz ltac:(lia) ltac:(lia) ltac:(lia) ltac:(change
      (rank9cf_real (ts_float 3587) = 3587)%R in Rpz; lra)) as [Fdz Hdz].
  destruct ts_endpoints as (Sxx & Szz & Ssum & Ssmall & Sxy).
  destruct rank12b_large_endpoints_stable as [Ssquare Slarge].
  assert (S0 : rank12b_stable 0) by (apply rank9cf_round_integer; lia).
  destruct (rank12b_mul_range _ _ 7123561 16777216 Fdx Fdx
    ltac:(lia) ltac:(lia) Sxx Ssmall ltac:(nra)) as [Fxx Hxx].
  destruct (rank12b_mul_range _ _ 7946761 16777216 Fdz Fdz
    ltac:(lia) ltac:(lia) Szz Ssmall ltac:(nra)) as [Fzz Hzz].
  destruct (rank12b_mul_range dy dy 0 268435456 Fy Fy
    ltac:(lia) ltac:(lia) S0 Ssquare ltac:(nra)) as [Fyy Hyy].
  destruct (rank12b_add_range _ _ 7123561 285212672 Fxx Fyy
    ltac:(lia) ltac:(lia) Sxx Sxy ltac:(lra)) as [Fxy Hxy].
  destruct (rank12b_add_range _ _ 15070322 536870912 Fxy Fzz
    ltac:(lia) ltac:(lia) Ssum Slarge ltac:(lra)) as [Fs Hs].
  set (squared := Float32.add
    (Float32.add (Float32.mul (Float32.sub (ts_float 3181) x)
      (Float32.sub (ts_float 3181) x)) (Float32.mul dy dy))
    (Float32.mul (Float32.sub (ts_float 3587) z)
      (Float32.sub (ts_float 3587) z))) in *.
  pose proof (Bsqrt_correct 24 128 eq_refl eq_refl Float32.unop_nan
    mode_NE squared) as [Hr _].
  change (rank9cf_real distance = rank9cf_round (sqrt (rank9cf_real squared))) in Hr.
  assert (Hroot : (3882 <= sqrt (rank9cf_real squared) <= 32768)%R).
  { pose proof (sqrt_pos (rank9cf_real squared)).
    pose proof (sqrt_def (rank9cf_real squared) ltac:(lra)). nra. }
  pose proof (rank9cf_round_range 3882 32768 _ ltac:(lia) ltac:(lia)
    ltac:(lia) Hroot) as Hdistance. rewrite <- Hr in Hdistance.
  assert (Fd : rank9cf_finite distance) by
    (apply rank12b_nonzero_real_is_finite; lra).
  split; [exact Fd|]. split; [exact Hdistance|].
  destruct (rank9cf_integer_exact 3000 ltac:(lia)) as [Rlimit Flimit].
  apply rank12b_cmp_lt_false; try assumption.
  change (rank9cf_real (ts_float 3000) = 3000)%R in Rlimit. lra.
Qed.

Definition ts_body version := match version with
| VersionUS => us_obj_behaviors_2.f_bhv_goomba_triplet_spawner_update
| VersionJP => jp_obj_behaviors_2.f_bhv_goomba_triplet_spawner_update end.
Definition ts_raw_int version temporary index :=
  Ederef (Ebinop Oadd
    (Efield (Efield
      (Ederef (Etempvar temporary (tptr (Tstruct TS._Object noattr)))
        (Tstruct TS._Object noattr)) TS._rawData
        (Tunion (rank15_raw_union_tag version) noattr))
      TS._asS32 (tarray tint 80))
    (Econst_int (Int.repr index) tint) (tptr tint)) tint.
Definition ts_threshold := Float32.of_bits (Int.repr 1161527296).

Theorem ts_generated_body : forall version, exists spawn loaded,
  fn_body (ts_body version) =
  Ssequence (Sset TS._t'1 rank15_current_object_expression)
    (Ssequence (Sset TS._t'2 (ts_raw_int version TS._t'1 49))
      (Sifthenelse (Ebinop Oeq (Etempvar TS._t'2 tint)
        (Econst_int Int.zero tint) tint)
        (Ssequence (Sset TS._t'6 rank15_current_object_expression)
          (Ssequence (Sset TS._t'7 (rank15_raw_float_expression version TS._t'6
            (Econst_int (Int.repr 53) tint)))
            (Sifthenelse (Ebinop Olt (Etempvar TS._t'7 tfloat)
              (Econst_single ts_threshold tfloat) tint) spawn Sskip))) loaded)).
Proof. intros []; do 2 eexists; reflexivity. Qed.

Definition ts_s32_layout_check environment union_tag :=
  match environment ! TS._Object, environment ! union_tag with
  | Some obj, Some raw =>
    match field_offset environment TS._rawData (co_members obj),
      union_field_offset environment TS._asS32 (co_members raw) with
    | OK (a, Full), OK (b, Full) => Z.eqb a 136 && Z.eqb b 0
    | _, _ => false end
  | _, _ => false end.
Lemma ts_s32_layout_checked : forall version,
  ts_s32_layout_check (rank15_selected_header_environment version)
    (rank15_raw_union_tag version) = true.
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma ts_s32_layout : forall version,
  let ge := Clight.globalenv (selected_clight_target version) in
  exists obj raw,
    (genv_cenv ge) ! TS._Object = Some obj /\
    (genv_cenv ge) ! (rank15_raw_union_tag version) = Some raw /\
    field_offset ge TS._rawData (co_members obj) = OK (136, Full) /\
    union_field_offset ge TS._asS32 (co_members raw) = OK (0, Full).
Proof.
  intros version ge. pose proof (ts_s32_layout_checked version) as H.
  rewrite rank15_selected_header_environment_exact in H.
  change (ts_s32_layout_check (genv_cenv ge) (rank15_raw_union_tag version) = true) in H.
  unfold ts_s32_layout_check in H.
  destruct ((genv_cenv ge) ! TS._Object) as [obj|] eqn:Ho; try discriminate.
  destruct ((genv_cenv ge) ! (rank15_raw_union_tag version)) as [raw|] eqn:Hr;
    try discriminate.
  destruct (field_offset ge TS._rawData (co_members obj)) as [[a af]|] eqn:Ha;
    try discriminate.
  destruct (union_field_offset ge TS._asS32 (co_members raw)) as [[b bf]|] eqn:Hb;
    [|destruct af; discriminate].
  destruct af, bf; cbn in H; try discriminate.
  apply andb_true_iff in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst a b.
  exists obj, raw. repeat split; assumption.
Qed.

Lemma ts_raw_int_read : forall version e le m temporary ob oo index value,
  le ! temporary = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr index))) =
    Some (Vint value) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ts_raw_int version temporary index) (Vint value).
Proof.
  intros version e le m temporary ob oo index value Htemp Hload.
  destruct (ts_s32_layout version) as (obj & raw & Ho & Hr & Ha & Hb).
  eapply eval_Elvalue.
  - unfold ts_raw_int, rank15_raw_address. apply eval_Ederef. eapply eval_Ebinop.
    + eapply eval_Elvalue.
      * eapply eval_Efield_union with (co := raw).
        -- eapply eval_Elvalue.
           ++ eapply eval_Efield_struct with (co := obj).
              ** eapply eval_Elvalue.
                 --- apply eval_Ederef. apply eval_Etempvar. exact Htemp.
                 --- apply deref_loc_copy. reflexivity.
              ** reflexivity.
              ** exact Ho.
              ** exact Ha.
           ++ apply deref_loc_copy. reflexivity.
        -- reflexivity.
        -- exact Hr.
        -- exact Hb.
      * apply deref_loc_reference. reflexivity.
    + constructor.
    + cbn. rewrite Ptrofs.add_zero. reflexivity.
  - eapply deref_loc_value with (chunk := Mint32); [reflexivity|exact Hload].
Qed.

Definition TripletNativeReadOnlyPath : Prop :=
  forall version e le m cb ob oo distance,
  e ! TS._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    TS._gCurrentObject = Some cb ->
  Mem.load Mptr m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 49))) =
    Some (Vint Int.zero) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 53))) =
    Some (Vsingle distance) ->
  Float32.cmp Clt distance ts_threshold = false ->
  exists le', readonly_path
    (Clight.globalenv (selected_clight_target version)) e m le
    (fn_body (ts_body version)) le'.

Theorem ts_native_readonly_path : TripletNativeReadOnlyPath.
Proof.
  intros version e le m cb ob oo distance Hlocal Hsymbol Hcurrent Haction Hdist Hfar.
  destruct (ts_generated_body version) as (spawn & loaded & Hbody).
  rewrite Hbody. eexists.
  eapply ro_seq.
  - apply ro_set. eapply rank15_current_object_read; eauto.
  - eapply ro_seq.
    + apply ro_set. eapply ts_raw_int_read; [apply PTree.gss|exact Haction].
    + eapply ro_if with (v := Vint Int.one) (choice := true).
      * eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|constructor|reflexivity].
      * reflexivity.
      * eapply ro_seq.
        -- apply ro_set. eapply rank15_current_object_read; eauto.
        -- eapply ro_seq.
           ++ apply ro_set. eapply rank15_raw_float_read;
                [apply PTree.gss|constructor|reflexivity|exact Hdist].
           ++ eapply ro_if with (v := Vint Int.zero) (choice := false).
              ** eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|constructor|].
                 change (Some (Val.of_bool (Float32.cmp Clt distance ts_threshold)) =
                   Some (Vint Int.zero)). rewrite Hfar. reflexivity.
              ** reflexivity.
              ** constructor.
Qed.

(** Every execution has this outcome, rather than only one constructed run. *)
Definition TripletNativeNoSpawnPreservation : Prop :=
  forall version e le m cb ob oo distance trace le' m' out,
  e ! TS._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    TS._gCurrentObject = Some cb ->
  Mem.load Mptr m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 49))) =
    Some (Vint Int.zero) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 53))) =
    Some (Vsingle distance) ->
  Float32.cmp Clt distance ts_threshold = false ->
  ClightBigstep.Clight2.exec_stmt
    (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ts_body version)) trace le' m' out ->
  trace = E0 /\ m' = m /\ out = Out_normal.

Theorem ts_native_no_spawn_preserves_all_memory : TripletNativeNoSpawnPreservation.
Proof.
  intros version e le m cb ob oo distance trace le' m' out
    Hlocal Hsymbol Hcurrent Haction Hdist Hfar Hrun.
  destruct (ts_native_readonly_path version e le m cb ob oo distance
    Hlocal Hsymbol Hcurrent Haction Hdist Hfar) as [final Hpath].
  destruct (readonly_path_forces_every_execution _ _ _ _ _ _ Hpath
    _ _ _ _ Hrun) as (? & ? & ? & ?). auto.
Qed.

(** The first script pass starts before the distance-computation flag is
    enabled. Allocation supplies 19000; subsequent passes use the helper. *)
Theorem ts_initial_distance_rejects :
  Float32.cmp Clt (Float32.of_bits (Int.repr 1184133120)) ts_threshold = false /\
  forall version, assigns_array_slot_float32_constant_s TS._asF32 53 1184133120
    (fn_body (match version with
      | VersionUS => us_spawn_object.f_allocate_object
      | VersionJP => jp_spawn_object.f_allocate_object end)) = true.
Proof. split; [reflexivity|intros []; vm_compute; reflexivity]. Qed.

Theorem ts_elevator_distance_rejects_native_guard : forall x z dy,
  ts_in_base x z -> rank9cf_finite dy ->
  (-16384 <= rank9cf_real dy <= 16384)%R ->
  Float32.cmp Clt
    (ts_distance (Float32.sub (ts_float 3181) x) dy
      (Float32.sub (ts_float 3587) z)) ts_threshold = false.
Proof.
  intros x z dy Hbase Fdy Hdy.
  exact (proj2 (proj2 (ts_every_base_position_is_out_of_range x z dy Hbase Fdy Hdy))).
Qed.

Lemma ts_actual_function_entry : forall version ge m e le entry,
  function_entry2 ge (ts_body version) [] m e le entry ->
  exists first second middle,
    Mem.alloc m 0 4 = (middle, first) /\
    Mem.alloc middle 0 2 = (entry, second) /\
    e = PTree.set TS._filler2 (second, tarray tuchar 2)
      (PTree.set TS._filler1 (first, tarray tuchar 4) empty_env).
Proof.
  intros version ge m e le entry Hentry.
  assert (Hvars : fn_vars (ts_body version) =
    [(TS._filler1, tarray tuchar 4); (TS._filler2, tarray tuchar 2)])
    by (destruct version; reflexivity).
  inversion Hentry; subst; clear Hentry.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Halloc : alloc_variables _ _ _ (_ :: _) _ _ |- _ =>
    inversion Halloc; subst; clear Halloc end.
  match goal with Hnil : alloc_variables _ _ _ [] _ _ |- _ =>
    inversion Hnil; subst; clear Hnil end.
  do 3 eexists. repeat split; eauto.
Qed.

(** Include the real local allocations and frees. No caller-supplied local
    environment or frame assumption is used for this complete native call. *)
Definition TripletNativeCallPreservation : Prop :=
  forall version m cb ob oo distance trace after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    TS._gCurrentObject = Some cb ->
  Mem.load Mptr m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 49))) =
    Some (Vint Int.zero) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 53))) =
    Some (Vsingle distance) ->
  Float32.cmp Clt distance ts_threshold = false ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ts_body version)) [] trace after result ->
  trace = E0 /\
  (forall chunk b ofs, Mem.valid_block m b ->
    Mem.load chunk after b ofs = Mem.load chunk m b ofs).

Theorem ts_complete_native_call_preserves_existing_cells : TripletNativeCallPreservation.
Proof.
  intros version m cb ob oo distance trace after result Hsymbol Hcurrent Haction
    Hdistance Hfar Hcall.
  inversion Hcall; subst; clear Hcall.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (ts_actual_function_entry _ _ _ _ _ _ Hentry)
      as (first & second & middle & Halloc1 & Halloc2 & ->) end.
  assert (Hfresh1 : forall b, Mem.valid_block m b -> b <> first).
  { intros b Hb ->. eapply Mem.fresh_block_alloc; [exact Halloc1|exact Hb]. }
  assert (Hvalid : forall b, Mem.valid_block m b -> Mem.valid_block middle b).
  { intros b Hb. eapply Mem.valid_block_alloc; [exact Halloc1|exact Hb]. }
  assert (Hfresh2 : forall b, Mem.valid_block m b -> b <> second).
  { intros b Hb ->. eapply Mem.fresh_block_alloc; [exact Halloc2|apply Hvalid; exact Hb]. }
  assert (Hloads : forall chunk b ofs, Mem.valid_block m b ->
    Mem.load chunk m1 b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hb. erewrite Mem.load_alloc_unchanged; [|exact Halloc2|eauto].
    eapply Mem.load_alloc_unchanged; eauto. }
  assert (Hcb : Mem.valid_block m cb) by (eapply ibcc_loaded_block_valid; exact Hcurrent).
  assert (Hob : Mem.valid_block m ob) by (eapply ibcc_loaded_block_valid; exact Haction).
  match goal with Hbody : ClightBigstep.exec_stmt _ _ ?e ?le m1
      (fn_body (ts_body version)) ?t ?le' ?last ?out |- _ =>
    assert (He : e ! TS._gCurrentObject = None) by reflexivity;
    destruct (ts_native_no_spawn_preserves_all_memory version e le m1 cb ob oo
      distance t le' last out He Hsymbol
      ltac:(rewrite Hloads by exact Hcb; exact Hcurrent)
      ltac:(rewrite Hloads by exact Hob; exact Haction)
      ltac:(rewrite Hloads by exact Hob; exact Hdistance) Hfar Hbody)
      as (Ht & Hlast & Hout); subst end.
  split; [reflexivity|]. intros chunk b ofs Hb.
  match goal with Hfree : Mem.free_list m1 (blocks_of_env ?ge ?locals) = Some after |- _ =>
    rewrite (ifc_free_list_frame (blocks_of_env ge locals) m1 after chunk b ofs
      ltac:(pose proof (Hfresh1 b Hb); pose proof (Hfresh2 b Hb);
        first [change (Forall (fun '(target, _, _) => target <> b)
          [(first, 0, 4); (second, 0, 2)])
        |change (Forall (fun '(target, _, _) => target <> b)
          [(second, 0, 2); (first, 0, 4)])]; repeat constructor; congruence)
      Hfree) end.
  apply Hloads; exact Hb.
Qed.
