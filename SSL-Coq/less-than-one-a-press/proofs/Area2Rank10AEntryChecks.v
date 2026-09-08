(** Rank 10A: ordinary elevator jolts and nearby hanging entry.
    Generated US/JP data and actual geometry-input guard, not a claim that
    every live frame has already been projected. Same-base selection,
    one-unit pose agreement, normal timing and ceiling freshness stay explicit. *)
From Coq Require Import Bool Lia List ZArith Reals Lra.
From Flocq Require Import Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_math_util jp_math_util
  us_ssl_collision jp_ssl_collision us_obj_behaviors jp_obj_behaviors
  us_mario jp_mario.
From LessThanOneAPress.Proofs Require Import ASTFacts GameTypes Area1FirstNull
  CollisionMeshFacts Area2ElevatorCut Area2Rank9ACoinFlight Area2Rank10AGroundPound
  Area2Rank11LivePoleExit EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Float32.cmp Float32.compare.
Module E := us_obj_behaviors.
Module M := us_mario.

(** All five elevator-height RHSs, in their actual source order. *)
Fixpoint rank10e_y_rhs (s : statement) : list expr := match s with
| Sassign lhs rhs => if expression_is_array_slot E._asF32 7 lhs then [rhs] else []
| Ssequence a b | Sloop a b | Sifthenelse _ a b => rank10e_y_rhs a ++ rank10e_y_rhs b
| Sswitch _ cases => rank10e_y_rhs_cases cases
| Slabel _ body => rank10e_y_rhs body
| _ => [] end
with rank10e_y_rhs_cases (cases : labeled_statements) : list expr := match cases with
| LSnil => [] | LScons _ body rest => rank10e_y_rhs body ++ rank10e_y_rhs_cases rest end.
Definition rank10e_float bits := Econst_single (Float32.of_bits (Int.repr bits)) tfloat.
Definition rank10e_expected_y_rhs :=
  [Ebinop Osub (Etempvar E._t'26 tfloat)
     (Ebinop Omul (Etempvar E._t'29 tfloat) (rank10e_float 1092616192) tfloat) tfloat;
   Ebinop Oadd (Etempvar E._t'17 tfloat) (Etempvar E._t'19 tfloat) tfloat;
   rank10e_float 1124073472;
   Ebinop Oadd (Ebinop Omul (Etempvar E._t'10 tfloat) (rank10e_float 1092616192) tfloat)
     (rank10e_float 1124073472) tfloat;
   rank10e_float 1124073472].
Theorem rank10e_height_expressions_are_generated : forall version,
  rank10e_y_rhs (fn_body (rank10a_body version GPElevator)) = rank10e_expected_y_rhs /\
  direct_callees_s (fn_body (rank10a_body version GPElevator)) = [].
Proof. intros []; split; reflexivity. Qed.

(** A full nominal cycle from the recorded home height. Waits may repeat
    samples; skipping a Mario reanchor is NOT such a wait. *)
Definition rank10e_sine version timer : float32 :=
  match nth (timer * 256)%nat
    (gvar_init (match version with VersionUS => us_math_util.v_gSineTable
      | VersionJP => jp_math_util.v_gSineTable end)) (Init_space 0) with
  | Init_float32 value => value | _ => rank9cf_integer 0 end.
Definition Rank10ESineSamplesInitialized : Prop := forall version,
  map (fun timer => nth_error
    (gvar_init (match version with VersionUS => us_math_util.v_gSineTable
      | VersionJP => jp_math_util.v_gSineTable end)) (timer * 256)%nat) (seq 0 9) =
  map (fun timer => Some (Init_float32 (rank10e_sine version timer))) (seq 0 9).
Theorem rank10e_sine_samples_are_initialized : Rank10ESineSamplesInitialized.
Proof. intros []; reflexivity. Qed.
Definition rank10e_start version timer := Float32.sub (rank9cf_integer 4966)
  (Float32.mul (rank10e_sine version timer) (rank9cf_integer 10)).
Definition rank10e_stop version timer :=
  if Nat.ltb timer 8 then Float32.add
    (Float32.mul (rank10e_sine version timer) (rank9cf_integer 10)) (rank9cf_integer 128)
  else rank9cf_integer 128.
Fixpoint rank10e_descend fuel y : list float32 := match fuel with
| O => [] | S rest =>
  let moved := Float32.add y (rank9cf_integer (-10)) in
  let next := if Float32.cmp Clt moved (rank9cf_integer 128)
    then rank9cf_integer 128 else moved in
  next :: rank10e_descend rest next end.
Definition rank10e_cycle version :=
  [rank9cf_integer 4966] ++ map (rank10e_start version) (seq 0 9) ++
  rank10e_descend 484 (rank9cf_integer 4966) ++
  map (rank10e_stop version) (seq 0 9) ++ [rank9cf_integer 128].
Fixpoint rank10e_pairs (ys : list float32) : list (float32 * float32) :=
  match ys with a :: ((b :: _) as rest) => (a,b) :: rank10e_pairs rest | _ => [] end.
Definition rank10e_pairs_with_waits version := rank10e_pairs (rank10e_cycle version) ++
  map (fun y => (y,y)) (rank10e_cycle version).
Definition rank10e_bin y := match Float32.to_int y with
| Some n => Int.signed n | None => 0 end.
Definition rank10e_pair_check (p : float32 * float32) : bool :=
  let '(before, after) := p in let bin := rank10e_bin before in
  (-16000 <=? bin) && (bin <=? 16000) && is_finite 24 128 before && is_finite 24 128 after &&
  negb (Float32.cmp Clt before (rank9cf_integer bin)) &&
  negb (Float32.cmp Clt (rank9cf_integer (bin+1)) before) &&
  negb (Float32.cmp Clt after (rank9cf_integer (bin-10))) &&
  negb (Float32.cmp Clt (rank9cf_integer (bin+10)) after).
Definition Rank10ENominalCycleChecked : Prop := forall version,
  length (rank10e_cycle version) = 504%nat /\
  Float32.to_bits (rank10e_start version 8) = Float32.to_bits (rank9cf_integer 4966) /\
  forallb rank10e_pair_check (rank10e_pairs_with_waits version) = true.
Theorem rank10e_nominal_cycle_checked : Rank10ENominalCycleChecked.
Proof. intros []; vm_compute; auto. Qed.

Lemma rank10e_pair_bounds : forall version before after,
  In (before,after) (rank10e_pairs_with_waits version) ->
  let bin := rank10e_bin before in
  -16000 <= bin <= 16000 /\
  (IZR bin <= rank9cf_real before <= IZR (bin+1))%R /\
  (IZR (bin-10) <= rank9cf_real after <= IZR (bin+10))%R.
Proof.
  intros version before after Hin bin.
  destruct (rank10e_nominal_cycle_checked version) as [_ [_ H]].
  rewrite forallb_forall in H. specialize (H (before,after) Hin).
  unfold rank10e_pair_check in H. fold bin in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[[Hlo Hhi] Fb] Fa] Hb0] Hb1] Ha0] Ha1].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  apply negb_true_iff in Hb0, Hb1, Ha0, Ha1.
  destruct (rank9cf_integer_exact bin ltac:(lia)) as [R0 F0].
  destruct (rank9cf_integer_exact (bin+1) ltac:(lia)) as [R1 F1].
  destruct (rank9cf_integer_exact (bin-10) ltac:(lia)) as [Rl Fl].
  destruct (rank9cf_integer_exact (bin+10) ltac:(lia)) as [Rh Fh].
  pose proof (rank9cf_less_false _ _ Fb F0 Hb0).
  pose proof (rank9cf_less_false _ _ F1 Fb Hb1).
  pose proof (rank9cf_less_false _ _ Fa Fl Ha0).
  pose proof (rank9cf_less_false _ _ Fh Fa Ha1).
  rewrite R0 in *. rewrite R1 in *. rewrite Rl in *. rewrite Rh in *.
  repeat split; try lia; lra.
Qed.

(** The margin is deliberately larger than exact base truncation: allow one
    unit at BOTH pose samples. A live floor projection must establish it. *)
Theorem rank10e_same_base_guard_false : forall version before after y floor,
  In (before,after) (rank10e_pairs_with_waits version) ->
  rank9cf_finite y -> rank9cf_finite floor ->
  (rank9cf_real before - 1 <= rank9cf_real y <= rank9cf_real before + 1)%R ->
  (rank9cf_real after - 1 <= rank9cf_real floor <= rank9cf_real after + 1)%R ->
  Float32.cmp Cgt y (Float32.add floor (rank9cf_integer 100)) = false.
Proof.
  intros version before after y floor Hp Fy Ff Hy Hf.
  destruct (rank10e_pair_bounds version before after Hp) as [Hb [Hbefore Hafter]].
  set (bin := rank10e_bin before) in *.
  destruct (rank9cf_integer_exact 100 ltac:(lia)) as [R100 F100].
  destruct (rank9cf_add_range floor (rank9cf_integer 100) (bin+89) (bin+111)
    Ff F100 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite R100; repeat rewrite plus_IZR in *; rewrite minus_IZR in Hafter; lra))
    as [Ft Hthreshold].
  assert (Hlt : (rank9cf_real y < rank9cf_real
    (Float32.add floor (rank9cf_integer 100)))%R).
  { repeat rewrite plus_IZR in *; rewrite minus_IZR in Hafter; lra. }
  unfold Float32.cmp, Float32.compare.
  rewrite Bcompare_correct by assumption. rewrite Rcompare_Lt by exact Hlt. reflexivity.
Qed.

(** The actual no-floor-distance guard is a connected Clight fragment. *)
Definition rank10e_guard yes :=
  Ssequence (Sset M._t'18 rank11_mario_y_expression)
    (Ssequence (Sset M._t'19 (rank11_mario_field_expression M._floorHeight tfloat))
      (Sifthenelse (Ebinop Ogt (Etempvar M._t'18 tfloat)
        (Ebinop Oadd (Etempvar M._t'19 tfloat) (rank10e_float 1120403456) tfloat) tint) yes Sskip)).
Fixpoint rank10e_find_guard (s : statement) : option statement :=
  match s with
  | Ssequence (Sset id _) (Ssequence (Sset id' _) (Sifthenelse _ _ _)) =>
      if Pos.eqb id M._t'18 && Pos.eqb id' M._t'19 then Some s else
      match s with Ssequence a b =>
        match rank10e_find_guard a with Some r => Some r | None => rank10e_find_guard b end
      | _ => None end
  | Ssequence a b | Sifthenelse _ a b =>
      match rank10e_find_guard a with Some r => Some r | None => rank10e_find_guard b end
  | _ => None end.
Theorem rank10e_guard_is_generated : forall version, exists yes,
  rank10e_find_guard (fn_body (rank10a_body version GPGeometryInputs)) = Some (rank10e_guard yes).
Proof. intros []; eexists; reflexivity. Qed.

Lemma rank10e_floor_field_layout : forall version,
  exists description,
    (genv_cenv (Clight.globalenv (selected_clight_target version))) ! M._MarioState = Some description /\
    field_offset (Clight.globalenv (selected_clight_target version)) M._floorHeight
      (co_members description) = OK (112, Full).
Proof.
  intro version.
  assert (H : match (rank15_selected_header_environment version) ! M._MarioState with
    | Some d => rank11_field_offset_check (rank15_selected_header_environment version)
        (co_members d) M._floorHeight 112 = true | None => False end).
  { destruct version; vm_compute; reflexivity. }
  rewrite rank15_selected_header_environment_exact in H.
  destruct ((prog_comp_env (selected_clight_target version)) ! M._MarioState) as [d|] eqn:E;
    [|contradiction]. exists d. split; [exact E|].
  now apply rank11_field_offset_check_sound in H.
Qed.
Lemma rank10e_floor_read : forall version environment locals memory mario floor,
  locals ! M._m = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mfloat32 memory mario 112 = Some (Vsingle floor) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) environment locals memory
    (rank11_mario_field_expression M._floorHeight tfloat) (Vsingle floor).
Proof.
  intros version environment locals memory mario floor Hm Hload.
  destruct (rank10e_floor_field_layout version) as [d [Hd Ho]].
  eapply eval_Elvalue with (ofs := Ptrofs.repr 112) (bf := Full).
  - unfold rank11_mario_field_expression.
    replace (Ptrofs.repr 112) with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 112)) by reflexivity.
    eapply eval_Efield_struct with (co := d).
    + eapply eval_Elvalue; [apply eval_Ederef; apply eval_Etempvar; exact Hm |].
      apply deref_loc_copy. reflexivity.
    + reflexivity.
    + exact Hd.
    + exact Ho.
  - eapply deref_loc_value with (chunk := Mfloat32); eauto.
Qed.
Definition Rank10AEntryGuardExecution : Prop := forall version environment locals memory
    mario before after y floor yes,
  In (before,after) (rank10e_pairs_with_waits version) ->
  rank9cf_finite y -> rank9cf_finite floor ->
  (rank9cf_real before - 1 <= rank9cf_real y <= rank9cf_real before + 1)%R ->
  (rank9cf_real after - 1 <= rank9cf_real floor <= rank9cf_real after + 1)%R ->
  locals ! M._m = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mfloat32 memory mario 64 = Some (Vsingle y) ->
  Mem.load Mfloat32 memory mario 112 = Some (Vsingle floor) ->
  ClightBigstep.Clight2.exec_stmt (Clight.globalenv (selected_clight_target version))
    environment locals memory (rank10e_guard yes) E0
    (PTree.set M._t'19 (Vsingle floor) (PTree.set M._t'18 (Vsingle y) locals)) memory Out_normal.
Theorem rank10e_geometry_guard_executes_skip : Rank10AEntryGuardExecution.
Proof.
  unfold Rank10AEntryGuardExecution.
  intros version environment locals memory mario before after y floor yes
    Hp Fy Ff Hy Hf Hm Hloady Hloadf.
  pose proof (rank10e_same_base_guard_false version before after y floor Hp Fy Ff Hy Hf) as Hcmp.
  unfold rank10e_guard. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_Sset. eapply rank11_mario_y_read; eauto.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply rank10e_floor_read; eauto.
      rewrite PTree.gso by discriminate. exact Hm.
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      * eapply eval_Ebinop.
        -- apply eval_Etempvar. rewrite PTree.gso by discriminate. apply PTree.gss.
        -- eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss | constructor | reflexivity].
        -- change (Some (Val.of_bool (Float32.cmp Cgt y
             (Float32.add floor (Float32.of_bits (Int.repr 1120403456))))) = Some (Vint Int.zero)).
           assert (H100 : Float32.of_bits (Int.repr 1120403456) = rank9cf_integer 100)
             by (apply rank9cf_bits_injective; vm_compute; reflexivity).
           rewrite H100, Hcmp. reflexivity.
      * reflexivity.
      * constructor.
Qed.

(** Preserve surface types while parsing every group; require the real end
    marker so a prematurely stopped parser cannot certify completeness. *)
Fixpoint rank10e_hangable_groups fuel words : option (list Area1TriangleIndex) :=
  match fuel with O => None | S rest => match words with
  | surface_type :: count :: tail =>
    if Z.eqb surface_type 65 then Some [] else
    if area1_source_is_surface_type surface_type then
      let '(triangles,suffix) := area1_parse_triangle_records (Z.to_nat count)
        (if area1_source_surface_has_force surface_type then 4%nat else 3%nat) tail in
      match rank10e_hangable_groups rest suffix with
      | Some later => Some ((if Z.eqb surface_type 5 then triangles else []) ++ later)
      | None => None end
    else None
  | _ => None end end.
Definition rank10e_hangable_stream words :=
  rank10e_hangable_groups 32 (skipn (2 + 3 * Z.to_nat (nth 1 words 0)) words).
Definition rank10e_hangable_indices :=
  [(18,19,20); (18,21,19); (21,22,23); (21,18,22); (24,25,26); (24,27,25)].
Definition rank10e_static_words version := match version with
| VersionUS => area2_collision_words_us | VersionJP => area2_collision_words_jp end.
Definition rank10e_hangable_faces version := map
  (area1_source_triangle_vertices (collision_vertices_from_words 1080 (rank10e_static_words version)))
  rank10e_hangable_indices.
Definition rank10e_moving_meshes version := match version with
| VersionUS => [us_ssl_collision.v_ssl_seg7_collision_grindel;
    us_ssl_collision.v_ssl_seg7_collision_spindel; us_ssl_collision.v_ssl_seg7_collision_0702808C;
    us_ssl_collision.v_ssl_seg7_collision_pyramid_elevator]
| VersionJP => [jp_ssl_collision.v_ssl_seg7_collision_grindel;
    jp_ssl_collision.v_ssl_seg7_collision_spindel; jp_ssl_collision.v_ssl_seg7_collision_0702808C;
    jp_ssl_collision.v_ssl_seg7_collision_pyramid_elevator] end.
Theorem rank10e_hangable_inventory_is_complete : forall version,
  rank10e_hangable_stream (rank10e_static_words version) = Some rank10e_hangable_indices /\
  map (fun v => rank10e_hangable_stream (init_int16_values (gvar_init v)))
    (rank10e_moving_meshes version) = [Some []; Some []; Some []; Some []].
Proof. intros []; vm_compute; auto. Qed.
Definition rank10e_face_box_contains x z face : Prop := match face with
| Some (a,b,c) =>
    Z.min (vertex_x a) (Z.min (vertex_x b) (vertex_x c)) <= x <=
      Z.max (vertex_x a) (Z.max (vertex_x b) (vertex_x c)) /\
    Z.min (vertex_z a) (Z.min (vertex_z b) (vertex_z c)) <= z <=
      Z.max (vertex_z a) (Z.max (vertex_z b) (vertex_z c))
| None => False end.
Theorem rank10e_no_hangable_face_over_bucket : forall version face x z,
  In face (rank10e_hangable_faces version) ->
  -511 <= x <= 512 -> -255 <= z <= 768 ->
  ~ rank10e_face_box_contains x z face.
Proof.
  intros version face x z Hin Hx Hz.
  destruct version; vm_compute in Hin;
    repeat destruct Hin as [Hin|Hin]; try contradiction; subst face;
    cbn [rank10e_face_box_contains vertex_x vertex_z]; lia.
Qed.

Definition Rank10AEntryChecksBoundary : Prop :=
  (forall version, rank10e_y_rhs (fn_body (rank10a_body version GPElevator)) = rank10e_expected_y_rhs) /\
  Rank10ESineSamplesInitialized /\
  Rank10ENominalCycleChecked /\
  Rank10AEntryGuardExecution /\
  (forall version, exists yes, rank10e_find_guard
    (fn_body (rank10a_body version GPGeometryInputs)) = Some (rank10e_guard yes)) /\
  (forall version before after y floor,
    In (before,after) (rank10e_pairs_with_waits version) ->
    rank9cf_finite y -> rank9cf_finite floor ->
    (rank9cf_real before - 1 <= rank9cf_real y <= rank9cf_real before + 1)%R ->
    (rank9cf_real after - 1 <= rank9cf_real floor <= rank9cf_real after + 1)%R ->
    Float32.cmp Cgt y (Float32.add floor (rank9cf_integer 100)) = false) /\
  (forall version, rank10e_hangable_stream (rank10e_static_words version) = Some rank10e_hangable_indices /\
    map (fun v => rank10e_hangable_stream (init_int16_values (gvar_init v)))
      (rank10e_moving_meshes version) = [Some []; Some []; Some []; Some []]) /\
  (forall version face x z, In face (rank10e_hangable_faces version) ->
    -511 <= x <= 512 -> -255 <= z <= 768 -> ~ rank10e_face_box_contains x z face).
Theorem rank10e_entry_checks_boundary_checked : Rank10AEntryChecksBoundary.
Proof.
  split; [intro version; exact (proj1 (rank10e_height_expressions_are_generated version))|].
  split; [exact rank10e_sine_samples_are_initialized|].
  split; [exact rank10e_nominal_cycle_checked|].
  split; [exact rank10e_geometry_guard_executes_skip|].
  split; [exact rank10e_guard_is_generated|].
  split; [exact rank10e_same_base_guard_false|].
  split; [exact rank10e_hangable_inventory_is_complete|
    exact rank10e_no_hangable_face_over_bucket].
Qed.
