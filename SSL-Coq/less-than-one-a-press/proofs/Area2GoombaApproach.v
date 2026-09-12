(** Backward Goomba approach to the pyramid elevator. The full generated
    static mesh classifies nearby support; it does not install a live floor.
    The generated landing code really rebounds a falling Goomba. Thus the
    ordinary jump's height is not a bound on all gameplay histories. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_behavior_data jp_behavior_data
  us_behavior_script jp_behavior_script.
From LessThanOneAPress.Proofs Require Import GameTypes Area1FirstNull
  Area2Rank12BContact Area2Rank10ASupportChange Area2ElevatorCoins
  InkVerticalRetryGeometry EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module GA := us_object_helpers.
Module GB := us_behavior_script.
Module GDG := Area2DownstreamGeometry.

(** Full base enlarged by the regular Goomba/Mario radii, 108+37.
    This is deliberately wider than the interior in which Mario can stand. *)
Definition ga_overlaps vertices loX hiX loZ hiZ := let '(a,b,c) := vertices in
  rank12b_axis_meets (GDG.x_of a) (GDG.x_of b) (GDG.x_of c) loX hiX &&
  rank12b_axis_meets (GDG.z_of a) (GDG.z_of b) (GDG.z_of c) loZ hiZ.
Definition ga_up vertices := 0 <? GDG.y_of (area1_source_normal_components vertices).
Definition ga_near vertices := ga_up vertices && ga_overlaps vertices (-656) 657 (-400) 913.
Definition ga_flat vertices height := let '(a,b,c) := vertices in
  (GDG.y_of a =? height) && (GDG.y_of b =? height) && (GDG.y_of c =? height).
Definition ga_filter version test := filter (fun face => match snd face with
  | Some vertices => test vertices | None => false end) (rank12b_faces version).
Definition ga_nearby version := ga_filter version ga_near.
Definition ga_640 version := ga_filter version (fun v => ga_up v && ga_flat v 640).

(** The displacement allowance is explicit: 55*30+216 = 1866 per axis.
    This is NOT claimed to bound every controller/Goomba/support history. *)
Definition GoombaApproachGeometryCertificate : Prop := forall version,
  length (ga_nearby version) = 53%nat /\
  map fst (filter (fun face => match snd face with
    | Some v => negb (rank10s_low v) | None => false end) (ga_nearby version)) =
    [1025;1037;1062;1064]%nat /\
  forallb (fun face => match snd face with
    | Some v => rank10s_low v || ga_flat v 384 || ga_flat v 896
    | None => false end) (ga_nearby version) = true /\
  length (ga_640 version) = 14%nat /\
  forallb (fun face => match snd face with
    | Some v => negb (ga_overlaps v (-2522) 2523 (-2266) 2779)
    | None => false end) (ga_640 version) = true.
Theorem ga_geometry_checked : GoombaApproachGeometryCertificate.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Lemma ga_overlap_sound : forall vertices x y z loX hiX loZ hiZ,
  rank12b_point_in_vertex_box (x,y,z) vertices ->
  (IZR loX <= x <= IZR hiX)%R -> (IZR loZ <= z <= IZR hiZ)%R ->
  ga_overlaps vertices loX hiX loZ hiZ = true.
Proof.
  intros [[a b] c] x y z lx hx lz hz [Bx [By Bz]] Hx Hz.
  apply andb_true_iff. split; eapply rank12b_axis_meets_sound; eauto.
Qed.

Lemma ga_flat_height : forall vertices x y z height,
  rank12b_point_in_vertex_box (x,y,z) vertices ->
  ga_flat vertices height = true -> y = IZR height.
Proof.
  intros [[a b] c] x y z h [Bx [By Bz]] H.
  cbn [ga_flat] in H. repeat rewrite andb_true_iff in H.
  destruct H as [[Ha Hb] Hc].
  apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. apply Z.eqb_eq in Hc.
  unfold rank12b_min3, rank12b_max3 in By.
  rewrite Ha, Hb, Hc, Z.min_id, Z.max_id, Z.min_id, Z.max_id in By. lra.
Qed.

(** Covers every point in every positive-Y source triangle's vertex box
    over the enlarged footprint, not a finite sample of floor queries. *)
Theorem ga_nearby_support_cases : forall version ordinal vertices x y z,
  In (ordinal,Some vertices) (rank12b_faces version) ->
  0 < GDG.y_of (area1_source_normal_components vertices) ->
  rank12b_point_in_vertex_box (x,y,z) vertices ->
  (-656 <= x <= 657)%R -> (-400 <= z <= 913)%R ->
  (y <= -101)%R \/ y = 384%R \/ y = 896%R.
Proof.
  intros version ordinal vertices x y z Hin Hup Hbox Hx Hz.
  assert (Hnear : In (ordinal,Some vertices) (ga_nearby version)).
  { apply filter_In. split; [exact Hin|]. cbn [snd].
    unfold ga_near. apply andb_true_iff. split.
    - apply Z.ltb_lt. exact Hup.
    - eapply ga_overlap_sound; eauto. }
  pose proof (ga_geometry_checked version) as (_ & _ & Hcases & _).
  rewrite forallb_forall in Hcases. specialize (Hcases _ Hnear).
  cbn [snd] in Hcases. repeat rewrite orb_true_iff in Hcases.
  destruct Hcases as [[Hlow|H384]|H896].
  - left. destruct vertices as [[a b] c]. cbn [rank10s_low] in Hlow.
    apply Z.leb_le in Hlow. apply IZR_le in Hlow.
    unfold rank12b_point_in_vertex_box in Hbox. lra.
  - right; left. eapply ga_flat_height; eauto.
  - right; right. eapply ga_flat_height; eauto.
Qed.

(** The low-support ORDINARY-JUMP case: height 66 and hitbox 75 do not
    bridge the vertical gap even at the nominal lowest bucket jolt, 118.
    The rebound execution below is why these premises cannot be universal. *)
Definition GoombaLowOrdinaryJumpExclusion : Prop := forall floor feet mario,
  (floor <= -101)%R -> (feet <= floor + 66)%R -> (118 <= mario)%R ->
  (feet + 75 < mario)%R.
Theorem ga_low_ordinary_jump_misses : GoombaLowOrdinaryJumpExclusion.
Proof. unfold GoombaLowOrdinaryJumpExclusion; intros; lra. Qed.

Definition GoombaApproachBudgetExclusion : Prop := forall version ordinal vertices
    startX startY startZ endX endZ,
  In (ordinal,Some vertices) (rank12b_faces version) ->
  ga_up vertices = true -> ga_flat vertices 640 = true ->
  rank12b_point_in_vertex_box (startX,startY,startZ) vertices ->
  (-656 <= endX <= 657)%R -> (-400 <= endZ <= 913)%R ->
  (-1866 <= endX-startX <= 1866)%R ->
  (-1866 <= endZ-startZ <= 1866)%R -> False.
Theorem ga_640_requires_more_displacement : GoombaApproachBudgetExclusion.
Proof.
  intros version ordinal vertices sx sy sz ex ez Hin Hup Hflat Hbox Hx Hz Dx Dz.
  assert (H640 : In (ordinal,Some vertices) (ga_640 version)).
  { apply filter_In. split; [exact Hin|]. cbn [snd].
    apply andb_true_iff. auto. }
  pose proof (ga_geometry_checked version) as (_ & _ & _ & _ & Hfar).
  rewrite forallb_forall in Hfar. specialize (Hfar _ H640).
  cbn [snd] in Hfar. apply negb_true_iff in Hfar.
  assert (Hmeet : ga_overlaps vertices (-2522) 2523 (-2266) 2779 = true).
  { eapply ga_overlap_sound; [exact Hbox| |]; cbn; lra. }
  congruence.
Qed.

(** The Goomba script really sets a negative bounce coefficient. Inspect
    both its physics words and the exact decoder expression in US and JP. *)
Definition ga_physics_body version := match version with
| VersionUS => us_behavior_script.f_bhv_cmd_set_obj_physics
| VersionJP => jp_behavior_script.f_bhv_cmd_set_obj_physics end.
Definition ga_decode_from_body version := match fn_body (ga_physics_body version) with
| Ssequence _ (Ssequence _ (Ssequence
    (Ssequence _ (Ssequence _ (Ssequence _ (Sassign _ rhs)))) _)) => rhs
| _ => Econst_int Int.zero tint end.
Definition ga_decode := Ebinop Odiv
  (Ecast (Ebinop Oshr (Etempvar GB._t'17 tuint)
    (Econst_int (Int.repr 16) tint) tuint) tshort)
  (Econst_single (Float32.of_bits (Int.repr 1120403456)) tfloat) tfloat.
Definition ga_coefficient := Float32.of_bits (Int.repr 3204448256). (* -0.5 *)
Theorem ga_stock_physics_checked : forall version,
  firstn 5 (skipn 6 (gvar_init (match version with
    | VersionUS => us_behavior_data.v_bhvGoomba
    | VersionJP => jp_behavior_data.v_bhvGoomba end))) =
  map (fun z => Init_int32 (Int.repr z))
    [805306368;2686576;-3275800;65536000;0] /\
  ga_decode_from_body version = ga_decode.
Proof. intros []; split; reflexivity. Qed.

Definition GoombaCoefficientDecodeExecution : Prop := forall version ge e le m,
  le ! GB._t'17 = Some (Vint (Int.repr (-3275800))) ->
  eval_expr ge e le m (ga_decode_from_body version) (Vsingle ga_coefficient).
Theorem ga_real_coefficient_decode : GoombaCoefficientDecodeExecution.
Proof.
  intros version ge e le m Hword.
  rewrite (proj2 (ga_stock_physics_checked version)). unfold ga_decode.
  eapply eval_Ebinop.
  - eapply eval_Ecast.
    + eapply eval_Ebinop; [apply eval_Etempvar; exact Hword|constructor|reflexivity].
    + reflexivity.
  - constructor.
  - change (Some (Vsingle (Float32.div (Float32.of_int (Int.repr (-50)))
      (Float32.of_bits (Int.repr 1120403456)))) = Some (Vsingle ga_coefficient)).
    f_equal. f_equal.
    rewrite <- (Float32.of_to_bits (Float32.div (Float32.of_int (Int.repr (-50)))
      (Float32.of_bits (Int.repr 1120403456)))).
    vm_compute. reflexivity.
Qed.

(** Extract the complete negative-velocity test and bounce store, after the
    selected-height copy. Earlier floor lookup/flag handling is NOT assumed
    harmless. This local execution starts after those operations. *)
Definition ga_bounce_from_body version := match fn_body (ec_ground_air_body version) with
| Ssequence _ (Ssequence
    (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
      (Sifthenelse _ (Ssequence _ (Ssequence _ (Ssequence bounce _))) _))))) _) => bounce
| _ => Sskip end.
Definition ga_vy version temporary := rank15_raw_float_expression version temporary
  (Econst_int (Int.repr 10) tint).
Definition ga_bounce version := Ssequence
  (Sset GA._t'22 rank15_current_object_expression)
  (Ssequence (Sset GA._t'23 (ga_vy version GA._t'22))
    (Sifthenelse (Ebinop Olt (Etempvar GA._t'23 tfloat)
      (Econst_single (Float32.of_bits Int.zero) tfloat) tint)
      (Ssequence (Sset GA._t'24 rank15_current_object_expression)
        (Ssequence (Sset GA._t'25 rank15_current_object_expression)
          (Ssequence (Sset GA._t'26 (ga_vy version GA._t'25))
            (Sassign (ga_vy version GA._t'24)
              (Ebinop Omul (Etempvar GA._t'26 tfloat)
                (Etempvar GA._bounciness tfloat) tfloat))))) Sskip)).
Theorem ga_bounce_is_generated : forall version,
  ga_bounce_from_body version = ga_bounce version.
Proof. intros []; reflexivity. Qed.
Definition ga_bounce_locals le object incoming :=
  PTree.set GA._t'26 (Vsingle incoming)
    (PTree.set GA._t'25 object (PTree.set GA._t'24 object
      (PTree.set GA._t'23 (Vsingle incoming) (PTree.set GA._t'22 object le)))).

Definition GoombaLandingBounceExecution : Prop :=
  forall version e le m cb ob oo incoming,
  e ! GA._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    GA._gCurrentObject = Some cb ->
  Mem.load Mptr m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 10))) =
    Some (Vsingle incoming) ->
  le ! GA._bounciness = Some (Vsingle ga_coefficient) ->
  Float32.cmp Clt incoming (Float32.of_bits Int.zero) = true ->
  Mem.valid_access m Mfloat32 ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 10))) Writable ->
  exists after,
    ClightBigstep.Clight2.exec_stmt
      (Clight.globalenv (selected_clight_target version)) e le m
      (ga_bounce_from_body version) E0 (ga_bounce_locals le (Vptr ob oo) incoming)
      after Out_normal /\
    Mem.load Mfloat32 after ob
      (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 10))) =
      Some (Vsingle (Float32.mul incoming ga_coefficient)) /\
    (forall chunk rb ro,
      rb <> ob \/ ro + size_chunk chunk <=
        Ptrofs.unsigned (rank15_raw_address oo (Int.repr 10)) \/
      Ptrofs.unsigned (rank15_raw_address oo (Int.repr 10)) + 4 <= ro ->
      Mem.load chunk after rb ro = Mem.load chunk m rb ro).

Theorem ga_real_landing_rebounds : GoombaLandingBounceExecution.
Proof.
  intros version e le m cb ob oo incoming Hlocal Hsymbol Hcurrent Hvy Hcoef Hneg Haccess.
  destruct (Mem.valid_access_store m Mfloat32 ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 10)))
    (Vsingle (Float32.mul incoming ga_coefficient)) Haccess) as [after Hstore].
  exists after. split.
  - rewrite ga_bounce_is_generated. unfold ga_bounce, ga_bounce_locals, ga_vy.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply rank15_current_object_read; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply rank15_raw_float_read;
          [apply PTree.gss|constructor|reflexivity|exact Hvy].
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        -- eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|constructor|].
           change (Some (Val.of_bool (Float32.cmp Clt incoming
             (Float32.of_bits Int.zero))) = Some (Vint Int.one)).
           rewrite Hneg. reflexivity.
        -- reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_Sset. eapply rank15_current_object_read; eauto.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** apply exec_Sset. eapply rank15_current_object_read; eauto.
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- apply exec_Sset. eapply rank15_raw_float_read;
                       [apply PTree.gss|constructor|reflexivity|exact Hvy].
                 --- eapply exec_Sassign with (loc := ob)
                       (ofs := rank15_raw_address oo (Int.repr 10)) (bf := Full)
                       (v := Vsingle (Float32.mul incoming ga_coefficient))
                       (v2 := Vsingle (Float32.mul incoming ga_coefficient)).
                     +++ eapply rank15_raw_float_lvalue.
                         *** repeat rewrite PTree.gso by discriminate. apply PTree.gss.
                         *** constructor.
                         *** reflexivity.
                     +++ eapply eval_Ebinop.
                         *** apply eval_Etempvar. apply PTree.gss.
                         *** apply eval_Etempvar.
                             repeat rewrite PTree.gso by discriminate. exact Hcoef.
                         *** reflexivity.
                     +++ reflexivity.
                     +++ eapply assign_loc_value with (chunk := Mfloat32);
                           [reflexivity|exact Hstore].
  - split.
    + exact (Mem.load_store_same _ _ _ _ _ _ Hstore).
    + intros chunk rb ro Hsep. eapply Mem.load_store_other; [exact Hstore|].
      destruct Hsep as [H|[H|H]]; auto.
Qed.

(** Fixed-parameter arithmetic following the actual rebound: no claim that
    earlier gameplay supplies the impact, or that subsequent calls preserve
    these parameters and do not select a floor. *)
Fixpoint ga_isolated_rise count y velocity : list Floats.float32 :=
  match count with O => [] | S remaining =>
    let vy := Float32.add velocity (area1_f32_of_Z (-4)) in
    let next := Float32.add y vy in next :: ga_isolated_rise remaining next vy end.
Definition GoombaHardBounceArithmetic : Prop :=
  Float32.cmp Clt (area1_f32_of_Z (-76)) (Float32.of_bits Int.zero) = true /\
  Float32.to_bits (Float32.mul (area1_f32_of_Z (-76)) ga_coefficient) =
    Float32.to_bits (area1_f32_of_Z 38) /\
  map Float32.to_bits (ga_isolated_rise 9 (area1_f32_of_Z (-101))
    (Float32.mul (area1_f32_of_Z (-76)) ga_coefficient)) =
    map (fun z => Float32.to_bits (area1_f32_of_Z z)) [-67;-37;-11;11;29;43;53;59;61] /\
  61 + 75 >= 128 /\ 61 + 78 >= 128.
Theorem ga_hard_bounce_arithmetic_checked : GoombaHardBounceArithmetic.
Proof. vm_compute; repeat split; congruence. Qed.

(** A concrete exterior support, rather than treating the coarse -101
    vertex bound as a floor at any chosen point. Mario's granted pose is
    (-410,128,-154); the Goomba's X/Z is (-551,-187). Its current position
    is outside the base, and the two nominal wall clearances are respected.
    A terminal-speed rebound has enough height for the broad contact test.
    This does not execute sqrtf, fill collision records, select an attack,
    or construct the high falling predecessor. *)
Definition ga_side_face : (Z * Z * Z)%type := (50,137,126).
Definition ga_side_query y : Area1IntegerQuery :=
  {| area1_query_x := -551; area1_query_y := y; area1_query_z := -187 |}.
Definition ga_side_peak height := nth 8
  (ga_isolated_rise 9 height (Float32.mul (area1_f32_of_Z (-78)) ga_coefficient))
  (area1_f32_of_Z 0).
Definition GoombaSideContactGeometry : Prop := forall version,
  nth_error (rank12b_triangles version) 1314 = Some ga_side_face /\
  ivr_accepts (rank12b_vertices version) (ga_side_query (-112)) ga_side_face = true /\
  filter (ivr_accepts (ec_bottom_vertices version) (ga_side_query 1000))
    ec_base_faces = [] /\
  (match area1_loaded_floor_height (rank12b_vertices version) ga_side_face (-551) (-187) with
  | Some height =>
      Float32.cmp Cgt height (area1_f32_of_Z (-113)) = true /\
      Float32.cmp Clt height (area1_f32_of_Z (-112)) = true /\
      Float32.cmp Cgt (ga_side_peak height) (area1_f32_of_Z 58) = true /\
      Float32.cmp Clt (ga_side_peak height) (area1_f32_of_Z 59) = true /\
      Float32.cmp Cgt (Float32.add (ga_side_peak height) (area1_f32_of_Z 75))
        (area1_f32_of_Z 128) = true
  | None => False end) /\
  (-551 - (-410))^2 + (-187 - (-154))^2 < (108+37)^2 /\
  -551 + 40 = -511 /\ -410 - 50 = -460 /\ -154 - 50 = -204.
Theorem ga_side_contact_geometry_checked : GoombaSideContactGeometry.
Proof. intros []; vm_compute; repeat split; congruence. Qed.

Definition GoombaNearbySupportCases : Prop := forall version ordinal vertices x y z,
  In (ordinal,Some vertices) (rank12b_faces version) ->
  0 < GDG.y_of (area1_source_normal_components vertices) ->
  rank12b_point_in_vertex_box (x,y,z) vertices ->
  (-656 <= x <= 657)%R -> (-400 <= z <= 913)%R ->
  (y <= -101)%R \/ y = 384%R \/ y = 896%R.
Definition Area2GoombaApproachBoundary : Prop :=
  GoombaApproachGeometryCertificate /\ GoombaNearbySupportCases /\
  GoombaLowOrdinaryJumpExclusion /\ GoombaApproachBudgetExclusion /\
  GoombaCoefficientDecodeExecution /\ GoombaLandingBounceExecution /\
  GoombaHardBounceArithmetic /\ GoombaSideContactGeometry.
Theorem ga_approach_boundary_checked : Area2GoombaApproachBoundary.
Proof.
  split; [exact ga_geometry_checked|].
  split; [exact ga_nearby_support_cases|].
  split; [exact ga_low_ordinary_jump_misses|].
  split; [exact ga_640_requires_more_displacement|].
  split; [exact ga_real_coefficient_decode|].
  split; [exact ga_real_landing_rebounds|].
  split; [exact ga_hard_bounce_arithmetic_checked|exact ga_side_contact_geometry_checked].
Qed.
