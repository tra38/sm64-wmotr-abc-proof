(** Rank 10A: distinguish a stopped quarter before floor alignment from the
    ordinary wall response AFTER alignment. The low-gap execution case is
    new; it complements the existing high-gap and missing-floor cuts.

    Geometry is a complete census of source triangles, not a live-list
    theorem. Query coordinates, loaded planes, other dynamic owners and
    whole-frame preservation are still explicit, separate obligations. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From Flocq Require Import Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_surface_collision jp_surface_collision.
From LessThanOneAPress.Proofs Require Import GameTypes Area1FirstNull
  Area2Rank10ASupportChange Area2Rank10AEntryChecks Area2Rank9ACoinFlight Area2Rank12BContact
  Area2SlideKickEnvelope InkFloorHistorySource InkFloorHistoryExecution
  InkFloorHistoryBackward InkFloorHistoryCall InkBackwardSource InkBackwardExecution
  ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Float32.cmp Float32.compare.
Module BC := us_surface_collision.

Lemma rank10b_floor_ceil_test : forall ge e le m floor ceiling choice,
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  le ! IFH._ceilHeight = Some (Vsingle ceiling) ->
  ocn_test_value ge e le m ifh_floor_ceil_guard choice ->
  choice = Float32.cmp Cge (Float32.add floor ifh_160) ceiling.
Proof.
  intros ge e le m floor ceiling choice Hfloor Hceiling [answer [Hread Hbool]].
  unfold ifh_floor_ceil_guard in Hread.
  repeat match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hr; subst; clear Hr end.
  all: try solve [match goal with Hb : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hb end].
  all: repeat match goal with
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._floorHeight _) ?v |- _ =>
      assert (v = Vsingle floor) by (eapply ocn_temp_value; eauto); subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._ceilHeight _) ?v |- _ =>
      assert (v = Vsingle ceiling) by (eapply ocn_temp_value; eauto); subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ => inversion Hr; subst; clear Hr
  end.
  all: try solve [match goal with Hb : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion Hb end].
  all: repeat match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    progress (cbn in Hsem; inversion Hsem; subst; clear Hsem) end.
  change (bool_val (Val.of_bool (Float32.cmp Cge (Float32.add floor ifh_160) ceiling))
    tint m = Some choice) in Hbool.
  destruct (Float32.cmp Cge (Float32.add floor ifh_160) ceiling).
  - change (Some true = Some choice) in Hbool. congruence.
  - change (Some false = Some choice) in Hbool. congruence.
Qed.

(** No premise says that this quarter aligns Mario. The actual low-gap tail
    must either take the ceiling return, without a memory write, or reach
    the real vec3f_set/floor-pointer/floor-height continuation. *)
Definition Rank10BLowGapQuarterCut : Prop :=
  forall version e le m nb no y floor ceiling t le' m' out,
  le ! IFH._nextPos = Some (Vptr nb no) ->
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  le ! IFH._ceilHeight = Some (Vsingle ceiling) ->
  Mem.load Mfloat32 m nb (Ptrofs.unsigned (Ptrofs.add no (Ptrofs.repr 4))) = Some (Vsingle y) ->
  Float32.cmp Cgt y (Float32.add floor ifh_100) = false ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_post_water version) t le' m' out ->
  (Float32.cmp Cge (Float32.add floor ifh_160) ceiling = true /\
    t = E0 /\ m' = m /\ out = ifh_returned 2) \/
  (Float32.cmp Cge (Float32.add floor ifh_160) ceiling = false /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IFH._t'16 (Vsingle y) le) m
      (ifh_accept version) t le' m' out).

Theorem rank10b_low_gap_stops_for_ceiling_or_reaches_alignment : Rank10BLowGapQuarterCut.
Proof.
  unfold Rank10BLowGapQuarterCut.
  intros version e le m nb no y floor ceiling t le' m' out
    Hnext Hfloor Hceiling Hload Hlow Hrun.
  assert (ifh_post_water version = Ssequence (ifh_vertical version)
    (Ssequence (ifh_floor_ceil version) (ifh_accept version))) as Hpost
    by (destruct version; reflexivity).
  destruct (ifh_quarter_source_cuts version)
    as (_ & _ & _ & _ & _ & _ & _ & Hvertical & _ & Hceil & _).
  rewrite Hpost, Hvertical in Hrun.
  apply ifh_sequence_reassociate in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IFH._t'16 (ifh_next 1))
    _ _ _ _ _ eq_refl Hrun) as (middle & memory & pre & rest & Htrace & Hset & Hrest).
  inversion Hset; subst; clear Hset.
  match goal with Hr : eval_expr _ _ _ _ (ifh_next 1) ?v |- _ =>
    assert (v = Vsingle y) by (eapply ifh_next_height_read; eauto); subst v; clear Hr end.
  inversion Hrest; subst.
  all: match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
    inversion Hg; subst; clear Hg end.
  all: assert (b = false) as Hb by
    (assert (b = Float32.cmp Cgt y (Float32.add floor ifh_100)) as Htest by
      (eapply ifh_leave_test;
        [apply PTree.gss|rewrite PTree.gso by discriminate; exact Hfloor|
         unfold ocn_test_value; eauto]); congruence).
  all: subst b.
  all: match goal with Hs : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
    inversion Hs; subst; clear Hs end.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
        (Ssequence (ifh_floor_ceil _) _) _ _ _ _ |- _ =>
      rewrite Hceil in Hr;
      destruct (ifh_return_gate _ _ _ _ _ _ _ _ _ _ _ Hr) as [Hstop|Haccept] end.
    + destruct Hstop as (Htest & -> & -> & -> & ->).
      pose proof (rank10b_floor_ceil_test _ _ (PTree.set IFH._t'16 (Vsingle y) le) _ floor ceiling true
        ltac:(rewrite PTree.gso by discriminate; exact Hfloor)
        ltac:(rewrite PTree.gso by discriminate; exact Hceiling) Htest).
      left. repeat apply conj; try reflexivity; congruence.
    + destruct Haccept as [Htest Haccept].
      pose proof (rank10b_floor_ceil_test _ _ (PTree.set IFH._t'16 (Vsingle y) le) _ floor ceiling false
        ltac:(rewrite PTree.gso by discriminate; exact Hfloor)
        ltac:(rewrite PTree.gso by discriminate; exact Hceiling) Htest).
      right. split; [congruence|exact Haccept].
  - contradiction.
Qed.

(** All static downward faces whose boxes meet the interior. The filter is
    conservative: it includes faces even if their triangles miss the point. *)
Definition rank10b_ceiling_meets vertices := let '(a,b,c) := vertices in
  (SD.y_of (area1_source_normal_components vertices) <? 0) &&
  rank12b_axis_meets (SD.x_of a) (SD.x_of b) (SD.x_of c) (-459) 460 &&
  rank12b_axis_meets (SD.z_of a) (SD.z_of b) (SD.z_of c) (-203) 716.
Definition rank10b_static_ceilings version := filter (fun face =>
  match snd face with Some vertices => rank10b_ceiling_meets vertices | None => false end)
  (rank12b_faces version).
Definition rank10b_ceiling_ordinals : list nat :=
  [83;84;85;86;87;91;92;93;94;95;96;98;99;100;101;102;1066;1067]%nat.
Definition rank10b_high_flat vertices := let '(a,b,c) := vertices in
  (5222 <=? SD.y_of a) && Z.eqb (SD.y_of a) (SD.y_of b) &&
  Z.eqb (SD.y_of a) (SD.y_of c).
Definition Rank10BStaticCeilingCertificate : Prop := forall version,
  map fst (rank10b_static_ceilings version) = rank10b_ceiling_ordinals /\
  forallb (fun face => match snd face with
    | Some vertices => rank10b_high_flat vertices | None => false end)
    (rank10b_static_ceilings version) = true.
Theorem rank10b_static_ceiling_certificate_checked : Rank10BStaticCeilingCertificate.
Proof. intros []; vm_compute; split; reflexivity. Qed.

Theorem rank10b_every_static_ceiling_is_high : forall version ordinal vertices x y z,
  In (ordinal, Some vertices) (rank12b_faces version) ->
  SD.y_of (area1_source_normal_components vertices) < 0 ->
  rank12b_point_in_vertex_box (x,y,z) vertices ->
  (-459 <= x <= 460)%R -> (-203 <= z <= 716)%R -> (5222 <= y)%R.
Proof.
  intros version ordinal vertices x y z Hin Hdown Hbox Hx Hz.
  assert (Hcandidate : In (ordinal, Some vertices) (rank10b_static_ceilings version)).
  { apply filter_In. split; [exact Hin|]. cbn [snd].
    unfold rank10b_ceiling_meets. destruct vertices as [[a b] c].
    unfold rank12b_point_in_vertex_box in Hbox.
    destruct Hbox as [Bx [By Bz]]. repeat rewrite andb_true_iff.
    split; [split; [apply Z.ltb_lt; exact Hdown|]|];
      eapply rank12b_axis_meets_sound; eauto. }
  pose proof (proj2 (rank10b_static_ceiling_certificate_checked version)) as Hhigh.
  rewrite forallb_forall in Hhigh. specialize (Hhigh _ Hcandidate).
  destruct vertices as [[a b] c]. cbn [snd rank10b_high_flat] in Hhigh.
  repeat rewrite andb_true_iff in Hhigh. destruct Hhigh as [[Hlo Hab] Hac].
  apply Z.leb_le in Hlo. apply Z.eqb_eq in Hab, Hac.
  unfold rank12b_point_in_vertex_box in Hbox.
  unfold rank12b_min3, rank12b_max3 in Hbox.
  rewrite <- Hab, <- Hac, !Z.min_id, !Z.max_id in Hbox.
  apply IZR_le in Hlo. lra.
Qed.

Definition rank10b_local_ceiling_meets vertices := let '(a,b,c) := vertices in
  (SD.y_of (area1_source_normal_components vertices) <? 0) &&
  rank12b_axis_meets (SD.x_of a) (SD.x_of b) (SD.x_of c) (-459) 460 &&
  rank12b_axis_meets (SD.z_of a) (SD.z_of b) (SD.z_of c) (-459) 460.
Definition Rank10BElevatorCeilingCertificate : Prop := forall version,
  filter (fun face => match face with
    | Some vertices => rank10b_local_ceiling_meets vertices | None => false end)
    (rank10s_elevator_faces version) =
    [Some ((-511,-50,-511),(512,-50,-511),(512,-50,512));
     Some ((-511,-50,-511),(512,-50,512),(-511,-50,512))].
Theorem rank10b_elevator_ceiling_certificate_checked : Rank10BElevatorCeilingCertificate.
Proof. intros []; vm_compute; reflexivity. Qed.

(** Generous finite bounds, not an assumed fixed height. With this margin the
    low-gap ceiling return is false for ANY returned finite ceiling >= 5222,
    independently of list order or which of the high static faces wins. *)
Lemma rank10b_floor_ceiling_clear : forall floor ceiling,
  rank9cf_finite floor -> rank9cf_finite ceiling ->
  (0 <= rank9cf_real floor <= 5000)%R -> (5222 <= rank9cf_real ceiling)%R ->
  Float32.cmp Cge (Float32.add floor ifh_160) ceiling = false.
Proof.
  intros floor ceiling Ff Fc Hf Hc.
  assert (H160 : ifh_160 = rank9cf_integer 160)
    by (apply rank9cf_bits_injective; vm_compute; reflexivity).
  rewrite H160.
  destruct (rank9cf_integer_exact 160 ltac:(lia)) as [R160 F160].
  destruct (rank9cf_add_range floor (rank9cf_integer 160) 160 5160
    Ff F160 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R160; lra)) as [Fs Hs].
  assert (Hlt : (rank9cf_real (Float32.add floor (rank9cf_integer 160)) <
    rank9cf_real ceiling)%R) by lra.
  unfold Float32.cmp, Float32.compare.
  rewrite Bcompare_correct by assumption. rewrite Rcompare_Lt by exact Hlt. reflexivity.
Qed.

Definition Rank10BNoEarlyCeilingStop : Prop :=
  forall version e le m nb no y floor ceiling t le' m' out,
  le ! IFH._nextPos = Some (Vptr nb no) ->
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  le ! IFH._ceilHeight = Some (Vsingle ceiling) ->
  Mem.load Mfloat32 m nb (Ptrofs.unsigned (Ptrofs.add no (Ptrofs.repr 4))) = Some (Vsingle y) ->
  Float32.cmp Cgt y (Float32.add floor ifh_100) = false ->
  rank9cf_finite floor -> rank9cf_finite ceiling ->
  (0 <= rank9cf_real floor <= 5000)%R -> (5222 <= rank9cf_real ceiling)%R ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_post_water version) t le' m' out ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e
    (PTree.set IFH._t'16 (Vsingle y) le) m (ifh_accept version) t le' m' out.
Theorem rank10b_clear_ceiling_reaches_alignment : Rank10BNoEarlyCeilingStop.
Proof.
  unfold Rank10BNoEarlyCeilingStop. intros.
  pose proof (rank10b_floor_ceiling_clear floor ceiling H4 H5 H6 H7) as Hclear.
  destruct (rank10b_low_gap_stops_for_ceiling_or_reaches_alignment
    version e le m nb no y floor ceiling t le' m' out H H0 H1 H2 H3 H8)
    as [(Hbad & _)|[_ Haccept]]; [congruence|exact Haccept].
Qed.

(** A blanket 100-unit invariant is false for the ALREADY CHECKED vertical
    episode. This is a certificate counterexample, not a clean controller run. *)
Theorem rank10b_blanket_100_bound_is_false :
  ~ (forall s, In s sk_normal_samples -> sk_gap8 s <= 800).
Proof.
  intro H. specialize (H (nth 11 sk_normal_samples sk_normal_start)).
  assert (In (nth 11 sk_normal_samples sk_normal_start) sk_normal_samples) as Hin
    by (apply nth_In; vm_compute; lia).
  specialize (H Hin). change (1136 <= 800) in H. lia.
Qed.

Definition Rank10ABlockedStepBoundary : Prop :=
  InkGroundQuarterCallHistoryCut /\ InkQuarterMissingFloorCut /\
  InkHighFloorGapQuarterCut /\ Rank10BLowGapQuarterCut /\
  Rank10BStaticCeilingCertificate /\ Rank10BElevatorCeilingCertificate /\
  (forall version ordinal vertices x y z,
    In (ordinal, Some vertices) (rank12b_faces version) ->
    SD.y_of (area1_source_normal_components vertices) < 0 ->
    rank12b_point_in_vertex_box (x,y,z) vertices ->
    (-459 <= x <= 460)%R -> (-203 <= z <= 716)%R -> (5222 <= y)%R) /\
  Rank10BNoEarlyCeilingStop /\
  ~ (forall s, In s sk_normal_samples -> sk_gap8 s <= 800).
Theorem rank10b_blocked_step_boundary_checked : Rank10ABlockedStepBoundary.
Proof.
  split; [exact ifh_completed_quarter_call_reaches_queried_floor_cut|].
  split; [exact ifh_missing_floor_returns_or_reaches_actual_water_tail|].
  split; [exact ifh_high_gap_requires_ceiling_block_or_leaves_ground|].
  split; [exact rank10b_low_gap_stops_for_ceiling_or_reaches_alignment|].
  split; [exact rank10b_static_ceiling_certificate_checked|].
  split; [exact rank10b_elevator_ceiling_certificate_checked|].
  split; [exact rank10b_every_static_ceiling_is_high|].
  split; [exact rank10b_clear_ceiling_reaches_alignment|].
  exact rank10b_blanket_100_bound_is_false.
Qed.
