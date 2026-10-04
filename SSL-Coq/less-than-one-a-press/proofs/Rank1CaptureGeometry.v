(** A binary32 obstruction at the ACTUAL contact and platform checks.
    The floor-height premise is about the real call's result, not a modeled
    replacement floor routine. No agreement of the three positions or frame
    between contact and final query is imposed on all gameplay. *)
From Coq Require Import Reals Lra Lia List ZArith Logic.ProofIrrelevance.
From Flocq Require Import BinarySingleNaN Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes ObjectContactNecessity
  Area2Rank12BContact Rank1PlatformInstallation Rank1FinalPlatformQuery
  InkPlatformSource InkPlatformDistance InkFloorListEffects InkCopyCaller InkCopyCompletion
  InkVerticalRetryGeometry
  UpperElevatorQueryResolution JPBinary32DepthWrites SelectedClightTarget.
Local Open Scope Z_scope.
Import ListNotations.
Local Transparent Float32.cmp Float32.compare Float32.sub Float32.neg.

Local Instance r1cg_prec_positive : Prec_gt_0 24.
Proof. constructor; lia. Defined.
Local Instance r1cg_prec_below_exponent : Prec_lt_emax 24 128.
Proof. constructor; lia. Defined.

Definition r1cg_warp_ceiling := Float32.of_bits (Int.repr 1145864192).
Definition r1cg_negative_margin := Float32.of_int (Int.repr (-256)).

Lemma r1cg_near_requires_finite_delta : forall x,
  Float32.cmp Clt (ipdist_abs x) ipdist_four = true ->
  is_finite 24 128 x = true.
Proof.
  intros x H. destruct x as [s|s|s pl Hp|s mant exponent Hb]; try reflexivity.
  - destruct s; vm_compute in H; discriminate.
  - vm_compute in H; discriminate.
Qed.

Lemma r1cg_abs_real : forall x,
  is_finite 24 128 x = true ->
  B2R 24 128 (ipdist_abs x) = Rabs (B2R 24 128 x).
Proof.
  intros x Hfinite.
  assert (B2R 24 128 Float32.zero = 0%R) as Hz by reflexivity.
  unfold ipdist_abs.
  destruct (Float32.cmp Cge x Float32.zero) eqn:Hsign.
  - unfold Float32.cmp, Float32.compare in Hsign.
    rewrite Binary.Bcompare_correct in Hsign by (try exact Hfinite; reflexivity).
    destruct (Rcompare (B2R 24 128 x) (B2R 24 128 Float32.zero)) eqn:Hcmp;
      cbn in Hsign; try discriminate.
    + apply Rcompare_Eq_inv in Hcmp. rewrite Hz in Hcmp. rewrite Rabs_right; lra.
    + apply Rcompare_Gt_inv in Hcmp. rewrite Hz in Hcmp. rewrite Rabs_right; lra.
  - unfold Float32.neg. rewrite Binary.B2R_Bopp.
    unfold Float32.cmp, Float32.compare in Hsign.
    rewrite Binary.Bcompare_correct in Hsign by (try exact Hfinite; reflexivity).
    destruct (Rcompare (B2R 24 128 x) (B2R 24 128 Float32.zero)) eqn:Hcmp;
      cbn in Hsign; try discriminate.
    apply Rcompare_Lt_inv in Hcmp. rewrite Hz in Hcmp. rewrite Rabs_left; lra.
Qed.

Lemma r1cg_near_real_distance : forall x,
  Float32.cmp Clt (ipdist_abs x) ipdist_four = true ->
  (Rabs (B2R 24 128 x) < 4)%R.
Proof.
  intros x Hnear. pose proof (r1cg_near_requires_finite_delta _ Hnear) as Hfinite.
  assert (is_finite 24 128 (ipdist_abs x) = true) as Ha.
  { unfold ipdist_abs. destruct (Float32.cmp Cge x Float32.zero); auto.
    unfold Float32.neg. rewrite Binary.is_finite_Bopp. exact Hfinite. }
  unfold Float32.cmp, Float32.compare in Hnear.
  rewrite Binary.Bcompare_correct in Hnear by (try exact Ha; reflexivity).
  assert (B2R 24 128 ipdist_four = 4%R) as Hfour by (vm_compute; lra).
  destruct (Rcompare (B2R 24 128 (ipdist_abs x)) (B2R 24 128 ipdist_four)) eqn:Hcmp;
    cbn in Hnear; try discriminate.
  apply Rcompare_Lt_inv in Hcmp. rewrite r1cg_abs_real in Hcmp by exact Hfinite.
  rewrite Hfour in Hcmp. exact Hcmp.
Qed.

(** All finite raw heights at or below the warp ceiling are excluded from
    capture of ANY finite returned floor at or above 1281. This includes the
    timer-131 height but is not a finite sampling of raw Y values. *)
Theorem r1cg_low_raw_cannot_capture_high_floor : forall raw height,
  is_finite 24 128 raw = true -> is_finite 24 128 height = true ->
  (B2R 24 128 raw <= 818)%R -> (1281 <= B2R 24 128 height)%R ->
  Float32.cmp Clt (ipdist_abs (Float32.sub raw height)) ipdist_four = false.
Proof.
  intros raw height Fr Fh Hy Hh.
  destruct (Float32.cmp Clt (ipdist_abs (Float32.sub raw height)) ipdist_four)
    eqn:Hnear; [|reflexivity].
  pose proof (r1cg_near_requires_finite_delta _ Hnear) as Fd.
  pose proof (r1cg_near_real_distance _ Hnear) as Hd.
  pose proof (Binary.Bminus_correct 24 128 _ _ Float32.binop_nan mode_NE
    raw height Fr Fh) as Hminus.
  assert (Float32.sub raw height = Binary.Bminus 24 128 r1cg_prec_positive
    r1cg_prec_below_exponent Float32.binop_nan mode_NE raw height) as Hsub.
  { unfold Float32.sub. f_equal; apply proof_irrelevance. }
  rewrite Hsub in Fd, Hd.
  destruct (Rlt_bool (Rabs (round radix2 (SpecFloat.fexp 24 128)
    (round_mode mode_NE) (B2R 24 128 raw - B2R 24 128 height))) (bpow radix2 128)).
  - destruct Hminus as [Hvalue _]. rewrite Hvalue in Hd.
    assert (B2R 24 128 r1cg_negative_margin = (-256)%R) as Hmargin by (vm_compute; lra).
    assert ((round radix2 (SpecFloat.fexp 24 128) (round_mode mode_NE)
      (B2R 24 128 raw - B2R 24 128 height) <= -256)%R) as Hbound.
    { rewrite <- Hmargin.
      rewrite <- (round_generic radix2 (SpecFloat.fexp 24 128)
        (round_mode mode_NE) (B2R 24 128 r1cg_negative_margin)).
      - apply round_le; [typeclasses eauto|typeclasses eauto|lra].
      - apply Binary.generic_format_B2R. }
    rewrite Rabs_left in Hd by lra. lra.
  - destruct Hminus as [Hoverflow _].
    destruct (Binary.Bminus 24 128 r1cg_prec_positive r1cg_prec_below_exponent
      Float32.binop_nan mode_NE raw height); cbn in Fd; try discriminate;
      cbn [B2FF binary_overflow] in Hoverflow; discriminate.
Qed.

(** This is the height of the checked timer-131 triangle at the candidate
    X/Z. Returning that triangle in a live call remains a separate claim. *)
Lemma r1cg_timer131_contact_height_bound :
  is_finite 24 128 ivr_contact_height = true /\
  (1281 <= B2R 24 128 ivr_contact_height)%R.
Proof. split; [reflexivity|vm_compute; lra]. Qed.

Theorem r1cg_low_raw_cannot_capture_timer131 : forall raw,
  is_finite 24 128 raw = true -> (B2R 24 128 raw <= 818)%R ->
  Float32.cmp Clt (ipdist_abs (Float32.sub raw ivr_contact_height)) ipdist_four = false.
Proof.
  intros raw Fr Hr. destruct r1cg_timer131_contact_height_bound as [Fh Hh].
  exact (r1cg_low_raw_cannot_capture_high_floor raw ivr_contact_height Fr Fh Hr Hh).
Qed.

Definition Rank1SuccessfulContactHeightCut : Prop :=
  forall version e le m t final final_m,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (rank12b_body version)) t final final_m
    (Out_return (Some (Vint Int.one, tint))) ->
  exists rl rm vl vm it ht rt,
    ocn_ordered_contact_checkpoints version e le m t final final_m rl rm vl vm it ht rt /\
    (forall y,
      vl ! RC._sp3C = Some (Vsingle y) ->
      vl ! RC._sp1C = Some (Vsingle r1cg_warp_ceiling) ->
      is_finite 24 128 y = true -> (B2R 24 128 y <= 818)%R).

Theorem r1cg_successful_contact_exposes_low_height : Rank1SuccessfulContactHeightCut.
Proof.
  intros version e le m t final final_m Hrun.
  destruct (ocn_success_requires_ordered_contact_tests _ _ _ _ _ _ _ Hrun)
    as (rl & rm & vl & vm & it & ht & rt & Hcuts).
  exists rl, rm, vl, vm, it, ht, rt. split; [exact Hcuts|].
  intros y Hy Hceiling Fy.
  destruct Hcuts as (_ & _ & _ & _ & Habove & _).
  pose proof (ocn_float_test_is_the_actual_comparison _ _ _ _ _ _ true _ _ _
    Hy Hceiling Habove) as Hcmp.
  cbn beta iota in Hcmp. change Cgt with (swap_comparison Clt) in Hcmp.
  rewrite Float32.cmp_swap in Hcmp.
  pose proof (jp_binary32_finite_not_lt_preserves_lower_bound r1cg_warp_ceiling y
    eq_refl Fy Hcmp) as Hbound.
  assert (B2R 24 128 r1cg_warp_ceiling = 818%R) as Hvalue by (vm_compute; lra).
  rewrite Hvalue in Hbound. exact Hbound.
Qed.

Definition Rank1LowFinalQueryClearing : Prop :=
  forall version e le m fb gb ob oo values t le' m' out,
  e ! IPD._gMarioObject = None -> e ! IPD._find_floor = None -> e ! ipdist_abs_id = None ->
  e ! IPD._gMarioPlatform = None -> e ! IPD._floor = Some (fb, ipd_surface) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  (forall axis, Mem.load Mfloat32 m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (160 + 4 * icp_number axis)))) = Some (Vsingle (values axis))) ->
  is_finite 24 128 (values ICPY) = true -> (B2R 24 128 (values ICPY) <= 818)%R ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ipd_body version IPDUpdate)) t le' m' out ->
  exists tq ts mq result,
    t = tq ++ ts /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
      (Internal (ueqr_native_body version UEQRFindFloor))
      (Vsingle (values ICPX) :: Vsingle (values ICPY) :: Vsingle (values ICPZ) :: Vptr fb Ptrofs.zero :: nil)
      tq mq result /\
    (forall height sb so owner offset pb currentb currentofs,
      result = Vsingle height -> is_finite 24 128 height = true -> (1281 <= B2R 24 128 height)%R ->
      Mem.load Mptr mq fb 0 = Some (Vptr sb so) ->
      Mem.load Mptr mq sb (Ptrofs.unsigned (Ptrofs.add so (Ptrofs.repr 44))) = Some (Vptr owner offset) ->
      Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
      pb <> fb -> pb <> sb -> pb <> currentb ->
      Mem.load Mptr mq gb 0 = Some (Vptr currentb currentofs) ->
      ts = E0 /\ out = Out_normal /\ Mem.load Mptr m' pb 0 = Some (Vint Int.zero) /\
      Mem.load Mptr m' currentb (Ptrofs.unsigned (Ptrofs.add currentofs (Ptrofs.repr 532))) = Some (Vint Int.zero)).

Theorem r1cg_real_final_query_clears_low_high : Rank1LowFinalQueryClearing.
Proof.
  intros version e le m fb gb ob oo values t le' m' out
    Hml Hfind Habs Hpl Hfloor Hms Hobj Hvalues Fy Hy Hrun.
  destruct (r1o_final_query_connects_raw_position_to_owner _ _ _ _ _ _ _ _ _ _ _ _ _
    Hml Hfind Habs Hpl Hfloor Hms Hobj Hvalues Hrun)
    as (tq & ts & mq & result & Htrace & Hcall & Howner).
  exists tq, ts, mq, result. split; [exact Htrace|]. split; [exact Hcall|].
  intros height sb so owner offset pb currentb currentofs Hr Fh Hh
    Hselected Hreturned Hps Hpf Hpsurface Hpo Hcurrent.
  specialize (Howner height sb so owner offset pb currentb currentofs
    Hr Hselected Hreturned Hps Hpf Hpsurface Hpo Hcurrent).
  rewrite (r1cg_low_raw_cannot_capture_high_floor _ _ Fy Fh Hy Hh) in Howner.
  cbn beta iota zeta in Howner.
  tauto.
Qed.

Definition Rank1CaptureGeometryBoundary : Prop :=
  Rank1SuccessfulContactHeightCut /\ Rank1LowFinalQueryClearing /\
  (is_finite 24 128 ivr_contact_height = true /\
    (1281 <= B2R 24 128 ivr_contact_height)%R).
Theorem r1cg_capture_geometry_checked : Rank1CaptureGeometryBoundary.
Proof.
  split; [exact r1cg_successful_contact_exposes_low_height|].
  split; [exact r1cg_real_final_query_clears_low_high|].
  exact r1cg_timer131_contact_height_bound.
Qed.
