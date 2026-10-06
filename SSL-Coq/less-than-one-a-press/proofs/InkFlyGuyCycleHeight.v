(** Source-linked normalization and signed growth after the positive prefix.

    These results do not classify every actor update. They establish what the
    actual completed normalization helper guarantees, and what a reached grow
    store can do once its live velocity is nonpositive. Action/receiver history
    and delayed X-to-Y reads remain separate execution obligations. *)
From Coq Require Import Bool List Reals Lia Lra ZArith Logic.ProofIrrelevance.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From Flocq Require Import BinarySingleNaN Binary Core.
From LessThanOneAPress.Generated Require Import us_obj_behaviors_2 jp_obj_behaviors_2.
From LessThanOneAPress.Proofs Require Import GameTypes InkFlyGuyGrowthPrefix
  InkFlyGuySizeBoundary InkFloorResetExecution InkBackwardExecution
  ObjectContactNecessity ContactConsumerExecution InkQuicksandArithmetic
  InkRawCopyExpressions ObjectContactReadback EyerokRank15LiveMovement
  Area2Rank9ACoinFlight Area2Rank12BContact SelectedClightTarget InkBounceApproachGap.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ifch_approach_body version := match version with
| VersionUS => us_obj_behaviors_2.f_approach_f32_ptr
| VersionJP => jp_obj_behaviors_2.f_approach_f32_ptr end.
Definition ifch_pointer := Ederef (Etempvar FGP._px (tptr tfloat)) tfloat.
Definition ifch_clamp_store := Sassign ifch_pointer (Etempvar FGP._target tfloat).
Definition ifch_return n := Sreturn (Some (Econst_int (Int.repr n) tint)).
Definition ifch_returned n := Out_return (Some (Vint (Int.repr n), tint)).
Definition ifch_clamp := Ssequence ifch_clamp_store (ifch_return 1).
Definition ifch_prefix version := ocn_prefix_items 2
  (fn_body (ifch_approach_body version)).
Definition ifch_prefix_stmt version := ocn_prepend (ifch_prefix version) Sskip.
Definition ifch_test version := match fn_body (ifch_approach_body version) with
| Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse test _ _)) _)) => test
| _ => Econst_int Int.zero tint end.
Definition ifch_read := Sset FGP._t'1 ifch_pointer.
Definition ifch_choice version := Ssequence ifch_read
  (Sifthenelse (ifch_test version) ifch_clamp Sskip).

Lemma ifch_actual_approach_shape : forall version,
  fn_vars (ifch_approach_body version) = [] /\
  fn_params (ifch_approach_body version) =
    [(FGP._px,tptr tfloat);(FGP._target,tfloat);(FGP._delta,tfloat)] /\
  fn_return (ifch_approach_body version) = tint /\
  fn_body (ifch_approach_body version) =
    ocn_prepend (ifch_prefix version)
      (Ssequence (ifch_choice version) (ifch_return 0)) /\
  forallb ibk_normal (ifch_prefix version) = true /\
  ifr_keeps_temp FGP._px (ifch_prefix_stmt version) = true /\
  ifr_keeps_temp FGP._target (ifch_prefix_stmt version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ifch_constant_return : forall ge e le m n t le' m' out,
  ocn_exec ge e le m (ifch_return n) t le' m' out ->
  le' = le /\ m' = m /\ out = ifch_returned n.
Proof.
  intros ge e le m n t le' m' out Hrun.
  unfold ifch_return in Hrun. inversion Hrun; subst.
  match goal with Hread : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hread; subst end.
  repeat split; reflexivity.
Qed.

Lemma ifch_actual_clamp_store : forall ge e le m b ofs target t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  ocn_exec ge e le m ifch_clamp_store t le' m' out ->
  Mem.store Mfloat32 m b (Ptrofs.unsigned ofs) (Vsingle target) = Some m' /\
  le' = le /\ out = Out_normal.
Proof.
  intros ge e le m b ofs target t le' m' out Hp Htarget Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt, ifch_clamp_store in Hrun.
  inversion Hrun; subst; clear Hrun.
  match goal with H : eval_lvalue _ _ _ _ ifch_pointer _ _ _ |- _ =>
    unfold ifch_pointer in H; inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ (Etempvar FGP._px _) ?v |- _ =>
    assert (v = Vptr b ofs) as Hpointer by (eapply ocn_temp_value; eauto);
    inversion Hpointer; subst; clear Hpointer end.
  match goal with H : eval_expr _ _ _ _ (Etempvar FGP._target _) ?v |- _ =>
    assert (v = Vsingle target) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ =>
    cbn in H; inversion H; subst end.
  repeat split; try reflexivity; assumption.
Qed.

Lemma ifch_actual_clamp_returns_target : forall ge e le m b ofs target
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  ocn_exec ge e le m ifch_clamp t le' m' out ->
  out = ifch_returned 1 /\
  Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) = Some (Vsingle target).
Proof.
  intros ge e le m b ofs target t le' m' out Hp Htarget Hrun.
  unfold ifch_clamp in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ifch_clamp_store _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hstore & Hreturn).
  destruct (ifch_actual_clamp_store _ _ _ _ _ _ _ _ _ _ _ Hp Htarget Hstore)
    as (Hwritten & -> & _).
  destruct (ifch_constant_return _ _ _ _ _ _ _ _ _ Hreturn) as (_ & -> & ->).
  split; [reflexivity|exact (Mem.load_store_same _ _ _ _ _ _ Hwritten)].
Qed.

Lemma ifch_actual_choice_outcome : forall version ge e le m b ofs target
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  ocn_exec ge e le m (ifch_choice version) t le' m' out ->
  out = Out_normal \/
  (out = ifch_returned 1 /\
   Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) = Some (Vsingle target)).
Proof.
  intros version ge e le m b ofs target t le' m' out Hp Htarget Hrun.
  unfold ifch_choice in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ifch_read _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hchoice).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ FGP._px Hread
    eq_refl) as Hpx.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ FGP._target Hread
    eq_refl) as Ht.
  assert (Hp' : middle ! FGP._px = Some (Vptr b ofs)) by (rewrite Hpx; exact Hp).
  assert (Ht' : middle ! FGP._target = Some (Vsingle target)) by (rewrite Ht; exact Htarget).
  inversion Hchoice; subst.
  match goal with Hbool : bool_val _ _ _ = Some ?choice |- _ =>
    destruct choice; cbn in * end.
  - right. eapply ifch_actual_clamp_returns_target with
      (b := b) (ofs := ofs) (target := target); eauto.
  - match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hskip; subst end. now left.
Qed.

Theorem ifch_actual_approach_body_normalizes_on_success : forall version e le m
    b ofs target t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ifch_approach_body version)) t le' m' out ->
  out = ifch_returned 0 \/
  (out = ifch_returned 1 /\
   Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) = Some (Vsingle target)).
Proof.
  intros version e le m b ofs target t le' m' out Hp Htarget Hrun.
  destruct (ifch_actual_approach_shape version)
    as (_ & _ & _ & Hbody & Hnormal & HkeepP & HkeepT).
  rewrite Hbody in Hrun.
  destruct (ibk_split_prefix _ _ (ifch_prefix version)
    (Ssequence (ifch_choice version) (ifch_return 0)) le m _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suf & Htrace & Hprefix & Hrest).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepP) as Hpx.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepT) as Ht.
  assert (Hp' : middle ! FGP._px = Some (Vptr b ofs)) by congruence.
  assert (Ht' : middle ! FGP._target = Some (Vsingle target)) by congruence.
  inversion Hrest; subst.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (ifch_return 0) _ _ _ _ |- _ =>
      destruct (ifch_constant_return _ _ _ _ _ _ _ _ _ Hr) as (_ & _ & ->) end.
    now left.
  - match goal with Hc : ClightBigstep.exec_stmt _ _ _ _ _ (ifch_choice version) _ _ _ _ |- _ =>
      destruct (ifch_actual_choice_outcome _ _ _ _ _ _ _ _ _ _ _ _ Hp' Ht' Hc)
        as [HnormalOut | Hclamped]; [contradiction|now right] end.
Qed.

Theorem ifch_completed_approach_normalizes : forall version m b ofs target delta
    t m',
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifch_approach_body version))
    [Vptr b ofs;Vsingle target;Vsingle delta] t m' (Vint Int.one) ->
  Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) = Some (Vsingle target).
Proof.
  intros version m b ofs target delta t m' Hcall.
  destruct (ifch_actual_approach_shape version)
    as (Hvars & Hparams & Hreturn & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! FGP._px = Some (Vptr b ofs)) as Hp by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (temps ! FGP._target = Some (Vsingle target)) as Htarget by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss) end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (ifch_actual_approach_body_normalizes_on_success
      _ _ _ _ _ _ _ _ _ _ _ Hp Htarget Hbody) as [Hzero | [Hone Hload]] end.
  - match goal with Hresult : outcome_result_value _ _ _ _ |- _ =>
      rewrite Hzero, Hreturn in Hresult; cbn in Hresult;
      destruct Hresult as [_ Hcast]; cbn in Hcast; discriminate end.
  - exact Hload.
Qed.

(** No finite amount of additional nonpositive-velocity growth can increase
    scale. This covers arbitrary signed negative size values, not just the
    seven certified positive steps. The finite-result premise is the selected
    physical-model boundary and is not an actor-history coverage claim. *)
Local Instance ifch_precision_positive : Prec_gt_0 24.
Proof. constructor; lia. Defined.
Local Instance ifch_precision_below_exponent : Prec_lt_emax 24 128.
Proof. constructor; lia. Defined.
Local Transparent Float32.add Float32.cmp Float32.compare Float32.neg.

Theorem ifch_nonpositive_addition_cannot_raise : forall scale velocity,
  is_finite 24 128 scale = true ->
  is_finite 24 128 velocity = true ->
  is_finite 24 128 (Float32.add scale velocity) = true ->
  (B2R 24 128 velocity <= 0)%R ->
  (B2R 24 128 (Float32.add scale velocity) <= B2R 24 128 scale)%R.
Proof.
  intros scale velocity Hscale Hvelocity Hresult Hsign.
  pose proof (Binary.Bplus_correct 24 128 _ _ Float32.binop_nan mode_NE
    scale velocity Hscale Hvelocity) as Hplus.
  assert (Hadd : Float32.add scale velocity =
    Binary.Bplus 24 128 ifch_precision_positive ifch_precision_below_exponent
      Float32.binop_nan mode_NE scale velocity).
  { unfold Float32.add. f_equal; apply proof_irrelevance. }
  rewrite Hadd in Hresult |- *.
  destruct (Rlt_bool (Rabs (round radix2 (SpecFloat.fexp 24 128)
    (round_mode mode_NE) (B2R 24 128 scale + B2R 24 128 velocity)))
    (bpow radix2 128)).
  - destruct Hplus as [Hvalue _]. rewrite Hvalue.
    rewrite <- (round_generic radix2 (SpecFloat.fexp 24 128)
      (round_mode mode_NE) (B2R 24 128 scale)) at 2.
    + apply round_le; [typeclasses eauto|typeclasses eauto|lra].
    + apply Binary.generic_format_B2R.
  - destruct Hplus as [Hoverflow _].
    destruct (Binary.Bplus 24 128 ifch_precision_positive ifch_precision_below_exponent
      Float32.binop_nan mode_NE scale velocity); cbn in Hresult; try discriminate;
      cbn [B2FF binary_overflow] in Hoverflow; discriminate.
Qed.

Theorem ifch_reached_nonpositive_growth_store_cannot_raise : forall version e le m
    ob oo scale velocity t le' m' out,
  le ! FGP._t'14 = Some (Vptr ob oo) ->
  le ! FGP._t'16 = Some (Vsingle scale) ->
  le ! FGP._t'17 = Some (Vsingle velocity) ->
  is_finite 24 128 scale = true ->
  is_finite 24 128 velocity = true ->
  is_finite 24 128 (Float32.add scale velocity) = true ->
  (B2R 24 128 velocity <= 0)%R ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ifgp_scale_store t le' m' out ->
  Mem.load Mfloat32 m' ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 44))) =
    Some (Vsingle (Float32.add scale velocity)) /\
  (B2R 24 128 (Float32.add scale velocity) <= B2R 24 128 scale)%R.
Proof.
  intros version e le m ob oo scale velocity t le' m' out Ho Hs Hv Fs Fv Fa Hsign Hrun.
  destruct (ifgp_actual_scale_store _ _ _ _ _ _ _ _ _ _ _ _ Ho Hs Hv Hrun)
    as (Hstore & _).
  split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  exact (ifch_nonpositive_addition_cannot_raise _ _ Fs Fv Fa Hsign).
Qed.

Theorem ifch_reached_nonpositive_velocity_store_stays_nonpositive : forall version
    e le m vb vo velocity t le' m' out,
  le ! FGP._scaleVel = Some (Vptr vb vo) ->
  le ! FGP._t'1 = Some (Vsingle (Float32.sub velocity ifgp_delta)) ->
  is_finite 24 128 velocity = true ->
  is_finite 24 128 (Float32.sub velocity ifgp_delta) = true ->
  (B2R 24 128 velocity <= 0)%R ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ifgp_velocity_store t le' m' out ->
  Mem.load Mfloat32 m' vb (Ptrofs.unsigned vo) =
    Some (Vsingle (Float32.sub velocity ifgp_delta)) /\
  (B2R 24 128 (Float32.sub velocity ifgp_delta) <= 0)%R.
Proof.
  intros version e le m vb vo velocity t le' m' out Hp Hv Fv Fa Hsign Hrun.
  destruct (ifgp_actual_velocity_store _ _ _ _ _ _ _ _ _ _ _ Hp Hv Hrun)
    as (Hstore & _).
  split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  assert (Fd : is_finite 24 128 ifgp_delta = true) by (vm_compute; reflexivity).
  assert (Hd : (0 <= B2R 24 128 ifgp_delta)%R) by (vm_compute; nra).
  pose proof (iq_nonnegative_subtraction_cannot_raise _ _ Fv Fd Fa Hd). lra.
Qed.

(** The scan only locates a source subtree. Its exact US/JP shape is checked
    below; the execution theorem additionally requires the reached subtree. *)
Fixpoint ifch_find_fire_reset (s : statement) : option statement :=
  match s with
  | Ssequence (Sset temporary _) (Sassign _ (Econst_single _ _)) =>
      if Pos.eqb temporary FGP._t'22 then Some s else None
  | Ssequence first rest | Sifthenelse _ first rest =>
      match ifch_find_fire_reset first with
      | Some cut => Some cut | None => ifch_find_fire_reset rest end
  | _ => None end.
Definition ifch_approach_actor version := match version with
| VersionUS => us_obj_behaviors_2.f_fly_guy_act_approach_mario
| VersionJP => jp_obj_behaviors_2.f_fly_guy_act_approach_mario end.
Definition ifch_fire_reset_store version := Sassign
  (rank15_raw_float_expression version FGP._t'22 (Econst_int (Int.repr 33) tint))
  (Econst_single (ifgp_f32 1031127695) tfloat).
Definition ifch_fire_reset version := Ssequence
  (Sset FGP._t'22 rank15_current_object_expression) (ifch_fire_reset_store version).

Theorem ifch_fire_reset_cut_is_generated : forall version,
  ifch_find_fire_reset (fn_body (ifch_approach_actor version)) =
    Some (ifch_fire_reset version).
Proof. intros []; reflexivity. Qed.

Lemma ifch_reset_location : forall version e le m ob oo b ofs bf,
  le ! FGP._t'22 = Some (Vptr ob oo) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (rank15_raw_float_expression version FGP._t'22 (Econst_int (Int.repr 33) tint))
    b ofs bf ->
  b = ob /\ ofs = rank15_raw_address oo (Int.repr 33) /\ bf = Full.
Proof.
  intros version e le m ob oo b ofs bf Htemp Hread.
  pose proof (rank15_raw_float_lvalue version e le m FGP._t'22
    (Econst_int (Int.repr 33) tint) (Int.repr 33) ob oo Htemp
    (eval_Econst_int _ _ _ _ _ _) eq_refl) as Hknown.
  destruct (proj2 (ocr_expression_lvalue_unique
    (Clight.globalenv (selected_clight_target version)) e le m)
    _ _ _ _ Hread _ _ _ Hknown) as (-> & -> & ->).
  repeat split; reflexivity.
Qed.

Theorem ifch_reached_fire_reset_writes_stock_velocity : forall version e le m
    ob oo t le' m' out,
  le ! FGP._t'22 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifch_fire_reset_store version) t le' m' out ->
  Mem.store Mfloat32 m ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 33)))
    (Vsingle (ifgp_f32 1031127695)) = Some m' /\
  Mem.load Mfloat32 m' ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 33))) =
    Some (Vsingle (ifgp_f32 1031127695)).
Proof.
  intros version e le m ob oo t le' m' out Htemp Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt, ifch_fire_reset_store in Hrun.
  inversion Hrun; subst; clear Hrun.
  match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ifch_reset_location _ _ _ _ _ _ _ _ _ Htemp H) as (-> & -> & ->) end.
  match goal with H : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ =>
    inversion H; subst; clear H;
    try match goal with Hl : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ =>
      inversion Hl end end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ =>
    cbn in H; inversion H; subst end.
  match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ =>
    change (Mem.store Mfloat32 m ob
      (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 33)))
      (Vsingle (ifgp_f32 1031127695)) = Some m') in Hstore;
    split; [exact Hstore|exact (Mem.load_store_same _ _ _ _ _ _ Hstore)] end.
Qed.

(** The actual source cut reloads its receiver itself. There is no intervening
    call between this global read and the velocity store. *)
Theorem ifch_actual_fire_reset_reload_and_store : forall version e le m
    current_block ob oo t le' m' out,
  e ! FGP._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    FGP._gCurrentObject = Some current_block ->
  Mem.load Mint32 m current_block 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifch_fire_reset version) t le' m' out ->
  Mem.store Mfloat32 m ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 33)))
    (Vsingle (ifgp_f32 1031127695)) = Some m' /\
  Mem.load Mfloat32 m' ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 33))) =
    Some (Vsingle (ifgp_f32 1031127695)).
Proof.
  intros version e le m current_block ob oo t le' m' out Hlocal Hsymbol Hload Hrun.
  unfold ifch_fire_reset in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sset FGP._t'22 rank15_current_object_expression) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hstore).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ rank15_current_object_expression ?answer |- _ =>
    assert (answer = Vptr ob oo) by
      (eapply irc_global_pointer_read; eauto); subst answer end.
  eapply ifch_reached_fire_reset_writes_stock_velocity; eauto.
  apply PTree.gss.
Qed.

(** The actual height multiplication is monotone in signed scale; it does
    not take an absolute value when scale becomes negative. *)
Local Transparent Float32.mul.
Lemma ifch_finite_product_real : forall x y,
  is_finite 24 128 x = true -> is_finite 24 128 y = true ->
  is_finite 24 128 (Float32.mul x y) = true ->
  B2R 24 128 (Float32.mul x y) =
    round radix2 (SpecFloat.fexp 24 128) (round_mode mode_NE)
      (B2R 24 128 x * B2R 24 128 y).
Proof.
  intros x y Fx Fy Fproduct.
  pose proof (Binary.Bmult_correct 24 128 _ _ Float32.binop_nan mode_NE x y) as Hmul.
  assert (Hmuldef : Float32.mul x y =
    Binary.Bmult 24 128 ifch_precision_positive ifch_precision_below_exponent
      Float32.binop_nan mode_NE x y).
  { unfold Float32.mul. f_equal; apply proof_irrelevance. }
  rewrite Hmuldef in Fproduct |- *.
  destruct (Rlt_bool (Rabs (round radix2 (SpecFloat.fexp 24 128)
    (round_mode mode_NE) (B2R 24 128 x * B2R 24 128 y))) (bpow radix2 128)).
  - exact (proj1 Hmul).
  - rename Hmul into Hoverflow.
    destruct (Binary.Bmult 24 128 ifch_precision_positive ifch_precision_below_exponent
      Float32.binop_nan mode_NE x y); cbn in Fproduct; try discriminate;
      cbn [B2FF binary_overflow] in Hoverflow; discriminate.
Qed.

Theorem ifch_signed_scale_height_is_bounded : forall scale_y,
  is_finite 24 128 scale_y = true ->
  is_finite 24 128 (Float32.mul scale_y (Float32.of_int (Int.repr 60))) = true ->
  (B2R 24 128 scale_y <= B2R 24 128 (ifgp_f32 1071309126))%R ->
  (B2R 24 128 (Float32.mul scale_y (Float32.of_int (Int.repr 60))) <=
    B2R 24 128 (ifgp_f32 1120744242))%R.
Proof.
  intros scale_y Fs Fproduct Hbound.
  assert (F60 : is_finite 24 128 (Float32.of_int (Int.repr 60)) = true)
    by (vm_compute; reflexivity).
  assert (Fpeak : is_finite 24 128 (ifgp_f32 1071309126) = true)
    by (vm_compute; reflexivity).
  assert (Hpeak : Float32.mul (ifgp_f32 1071309126)
    (Float32.of_int (Int.repr 60)) = ifgp_f32 1120744242).
  { rewrite <- (Float32.of_to_bits
      (Float32.mul (ifgp_f32 1071309126) (Float32.of_int (Int.repr 60)))).
    unfold ifgp_f32. f_equal; vm_compute; reflexivity. }
  assert (Fpeakproduct : is_finite 24 128
    (Float32.mul (ifgp_f32 1071309126) (Float32.of_int (Int.repr 60))) = true)
    by (rewrite Hpeak; vm_compute; reflexivity).
  rewrite (ifch_finite_product_real _ _ Fs F60 Fproduct).
  rewrite <- Hpeak.
  rewrite (ifch_finite_product_real _ _ Fpeak F60 Fpeakproduct).
  apply round_le; [typeclasses eauto|typeclasses eauto|].
  assert (H60 : (0 <= B2R 24 128 (Float32.of_int (Int.repr 60)))%R)
    by (vm_compute; nra).
  nra.
Qed.

Theorem ifch_actual_signed_height_store_is_bounded : forall version e le m ob oo
    scale_y t le' m' out,
  le ! FGH._obj = Some (Vptr ob oo) ->
  le ! FGH._t'7 = Some (Vsingle scale_y) ->
  le ! FGH._t'8 = Some (Vint (Int.repr 60)) ->
  is_finite 24 128 scale_y = true ->
  is_finite 24 128 (Float32.mul scale_y (Float32.of_int (Int.repr 60))) = true ->
  (B2R 24 128 scale_y <= B2R 24 128 (ifgp_f32 1071309126))%R ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ifgp_height_store t le' m' out ->
  exists written,
    Mem.load Mfloat32 m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
      Some (Vsingle written) /\
    (B2R 24 128 written <= B2R 24 128 (ifgp_f32 1120744242))%R.
Proof.
  intros version e le m ob oo scale_y t le' m' out Ho Hs Hh Fs Fp Hbound Hrun.
  destruct (ifgp_actual_hitbox_height_store _ _ _ _ _ _ _ _ _ _ _ Ho Hs Hh Hrun)
    as (Hstore & _).
  exists (Float32.mul scale_y (Float32.of_int (Int.repr 60))).
  split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  exact (ifch_signed_scale_height_is_bounded _ Fs Fp Hbound).
Qed.

Definition ifch_stock_approach_pairs : list (float32 * float32) :=
  [(ifgp_f32 1069547520,ifgp_f32 1017370378);
   (ifgp_f32 1066192077,ifgp_f32 1028443341)].
Definition ifch_ceiling := ifgp_f32 1071309126.
Definition ifch_effective_delta old target delta :=
  if Float32.cmp Cgt old target then Float32.neg delta else delta.
Definition ifch_candidate old target delta :=
  Float32.add old (ifch_effective_delta old target delta).
Definition ifch_should_clamp candidate target delta :=
  Float32.cmp Cge (Float32.mul (Float32.sub candidate target) delta)
    (Float32.of_int Int.zero).
Definition ifch_approach_result old target delta :=
  if ifch_should_clamp (ifch_candidate old target delta) target
      (ifch_effective_delta old target delta)
  then target else ifch_candidate old target delta.

Lemma ifch_stock_approach_numbers : forall target delta,
  In (target,delta) ifch_stock_approach_pairs ->
  rank9cf_finite target /\ rank9cf_finite delta /\
  (1 <= rank9cf_real target <= 3/2)%R /\
  (0 < rank9cf_real delta <= 1/4)%R /\
  (rank9cf_real target <= rank9cf_real ifch_ceiling)%R /\
  (3/2 <= rank9cf_real ifch_ceiling <= 7/4)%R.
Proof.
  intros target delta [Hpair | [Hpair | Hnone]]; try contradiction;
    inversion Hpair; subst; unfold rank9cf_finite, rank9cf_real, ifch_ceiling,
      ifgp_f32; vm_compute; repeat split; nra.
Qed.

(** Incrementing by a stock positive delta stays finite even when the old
    signed scale is very negative. Its rounded lower bound is the old finite
    float itself, so no artificial lower-scale bound is needed. *)
Lemma ifch_positive_increment_under_two : forall old delta,
  rank9cf_finite old -> rank9cf_finite delta ->
  (rank9cf_real old <= rank9cf_real ifch_ceiling)%R ->
  (0 <= rank9cf_real delta <= 1/4)%R ->
  rank9cf_finite (Float32.add old delta) /\
  (rank9cf_real (Float32.add old delta) <= 2)%R.
Proof.
  intros old delta Fo Fd Hold Hd.
  assert (Hpeak : (rank9cf_real ifch_ceiling <= 7/4)%R)
    by (unfold rank9cf_real, ifch_ceiling, ifgp_f32; vm_compute; nra).
  assert (Hlower : (rank9cf_real old <=
    rank9cf_round (rank9cf_real old + rank9cf_real delta))%R).
  { rewrite <- (round_generic radix2 (SpecFloat.fexp 24 128)
      (round_mode mode_NE) (rank9cf_real old)) at 1.
    - unfold rank9cf_round. apply round_le; [typeclasses eauto|typeclasses eauto|lra].
    - apply Binary.generic_format_B2R. }
  assert (Hupper : (rank9cf_round (rank9cf_real old + rank9cf_real delta) <= 2)%R).
  { rewrite <- (rank9cf_round_integer 2) by lia.
    unfold rank9cf_round. apply round_le; [typeclasses eauto|typeclasses eauto|].
    cbn. lra. }
  assert (Hnooverflow : (Rabs
    (rank9cf_round (rank9cf_real old + rank9cf_real delta)) < bpow radix2 128)%R).
  { pose proof (Binary.abs_B2R_lt_emax 24 128 old) as Hfinitebound.
    unfold rank9cf_real in Hlower.
    apply Rabs_lt.
    pose proof (Rle_abs (- B2R 24 128 old)) as Hnegative.
    rewrite Rabs_Ropp in Hnegative.
    replace (bpow radix2 128) with
      (340282366920938463463374607431768211456)%R in * by reflexivity.
    unfold rank9cf_real in Hupper |- *.
    lra. }
  pose proof (Binary.Bplus_correct 24 128 eq_refl eq_refl Float32.binop_nan
    mode_NE old delta Fo Fd) as Hplus.
  fold rank9cf_round in Hplus.
  rewrite Rlt_bool_true in Hplus by exact Hnooverflow.
  destruct Hplus as [Hvalue [Fresult _]].
  split; [exact Fresult|].
  change (rank9cf_real (Float32.add old delta) =
    rank9cf_round (rank9cf_real old + rank9cf_real delta)) in Hvalue.
  now rewrite Hvalue.
Qed.

Lemma ifch_finite_nonnegative_cmp_zero : forall value,
  rank9cf_finite value -> (0 <= rank9cf_real value)%R ->
  Float32.cmp Cge value (Float32.of_int Int.zero) = true.
Proof.
  intros value Fvalue Hsign.
  unfold Float32.cmp, Float32.compare.
  rewrite Bcompare_correct; try exact Fvalue; try (vm_compute; reflexivity).
  change (match Rcompare (rank9cf_real value) 0 with
    | Lt => false | _ => true end = true).
  destruct (Rcompare_spec (rank9cf_real value) 0); cbn; try reflexivity; lra.
Qed.

Theorem ifch_all_stock_approach_results_are_bounded : forall old target delta,
  In (target,delta) ifch_stock_approach_pairs ->
  rank9cf_finite old ->
  (rank9cf_real old <= rank9cf_real ifch_ceiling)%R ->
  rank9cf_finite (ifch_approach_result old target delta) /\
  (rank9cf_real (ifch_approach_result old target delta) <=
    rank9cf_real ifch_ceiling)%R.
Proof.
  intros old target delta Hstock Fo Hold.
  destruct (ifch_stock_approach_numbers _ _ Hstock)
    as (Ft & Fd & Ht & Hd & Htarget & Hpeak).
  unfold ifch_approach_result, ifch_candidate, ifch_effective_delta.
  destruct (Float32.cmp Cgt old target) eqn:Hdescending.
  - assert (Hgreater : (rank9cf_real target < rank9cf_real old)%R).
    { unfold Float32.cmp, Float32.compare in Hdescending.
      rewrite Bcompare_correct in Hdescending by assumption.
      change (match Rcompare (rank9cf_real old) (rank9cf_real target) with
        | Gt => true | _ => false end = true) in Hdescending.
      destruct (Rcompare_spec (rank9cf_real old) (rank9cf_real target));
        cbn in Hdescending; try discriminate; lra. }
    assert (Fn : rank9cf_finite (Float32.neg delta)).
    { unfold rank9cf_finite, Float32.neg. now rewrite is_finite_Bopp. }
    assert (Hneg : rank9cf_real (Float32.neg delta) = (-rank9cf_real delta)%R).
    { unfold rank9cf_real, Float32.neg. apply B2R_Bopp. }
    destruct (rank9cf_add_range old (Float32.neg delta) 0 2 Fo Fn
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hneg; cbn; lra))
      as [Fc Hc].
    pose proof (ifch_nonpositive_addition_cannot_raise old (Float32.neg delta)
      Fo Fn Fc ltac:(change (rank9cf_real (Float32.neg delta) <= 0)%R;
        rewrite Hneg; lra)) as Hnonincrease.
    change (rank9cf_real (Float32.add old (Float32.neg delta)) <=
      rank9cf_real old)%R in Hnonincrease.
    destruct (ifch_should_clamp (Float32.add old (Float32.neg delta))
      target (Float32.neg delta)); split; auto; lra.
  - destruct (ifch_positive_increment_under_two _ _ Fo Fd Hold ltac:(lra))
      as [Fc Hc].
    destruct (ifch_should_clamp (Float32.add old delta) target delta)
      eqn:Hclamp; [split; assumption|].
    split; [exact Fc|].
    destruct (Rle_dec (rank9cf_real (Float32.add old delta))
      (rank9cf_real ifch_ceiling)); [assumption|].
    assert (Hcandidate : (rank9cf_real target <=
      rank9cf_real (Float32.add old delta) <= 2)%R) by lra.
    destruct (rank12b_sub_range (Float32.add old delta) target 0 2 Fc Ft
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lra)) as [Fs Hs].
    destruct (rank9cf_mul_range (Float32.sub (Float32.add old delta) target)
      delta 0 2 Fs Fd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; nra)) as [Fm Hm].
    unfold ifch_should_clamp in Hclamp.
    rewrite (ifch_finite_nonnegative_cmp_zero _ Fm ltac:(cbn in Hm; lra))
      in Hclamp. discriminate.
Qed.

Definition ifch_greater := Ebinop Ogt (Etempvar FGP._t'3 tfloat)
  (Etempvar FGP._target tfloat) tint.
Definition ifch_sign_stage := Ssequence (Sset FGP._t'3 ifch_pointer)
  (Sifthenelse ifch_greater
    (Sset FGP._delta (Eunop Oneg (Etempvar FGP._delta tfloat) tfloat)) Sskip).
Definition ifch_increment_sum := Ebinop Oadd (Etempvar FGP._t'2 tfloat)
  (Etempvar FGP._delta tfloat) tfloat.
Definition ifch_increment_store := Sassign ifch_pointer ifch_increment_sum.
Definition ifch_increment_stage := Ssequence (Sset FGP._t'2 ifch_pointer)
  ifch_increment_store.
Definition ifch_guard := Ebinop Oge
  (Ebinop Omul
    (Ebinop Osub (Etempvar FGP._t'1 tfloat) (Etempvar FGP._target tfloat) tfloat)
    (Etempvar FGP._delta tfloat) tfloat)
  (Econst_int Int.zero tint) tint.

Lemma ifch_actual_three_stages : forall version,
  fn_body (ifch_approach_body version) = Ssequence ifch_sign_stage
    (Ssequence ifch_increment_stage
      (Ssequence (ifch_choice version) (ifch_return 0))) /\
  ifch_test version = ifch_guard.
Proof. intros []; split; reflexivity. Qed.

Lemma ifch_pointer_read_value : forall ge e le m b ofs old answer,
  le ! FGP._px = Some (Vptr b ofs) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle old) ->
  eval_expr ge e le m ifch_pointer answer -> answer = Vsingle old.
Proof.
  intros ge e le m b ofs old answer Hp Hload Hread.
  assert (Hknown : eval_expr ge e le m ifch_pointer (Vsingle old)).
  { unfold ifch_pointer. eapply eval_Elvalue with (loc := b) (ofs := ofs) (bf := Full).
    - apply eval_Ederef. now apply eval_Etempvar.
    - eapply deref_loc_value with (chunk := Mfloat32); [reflexivity|exact Hload]. }
  exact (proj1 (ocr_expression_lvalue_unique ge e le m) _ _ Hread _ Hknown).
Qed.

Lemma ifch_greater_value : forall ge e le m old target answer,
  le ! FGP._t'3 = Some (Vsingle old) ->
  le ! FGP._target = Some (Vsingle target) ->
  eval_expr ge e le m ifch_greater answer ->
  answer = Val.of_bool (Float32.cmp Cgt old target).
Proof.
  intros ge e le m old target answer Ho Ht Hread.
  assert (Hknown : eval_expr ge e le m ifch_greater
    (Val.of_bool (Float32.cmp Cgt old target))).
  { unfold ifch_greater. eapply eval_Ebinop with (v1 := Vsingle old) (v2 := Vsingle target).
    - now apply eval_Etempvar.
    - now apply eval_Etempvar.
    - reflexivity. }
  exact (proj1 (ocr_expression_lvalue_unique ge e le m) _ _ Hread _ Hknown).
Qed.

Lemma ifch_increment_sum_value : forall ge e le m old delta answer,
  le ! FGP._t'2 = Some (Vsingle old) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  eval_expr ge e le m ifch_increment_sum answer ->
  answer = Vsingle (Float32.add old delta).
Proof.
  intros ge e le m old delta answer Ho Hd Hread.
  assert (Hknown : eval_expr ge e le m ifch_increment_sum
    (Vsingle (Float32.add old delta))).
  { unfold ifch_increment_sum. eapply eval_Ebinop with (v1 := Vsingle old) (v2 := Vsingle delta).
    - now apply eval_Etempvar.
    - now apply eval_Etempvar.
    - reflexivity. }
  exact (proj1 (ocr_expression_lvalue_unique ge e le m) _ _ Hread _ Hknown).
Qed.

Lemma ifch_guard_value : forall ge e le m candidate target delta answer,
  le ! FGP._t'1 = Some (Vsingle candidate) ->
  le ! FGP._target = Some (Vsingle target) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  eval_expr ge e le m ifch_guard answer ->
  answer = Val.of_bool (ifch_should_clamp candidate target delta).
Proof.
  intros ge e le m candidate target delta answer Hc Ht Hd Hread.
  assert (Hknown : eval_expr ge e le m ifch_guard
    (Val.of_bool (ifch_should_clamp candidate target delta))).
  { unfold ifch_guard, ifch_should_clamp.
    eapply eval_Ebinop with
      (v1 := Vsingle (Float32.mul (Float32.sub candidate target) delta))
      (v2 := Vint Int.zero).
    - eapply eval_Ebinop with (v1 := Vsingle (Float32.sub candidate target))
        (v2 := Vsingle delta).
      + eapply eval_Ebinop with (v1 := Vsingle candidate) (v2 := Vsingle target);
          [now apply eval_Etempvar|now apply eval_Etempvar|reflexivity].
      + now apply eval_Etempvar.
      + reflexivity.
    - apply eval_Econst_int.
    - reflexivity. }
  exact (proj1 (ocr_expression_lvalue_unique ge e le m) _ _ Hread _ Hknown).
Qed.

Lemma ifch_actual_sign_stage_effect : forall ge e le m b ofs old target delta
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle old) ->
  ocn_exec ge e le m ifch_sign_stage t le' m' out ->
  m' = m /\ le' ! FGP._px = Some (Vptr b ofs) /\
  le' ! FGP._target = Some (Vsingle target) /\
  le' ! FGP._delta = Some (Vsingle (ifch_effective_delta old target delta)).
Proof.
  intros ge e le m b ofs old target delta t le' m' out Hp Ht Hd Hload Hrun.
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ FGP._px Hrun eq_refl)
    as (_ & Hmemory & Hpointer).
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ FGP._target Hrun eq_refl)
    as (_ & _ & Htarget).
  split; [exact Hmemory|]. split; [congruence|]. split; [congruence|].
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt, ifch_sign_stage in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hread : eval_expr _ _ _ _ ifch_pointer ?value |- _ =>
    assert (value = Vsingle old) by (eapply ifch_pointer_read_value; eauto); subst value end.
  all: match goal with Hread : eval_expr _ _ _ _ ifch_greater ?value |- _ =>
    assert (value = Val.of_bool (Float32.cmp Cgt old target)) by
      (eapply ifch_greater_value; [apply PTree.gss|rewrite PTree.gso by discriminate; exact Ht|exact Hread]);
    subst value end.
  all: destruct (Float32.cmp Cgt old target) eqn:Hcmp;
    cbn [bool_val Val.of_bool Int.eq] in *; try discriminate.
  - match goal with Hread : eval_expr _ _ ?temps ?memory
      (Eunop Oneg (Etempvar FGP._delta tfloat) tfloat) ?answer |- _ =>
      assert (answer = Vsingle (Float32.neg delta)) as Hanswer by
        (assert (Hknown : eval_expr ge e temps memory
          (Eunop Oneg (Etempvar FGP._delta tfloat) tfloat)
          (Vsingle (Float32.neg delta))) by
          (eapply eval_Eunop; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact Hd|reflexivity]);
         exact (proj1 (ocr_expression_lvalue_unique ge e temps memory) _ _ Hread _ Hknown));
      subst answer end.
    unfold ifch_effective_delta. rewrite Hcmp. apply PTree.gss.
  - unfold ifch_effective_delta. rewrite Hcmp.
    rewrite PTree.gso by discriminate. exact Hd.
Qed.

Lemma ifch_actual_increment_store : forall ge e le m b ofs old delta
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._t'2 = Some (Vsingle old) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  ocn_exec ge e le m ifch_increment_store t le' m' out ->
  Mem.store Mfloat32 m b (Ptrofs.unsigned ofs)
    (Vsingle (Float32.add old delta)) = Some m' /\ le' = le.
Proof.
  intros ge e le m b ofs old delta t le' m' out Hp Ho Hd Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt, ifch_increment_store in Hrun.
  inversion Hrun; subst; clear Hrun.
  match goal with H : eval_lvalue _ _ _ _ ifch_pointer _ _ _ |- _ =>
    unfold ifch_pointer in H; inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ (Etempvar FGP._px _) ?v |- _ =>
    assert (v = Vptr b ofs) as Hpointer by (eapply ocn_temp_value; eauto);
    inversion Hpointer; subst; clear Hpointer end.
  match goal with H : eval_expr _ _ _ _ ifch_increment_sum ?v |- _ =>
    assert (v = Vsingle (Float32.add old delta)) by
      (eapply ifch_increment_sum_value; eauto); subst v end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ =>
    cbn in H; inversion H; subst end.
  split; [assumption|reflexivity].
Qed.

Lemma ifch_actual_increment_stage_effect : forall ge e le m b ofs old target delta
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle old) ->
  ocn_exec ge e le m ifch_increment_stage t le' m' out ->
  le' ! FGP._px = Some (Vptr b ofs) /\
  le' ! FGP._target = Some (Vsingle target) /\
  le' ! FGP._delta = Some (Vsingle delta) /\
  Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) =
    Some (Vsingle (Float32.add old delta)).
Proof.
  intros ge e le m b ofs old target delta t le' m' out Hp Ht Hd Hload Hrun.
  unfold ifch_increment_stage in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset FGP._t'2 ifch_pointer)
    _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hstore).
  inversion Hread; subst.
  match goal with Hread : eval_expr _ _ _ _ ifch_pointer ?value |- _ =>
    assert (value = Vsingle old) by (eapply ifch_pointer_read_value; eauto); subst value end.
  destruct (ifch_actual_increment_store ge e
    (PTree.set FGP._t'2 (Vsingle old) le) memory b ofs old delta suf le' m' out
    ltac:(rewrite PTree.gso by discriminate; exact Hp) (PTree.gss _ _ _)
    ltac:(rewrite PTree.gso by discriminate; exact Hd) Hstore) as (Hwritten & ->).
  repeat split; try (rewrite PTree.gso by discriminate; assumption).
  exact (Mem.load_store_same _ _ _ _ _ _ Hwritten).
Qed.

Lemma ifch_actual_choice_effect : forall version ge e le m b ofs candidate target delta
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle candidate) ->
  ocn_exec ge e le m (ifch_choice version) t le' m' out ->
  if ifch_should_clamp candidate target delta
  then out = ifch_returned 1 /\
    Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) = Some (Vsingle target)
  else out = Out_normal /\ m' = m.
Proof.
  intros version ge e le m b ofs candidate target delta t le' m' out Hp Ht Hd Hload Hrun.
  unfold ifch_choice in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ifch_read _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hchoice).
  unfold ifch_read in Hread. inversion Hread; subst.
  match goal with Hread : eval_expr _ _ _ _ ifch_pointer ?value |- _ =>
    assert (value = Vsingle candidate) by (eapply ifch_pointer_read_value; eauto);
    subst value end.
  rewrite (proj2 (ifch_actual_three_stages version)) in Hchoice.
  inversion Hchoice; subst.
  match goal with Hread : eval_expr _ _ _ _ ifch_guard ?value |- _ =>
    assert (value = Val.of_bool (ifch_should_clamp candidate target delta)) by
      (eapply ifch_guard_value; [apply PTree.gss|
        rewrite PTree.gso by discriminate; exact Ht|
        rewrite PTree.gso by discriminate; exact Hd|exact Hread]); subst value end.
  match goal with Hbool : bool_val _ _ _ = Some ?choice |- _ =>
    destruct choice; cbn beta iota in * end.
  all: destruct (ifch_should_clamp candidate target delta) eqn:Hclamp;
    cbn [bool_val Val.of_bool Int.eq] in *; try discriminate.
  - eapply ifch_actual_clamp_returns_target with (ge := ge) (e := e)
      (le := PTree.set FGP._t'1 (Vsingle candidate) le) (m := memory)
      (b := b) (ofs := ofs) (target := target).
    + rewrite PTree.gso by discriminate. exact Hp.
    + rewrite PTree.gso by discriminate. exact Ht.
    + eassumption.
  - match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hskip; subst end. split; reflexivity.
Qed.

Lemma ifch_actual_final_stages_effect : forall version ge e le m b ofs candidate target delta
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle candidate) ->
  ocn_exec ge e le m
    (Ssequence (ifch_choice version) (ifch_return 0)) t le' m' out ->
  Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) = Some
    (Vsingle (if ifch_should_clamp candidate target delta then target else candidate)).
Proof.
  intros version ge e le m b ofs candidate target delta t le' m' out Hp Ht Hd Hload Hrun.
  inversion Hrun; subst.
  - match goal with Hchoice : ClightBigstep.exec_stmt _ _ _ _ _
      (ifch_choice version) _ _ _ _ |- _ =>
      pose proof (ifch_actual_choice_effect version ge e le m b ofs candidate target delta
        _ _ _ _ Hp Ht Hd Hload Hchoice) as HchoiceEffect end.
    destruct (ifch_should_clamp candidate target delta); cbn in *.
    + destruct HchoiceEffect as [Hout _]. discriminate.
    + destruct HchoiceEffect as [_ ->].
      match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (ifch_return 0) _ _ _ _ |- _ =>
        destruct (ifch_constant_return _ _ _ _ _ _ _ _ _ Hr) as (_ & -> & _) end.
      exact Hload.
  - match goal with Hchoice : ClightBigstep.exec_stmt _ _ _ _ _
      (ifch_choice version) _ _ _ _ |- _ =>
      pose proof (ifch_actual_choice_effect version ge e le m b ofs candidate target delta
        _ _ _ _ Hp Ht Hd Hload Hchoice) as HchoiceEffect end.
    destruct (ifch_should_clamp candidate target delta); cbn in *.
    + exact (proj2 HchoiceEffect).
    + destruct HchoiceEffect as [Hout _]. contradiction.
Qed.

(** This is the whole actual helper body, including false/zero returns.
    Every pointer reload and the guard use the memory produced by the real
    preceding store; no preserved-value premise is imposed between stages. *)
Theorem ifch_actual_stock_approach_body_preserves_ceiling : forall version e le m
    b ofs old target delta t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle old) ->
  In (target,delta) ifch_stock_approach_pairs ->
  rank9cf_finite old ->
  (rank9cf_real old <= rank9cf_real ifch_ceiling)%R ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ifch_approach_body version)) t le' m' out ->
  exists written,
    Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) = Some (Vsingle written) /\
    rank9cf_finite written /\
    (rank9cf_real written <= rank9cf_real ifch_ceiling)%R.
Proof.
  intros version e le m b ofs old target delta t le' m' out Hp Ht Hd Hload Hstock Fo Hold Hrun.
  rewrite (proj1 (ifch_actual_three_stages version)) in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ifch_sign_stage _ _ _ _ _ eq_refl Hrun)
    as (sign_le & sign_m & pre & suf & Htrace & Hsign & HafterSign).
  destruct (ifch_actual_sign_stage_effect _ _ _ _ _ _ _ _ _ _ _ _ _
    Hp Ht Hd Hload Hsign) as (-> & HsignP & HsignT & HsignD).
  destruct (ibk_split_sequence _ _ _ _ ifch_increment_stage _ _ _ _ _ eq_refl HafterSign)
    as (increment_le & increment_m & pre2 & suf2 & Htrace2 & Hincrement & Hfinal).
  destruct (ifch_actual_increment_stage_effect _ _ _ _ _ _ _ _ _ _ _ _ _
    HsignP HsignT HsignD Hload Hincrement) as (HincP & HincT & HincD & HincLoad).
  pose proof (ifch_actual_final_stages_effect version
    (Clight.globalenv (selected_clight_target version)) e increment_le increment_m
    b ofs (ifch_candidate old target delta) target (ifch_effective_delta old target delta)
    _ _ _ _ HincP HincT HincD HincLoad Hfinal) as HfinalLoad.
  exists (ifch_approach_result old target delta). split; [exact HfinalLoad|].
  exact (ifch_all_stock_approach_results_are_bounded _ _ _ Hstock Fo Hold).
Qed.

Theorem ifch_completed_stock_approach_preserves_ceiling : forall version m b ofs old
    target delta t m' result,
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle old) ->
  In (target,delta) ifch_stock_approach_pairs ->
  rank9cf_finite old ->
  (rank9cf_real old <= rank9cf_real ifch_ceiling)%R ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifch_approach_body version))
    [Vptr b ofs;Vsingle target;Vsingle delta] t m' result ->
  exists written,
    Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) = Some (Vsingle written) /\
    rank9cf_finite written /\
    (rank9cf_real written <= rank9cf_real ifch_ceiling)%R.
Proof.
  intros version m b ofs old target delta t m' result Hload Hstock Fo Hold Hcall.
  destruct (ifch_actual_approach_shape version)
    as (Hvars & Hparams & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! FGP._px = Some (Vptr b ofs)) as Hp by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (temps ! FGP._target = Some (Vsingle target)) as Htarget by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (temps ! FGP._delta = Some (Vsingle delta)) as Hdelta by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; apply PTree.gss) end.
  eapply ifch_actual_stock_approach_body_preserves_ceiling; eauto.
Qed.

(** The real helper writes only its pointed scale cell: first the increment,
    then at most one clamp. This is an exact store history, so callers can
    derive a frame for disjoint cells without a blanket callee contract. *)
Lemma ifch_actual_increment_stage_store : forall ge e le m b ofs old delta
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle old) ->
  ocn_exec ge e le m ifch_increment_stage t le' m' out ->
  Mem.store Mfloat32 m b (Ptrofs.unsigned ofs)
    (Vsingle (Float32.add old delta)) = Some m'.
Proof.
  intros ge e le m b ofs old delta t le' m' out Hp Hd Hload Hrun.
  unfold ifch_increment_stage in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset FGP._t'2 ifch_pointer)
    _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hstore).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ ifch_pointer ?value |- _ =>
    assert (value = Vsingle old) by (eapply ifch_pointer_read_value; eauto);
    subst value end.
  exact (proj1 (ifch_actual_increment_store ge e
    (PTree.set FGP._t'2 (Vsingle old) le) memory b ofs old delta suf le' m' out
    ltac:(rewrite PTree.gso by discriminate; exact Hp) (PTree.gss _ _ _)
    ltac:(rewrite PTree.gso by discriminate; exact Hd) Hstore)).
Qed.

Lemma ifch_actual_choice_store_history : forall version ge e le m b ofs target
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  ocn_exec ge e le m (ifch_choice version) t le' m' out ->
  m' = m \/ Mem.store Mfloat32 m b (Ptrofs.unsigned ofs)
    (Vsingle target) = Some m'.
Proof.
  intros version ge e le m b ofs target t le' m' out Hp Ht Hrun.
  unfold ifch_choice in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ifch_read _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hchoice).
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ FGP._px Hread eq_refl)
    as (_ & Hsame & Hpx).
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ FGP._target Hread eq_refl)
    as (_ & _ & Htarget).
  assert (Hp' : middle ! FGP._px = Some (Vptr b ofs)) by (rewrite Hpx; exact Hp).
  assert (Ht' : middle ! FGP._target = Some (Vsingle target)) by (rewrite Htarget; exact Ht).
  subst memory. inversion Hchoice; subst.
  match goal with Hbool : bool_val _ _ _ = Some ?choice |- _ =>
    destruct choice; cbn beta iota in * end.
  - right. match goal with Hclamp : ClightBigstep.exec_stmt _ _ _ _ _ ifch_clamp _ _ _ _ |- _ =>
      unfold ifch_clamp in Hclamp;
      destruct (ibk_split_sequence _ _ _ _ ifch_clamp_store _ _ _ _ _ eq_refl Hclamp)
        as (stored_le & stored_m & first_t & last_t & Hct & Hstore & Hreturn);
      destruct (ifch_actual_clamp_store ge e middle m b ofs target
        first_t stored_le stored_m Out_normal Hp' Ht' Hstore)
        as (Hwritten & _);
      destruct (ifch_constant_return _ _ _ _ _ _ _ _ _ Hreturn) as (_ & -> & _);
      exact Hwritten end.
  - match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hskip; subst end. now left.
Qed.

Lemma ifch_actual_final_stages_store_history : forall version ge e le m b ofs target
    t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  ocn_exec ge e le m
    (Ssequence (ifch_choice version) (ifch_return 0)) t le' m' out ->
  m' = m \/ Mem.store Mfloat32 m b (Ptrofs.unsigned ofs)
    (Vsingle target) = Some m'.
Proof.
  intros version ge e le m b ofs target t le' m' out Hp Ht Hrun.
  inversion Hrun; subst.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (ifch_return 0) _ _ _ _ |- _ =>
      destruct (ifch_constant_return _ _ _ _ _ _ _ _ _ Hr) as (_ & -> & _) end.
    eapply ifch_actual_choice_store_history; eauto.
  - eapply ifch_actual_choice_store_history; eauto.
Qed.

Theorem ifch_actual_approach_body_exact_effect : forall version e le m b ofs old
    target delta t le' m' out,
  le ! FGP._px = Some (Vptr b ofs) ->
  le ! FGP._target = Some (Vsingle target) ->
  le ! FGP._delta = Some (Vsingle delta) ->
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle old) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ifch_approach_body version)) t le' m' out ->
  exists middle,
    Mem.store Mfloat32 m b (Ptrofs.unsigned ofs)
      (Vsingle (ifch_candidate old target delta)) = Some middle /\
    (m' = middle \/ Mem.store Mfloat32 middle b (Ptrofs.unsigned ofs)
      (Vsingle target) = Some m') /\
    Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) =
      Some (Vsingle (ifch_approach_result old target delta)).
Proof.
  intros version e le m b ofs old target delta t le' m' out Hp Ht Hd Hload Hrun.
  rewrite (proj1 (ifch_actual_three_stages version)) in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ifch_sign_stage _ _ _ _ _ eq_refl Hrun)
    as (sign_le & sign_m & pre & suf & Htrace & Hsign & HafterSign).
  destruct (ifch_actual_sign_stage_effect _ _ _ _ _ _ _ _ _ _ _ _ _
    Hp Ht Hd Hload Hsign) as (-> & HsignP & HsignT & HsignD).
  destruct (ibk_split_sequence _ _ _ _ ifch_increment_stage _ _ _ _ _ eq_refl HafterSign)
    as (increment_le & increment_m & pre2 & suf2 & Htrace2 & Hincrement & Hfinal).
  pose proof (ifch_actual_increment_stage_store _ _ _ _ _ _ _ _ _ _ _ _
    HsignP HsignD Hload Hincrement) as Hwritten.
  destruct (ifch_actual_increment_stage_effect _ _ _ _ _ _ _ _ _ _ _ _ _
    HsignP HsignT HsignD Hload Hincrement) as (HincP & HincT & HincD & HincLoad).
  pose proof (ifch_actual_final_stages_store_history version _ _ _ _ _ _ _ _ _ _ _
    HincP HincT Hfinal) as Hhistory.
  pose proof (ifch_actual_final_stages_effect version
    (Clight.globalenv (selected_clight_target version)) e increment_le increment_m
    b ofs (ifch_candidate old target delta) target (ifch_effective_delta old target delta)
    _ _ _ _ HincP HincT HincD HincLoad Hfinal) as HfinalLoad.
  exists increment_m. repeat split; assumption.
Qed.

Theorem ifch_completed_approach_exact_effect : forall version m b ofs old target delta
    t m' result,
  Mem.load Mfloat32 m b (Ptrofs.unsigned ofs) = Some (Vsingle old) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifch_approach_body version))
    [Vptr b ofs;Vsingle target;Vsingle delta] t m' result ->
  exists middle,
    Mem.store Mfloat32 m b (Ptrofs.unsigned ofs)
      (Vsingle (ifch_candidate old target delta)) = Some middle /\
    (m' = middle \/ Mem.store Mfloat32 middle b (Ptrofs.unsigned ofs)
      (Vsingle target) = Some m') /\
    Mem.load Mfloat32 m' b (Ptrofs.unsigned ofs) =
      Some (Vsingle (ifch_approach_result old target delta)).
Proof.
  intros version m b ofs old target delta t m' result Hload Hcall.
  destruct (ifch_actual_approach_shape version) as (Hvars & Hparams & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! FGP._px = Some (Vptr b ofs)) as Hp by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (temps ! FGP._target = Some (Vsingle target)) as Htarget by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (temps ! FGP._delta = Some (Vsingle delta)) as Hdelta by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; apply PTree.gss) end.
  eapply ifch_actual_approach_body_exact_effect; eauto.
Qed.

Theorem ifch_pokey_approach_result_bounded : forall old,
  rank9cf_finite old -> (rank9cf_real old < 1)%R ->
  rank9cf_finite (ifch_approach_result old (ifgp_f32 1065353216)
    (ifgp_f32 1036831949)) /\
  (rank9cf_real (ifch_approach_result old (ifgp_f32 1065353216)
    (ifgp_f32 1036831949)) <= 1)%R.
Proof.
  intros old Fo Hold.
  set (target := ifgp_f32 1065353216).
  set (delta := ifgp_f32 1036831949).
  assert (Ft : rank9cf_finite target) by (unfold target, rank9cf_finite, ifgp_f32; vm_compute; reflexivity).
  assert (Fd : rank9cf_finite delta) by (unfold delta, rank9cf_finite, ifgp_f32; vm_compute; reflexivity).
  assert (Ht : (rank9cf_real target = 1)%R) by (unfold target, rank9cf_real, ifgp_f32; vm_compute; nra).
  assert (Hd : (0 < rank9cf_real delta <= 1/4)%R)
    by (unfold delta, rank9cf_real, ifgp_f32; vm_compute; nra).
  assert (Hpeak : (1 <= rank9cf_real ifch_ceiling)%R)
    by (unfold ifch_ceiling, rank9cf_real, ifgp_f32; vm_compute; nra).
  assert (Hcmp : Float32.cmp Cgt old target = false).
  { unfold Float32.cmp, Float32.compare.
    rewrite Bcompare_correct by assumption.
    change (match Rcompare (rank9cf_real old) (rank9cf_real target) with
      | Gt => true | _ => false end = false).
    destruct (Rcompare_spec (rank9cf_real old) (rank9cf_real target)); cbn; try reflexivity; lra. }
  unfold ifch_approach_result, ifch_candidate, ifch_effective_delta. rewrite Hcmp.
  destruct (ifch_positive_increment_under_two _ _ Fo Fd ltac:(lra) ltac:(lra)) as [Fc Hc].
  destruct (ifch_should_clamp (Float32.add old delta) target delta) eqn:Hclamp.
  - split; [exact Ft|lra].
  - split; [exact Fc|].
    destruct (Rle_dec (rank9cf_real (Float32.add old delta)) 1); [assumption|].
    destruct (rank12b_sub_range (Float32.add old delta) target 0 2 Fc Ft
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lra)) as [Fs Hs].
    destruct (rank9cf_mul_range (Float32.sub (Float32.add old delta) target) delta 0 2
      Fs Fd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; nra)) as [Fm Hm].
    unfold ifch_should_clamp in Hclamp.
    rewrite (ifch_finite_nonnegative_cmp_zero _ Fm ltac:(cbn in Hm; lra)) in Hclamp.
    discriminate.
Qed.

(** A huge finite negative signed hitbox cannot add upward placement.
    This removes the old artificial lower-height range; the real rounded
    snap sum must still be finite at the selected physical-model boundary. *)
Theorem ifch_signed_snap_rise_is_at_most_251 : forall movement_y actor_y hitbox_h,
  rank9cf_finite movement_y -> rank9cf_finite actor_y -> rank9cf_finite hitbox_h ->
  (-32768 <= rank9cf_real movement_y <= 32768)%R ->
  (-32768 <= rank9cf_real actor_y)%R -> (rank9cf_real hitbox_h <= 250)%R ->
  rank9cf_finite (Float32.add actor_y hitbox_h) ->
  Float32.cmp Cgt movement_y actor_y = true ->
  (rank9cf_real (Float32.add actor_y hitbox_h) - rank9cf_real movement_y <= 251)%R.
Proof.
  intros movement_y actor_y hitbox_h Fmovement Factor Fheight Bmovement Bactor
    BheightUpper Fsum Hcmp.
  destruct (Rle_dec (rank9cf_real hitbox_h) 0) as [Hnonpositive|Hpositive].
  - pose proof (ibag_greater_true _ _ Fmovement Factor Hcmp) as Hbelow.
    pose proof (ifch_nonpositive_addition_cannot_raise actor_y hitbox_h
      Factor Fheight Fsum Hnonpositive) as HnoRise.
    change (rank9cf_real (Float32.add actor_y hitbox_h) <= rank9cf_real actor_y)%R in HnoRise.
    lra.
  - exact (proj2 (ibag_live_snap_rise_is_at_most_251 movement_y actor_y hitbox_h
      Fmovement Factor Fheight Bmovement Bactor ltac:(lra) Hcmp)).
Qed.
