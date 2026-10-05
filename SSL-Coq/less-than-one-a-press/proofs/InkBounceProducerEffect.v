(** The actual bounce height write, before its sound call.

    This checkpoint pins down a proposed height producer, rather than treating
    the stored 30/80 vertical speed as a position displacement.  The later
    sound/action/movement calls and reachable actor scaling are not framed
    by assumption.  In particular this theorem does not assert a whole-frame
    gap or a controller-reachable bounce near the upper warp. *)
From Coq Require Import Bool Lia List ZArith Reals Lra.
From Flocq Require Import BinarySingleNaN Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_interaction jp_interaction
  us_obj_behaviors_2 jp_obj_behaviors_2 us_ssl_area1_macro jp_ssl_area1_macro
  us_behavior_data jp_behavior_data.
From LessThanOneAPress.Proofs Require Import GameTypes InkCopyCaller
  InkRawCopyExpressions InkFloorResetSource InkFloorResetExecution
  InkControllerSource InkControllerEdge InkBackwardExecution
  ObjectContactNecessity ObjectContactReadback ObjectContactPhaseReadback ContactConsumerExecution
  Area2Rank12BContact
  EyerokRank15LiveMovement SelectedClightTarget ASTFacts Area2Rank9ACoinFlight.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Float32.cmp Float32.compare.
Module IBP := us_interaction.

Definition ibp_body version := match version with
| VersionUS => us_interaction.f_bounce_off_object
| VersionJP => jp_interaction.f_bounce_off_object end.
Definition ibp_height_read := ics_field IBP._o IBP._Object IBP._hitboxHeight tfloat.
Definition ibp_object_y version := rank15_raw_float_expression version IBP._o
  (Ebinop Oadd (Econst_int (Int.repr 6) tint)
    (Econst_int Int.one tint) tint).
Definition ibp_sum := Ebinop Oadd (Etempvar IBP._t'3 tfloat)
  (Etempvar IBP._t'4 tfloat) tfloat.
Definition ibp_height_stage version := Ssequence
  (Sset IBP._t'3 (ibp_object_y version))
  (Ssequence (Sset IBP._t'4 ibp_height_read) (Sassign ifr_y_cell ibp_sum)).
Definition ibp_tail version := match fn_body (ibp_body version) with
| Ssequence _ tail => tail | _ => Sskip end.

Theorem ibp_height_stage_is_generated : forall version,
  fn_vars (ibp_body version) = [] /\
  fn_body (ibp_body version) =
    Ssequence (ibp_height_stage version) (ibp_tail version) /\
  ibk_normal (ibp_height_stage version) = true /\
  ifr_keeps_temp IBP._m (ibp_height_stage version) = true /\
  ifr_keeps_temp IBP._o (ibp_height_stage version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ibp_object_y_read : forall version e le m ob oo height answer,
  le ! IBP._o = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle height) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ibp_object_y version) answer -> answer = Vsingle height.
Proof.
  intros version e le m ob oo height answer Ho Hload Hread.
  assert (Mem.load Mfloat32 m ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 7))) = Some (Vsingle height))
    as Hraw.
  { unfold rank15_raw_address.
    change (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr 7)))
      with (Ptrofs.repr 28).
    rewrite Ptrofs.add_assoc. exact Hload. }
  assert (eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ibp_object_y version) (Vsingle height)) as Hconstructed.
  { unfold ibp_object_y. eapply rank15_raw_float_read;
      [exact Ho|apply rank15_y_index_evaluates|reflexivity|exact Hraw]. }
  eapply (proj1 (ocr_expression_lvalue_unique _ _ _ _)); eauto.
Qed.

Lemma ibp_sum_value : forall ge e le m y h answer,
  le ! IBP._t'3 = Some (Vsingle y) ->
  le ! IBP._t'4 = Some (Vsingle h) ->
  eval_expr ge e le m ibp_sum answer -> answer = Vsingle (Float32.add y h).
Proof.
  intros ge e le m y h answer Hy Hh Hr. unfold ibp_sum in Hr.
  inversion Hr; subst.
  - match goal with H3 : eval_expr _ _ _ _ (Etempvar IBP._t'3 _) ?v |- _ =>
      assert (v = Vsingle y) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H4 : eval_expr _ _ _ _ (Etempvar IBP._t'4 _) ?v |- _ =>
      assert (v = Vsingle h) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn in Hsem; inversion Hsem; reflexivity end.
  - match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Theorem ibp_actual_height_stage_store :
  forall version e le m mb mo ob oo object_y hitbox_h t le' m' out,
  le ! IBP._m = Some (Vptr mb mo) ->
  le ! IBP._o = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle object_y) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibp_height_stage version) t le' m' out ->
  Mem.store Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64)))
    (Vsingle (Float32.add object_y hitbox_h)) = Some m' /\
  le' = PTree.set IBP._t'4 (Vsingle hitbox_h)
    (PTree.set IBP._t'3 (Vsingle object_y) le) /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m mb mo ob oo object_y hitbox_h t le' m' out
    Hm Ho Hy Hh Hrun.
  unfold ibp_height_stage, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  pose proof (ibp_object_y_read version e le _ ob oo object_y _ Ho Hy H8) as Hvalue.
  subst v0.
  assert ((PTree.set IBP._t'3 (Vsingle object_y) le) ! IBP._o = Some (Vptr ob oo))
    as HoNow by (rewrite PTree.gso by discriminate; exact Ho).
  match goal with Hr : eval_expr _ _ _ _ ibp_height_read ?v |- _ =>
    pose proof (ice_field_read (Clight.globalenv (selected_clight_target version))
      e (PTree.set IBP._t'3 (Vsingle object_y) le) _
      IBP._o IBP._Object IBP._hitboxHeight tfloat ob oo 508 Mfloat32
      (Vsingle hitbox_h) v HoNow (ocp_selected_height version) eq_refl Hh Hr)
      as Hhitbox;
    subst v end.
  match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  assert ((PTree.set IBP._t'4 (Vsingle hitbox_h)
    (PTree.set IBP._t'3 (Vsingle object_y) le)) ! IBP._m = Some (Vptr mb mo))
    as HmNow by (repeat rewrite PTree.gso by discriminate; exact Hm).
  match goal with Hl : eval_lvalue _ _ _ _ ifr_y_cell _ _ _ |- _ =>
    destruct (ifr_state_y_location _ _ _ _ _ _ _ _ _ HmNow Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ ibp_sum ?v |- _ =>
    pose proof (ibp_sum_value (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBP._t'4 (Vsingle hitbox_h)
        (PTree.set IBP._t'3 (Vsingle object_y) le)) _ object_y hitbox_h v
      ltac:(rewrite PTree.gso by discriminate; apply PTree.gss)
      ltac:(apply PTree.gss) Hr) as Hsum;
    subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  repeat split; try reflexivity; assumption.
Qed.

(** A completed real helper call reaches this store; no premise about the
    external sound effect or the helper's final memory is introduced. *)
Definition InkBounceHeightCheckpoint : Prop :=
  forall version m mb mo ob oo object_y hitbox_h velocity t m' result,
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle object_y) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ibp_body version)) [Vptr mb mo; Vptr ob oo; Vsingle velocity]
    t m' result ->
  exists start_le cut_le cut_m final_le suffix out,
    t = suffix /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env start_le m
      (ibp_height_stage version) E0 cut_le cut_m Out_normal /\
    Mem.store Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64)))
      (Vsingle (Float32.add object_y hitbox_h)) = Some cut_m /\
    (forall chunk b offset,
      b <> mb -> Mem.load chunk cut_m b offset = Mem.load chunk m b offset) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env cut_le cut_m
      (ibp_tail version) suffix final_le m' out.

Theorem ibp_completed_bounce_reaches_height_checkpoint : InkBounceHeightCheckpoint.
Proof.
  unfold InkBounceHeightCheckpoint.
  intros version m mb mo ob oo object_y hitbox_h velocity t m' result Hy Hh Hcall.
  destruct (ibp_height_stage_is_generated version) as (Hvars & Hbody & Hnormal & _).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IBP._m = Some (Vptr mb mo) /\ temps ! IBP._o = Some (Vptr ob oo))
      as [Hm Ho] by (destruct version; cbn in Hbind; inversion Hbind;
        split; reflexivity) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (cut_le & cut_m & pre & suffix & Htrace & Hstage & Hsuffix) end.
  destruct (ibp_actual_height_stage_store _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hm Ho Hy Hh Hstage) as (Hstore & _ & -> & _).
  exists le1, cut_le, cut_m, le2, suffix, out.
  split; [exact Htrace|]. split; [exact Hstage|]. split; [exact Hstore|].
  split.
  - intros chunk b offset Hseparate.
    eapply Mem.load_store_other; [exact Hstore|left; congruence].
  - exact Hsuffix.
Qed.

(** The scale-independent templates are stock data.  obj_set_hitbox multiplies
    them by the live graphics scale; 50/20/60 are NOT all-history live bounds. *)
Definition ibp_hitbox_template_height (data : list init_data) :=
  match nth_error data 6 with Some (Init_int16 height) => Some (Int.signed height)
  | _ => None end.
Theorem ibp_stock_bounce_templates_checked :
  ibp_hitbox_template_height (gvar_init us_obj_behaviors_2.v_sGoombaHitbox) = Some 50 /\
  ibp_hitbox_template_height (gvar_init jp_obj_behaviors_2.v_sGoombaHitbox) = Some 50 /\
  ibp_hitbox_template_height (gvar_init us_obj_behaviors_2.v_sPokeyBodyPartHitbox) = Some 20 /\
  ibp_hitbox_template_height (gvar_init jp_obj_behaviors_2.v_sPokeyBodyPartHitbox) = Some 20 /\
  ibp_hitbox_template_height (gvar_init us_obj_behaviors_2.v_sFlyGuyHitbox) = Some 60 /\
  ibp_hitbox_template_height (gvar_init jp_obj_behaviors_2.v_sFlyGuyHitbox) = Some 60 /\
  ibp_hitbox_template_height (gvar_init us_obj_behaviors_2.v_sKleptoHitbox) = Some 250 /\
  ibp_hitbox_template_height (gvar_init jp_obj_behaviors_2.v_sKleptoHitbox) = Some 250.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** Stock spawn records, not a claim that the actor is reachable there at the
    required timer, or that its child hitbox is already initialized. *)
Definition ibp_area1_goombas :=
  [[68; 6068; 51; 2800; 0]; [68; 5535; 51; 3377; 0]; [68; 5980; 51; 3911; 0]].
Definition ibp_area1_pokeys :=
  [[170; 4602; 40; 4622; 0]; [170; 5057; 143; 256; 0];
   [170; -6858; 8; -3711; 0]; [170; -5372; 64; 3083; 0]].
Definition ibp_area1_fly_guys := [[185; 3500; 149; 5600; 0]].
Definition ibp_area1_fire_fly_guys :=
  [[117; 1440; 800; -960; 0]; [117; -3400; 1160; -1120; 0]].
Theorem ibp_named_area1_bounce_actor_records_checked : forall version,
  let data := gvar_init (match version with
    | VersionUS => us_ssl_area1_macro.v_ssl_seg7_area_1_macro_objs
    | VersionJP => jp_ssl_area1_macro.v_ssl_seg7_area_1_macro_objs end) in
  records_with_tag 68 data = ibp_area1_goombas /\
  records_with_tag 170 data = ibp_area1_pokeys /\
  records_with_tag 185 data = ibp_area1_fly_guys /\
  records_with_tag 117 data = ibp_area1_fire_fly_guys.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Theorem ibp_fly_guy_twirl_and_initial_scale_commands_checked : forall version,
  let data := gvar_init (match version with
    | VersionUS => us_behavior_data.v_bhvFlyGuy
    | VersionJP => jp_behavior_data.v_bhvFlyGuy end) in
  nth_error data 13 = Some (Init_int32 (Int.repr 272760960)) /\
  nth_error data 15 = Some (Init_int32 (Int.repr 838860950)).
Proof. intros []; split; reflexivity. Qed.

(** Both bounce velocities are real supplied literals in the handlers.
    Velocity 80 does not itself add 80 to Mario's height. *)
Theorem ibp_bounce_velocities_are_generated : forall version,
  statement_mentions_float32_bits_s 1106247680
    (fn_body (match version with VersionUS => us_interaction.f_interact_bounce_top
      | VersionJP => jp_interaction.f_interact_bounce_top end)) = true /\
  statement_mentions_float32_bits_s 1117782016
    (fn_body (match version with VersionUS => us_interaction.f_interact_bounce_top
      | VersionJP => jp_interaction.f_interact_bounce_top end)) = true.
Proof. intros []; vm_compute; split; reflexivity. Qed.

Definition ibp_f32 (z : Z) := Float32.of_int (Int.repr z).
(** Finite bounded-height diagnostic, NOT a bound over unclassified scaling or
    inherited discrepancies.  Even actor raw position Y=768 and live height=90
    produce Y=858, below both tested high-movement installation heights. *)
Theorem ibp_named_small_snap_is_below_installers :
  Int.unsigned (Float32.to_bits (Float32.add (ibp_f32 768) (ibp_f32 90))) = 1146519552 /\
  Float32.cmp Clt (Float32.add (ibp_f32 768) (ibp_f32 90)) (ibp_f32 1861) = true /\
  Float32.cmp Clt (Float32.add (ibp_f32 768) (ibp_f32 90))
    (Float32.of_bits (Int.repr 1156733869)) = true /\
  1861 - 768 = 1093 /\ 858 - 768 = 90.
Proof. vm_compute; repeat split; reflexivity. Qed.

Theorem ibp_named_nominal_snaps_remain_below_variant :
  map (fun h => Float32.cmp Clt (Float32.add (ibp_f32 768) (ibp_f32 h))
    (ibp_f32 1861)) [75; 60; 90; 250] = [true; true; true; true].
Proof. vm_compute; reflexivity. Qed.

(** Do not mistake the upward obstruction for a bound on every direction of
    mismatch.  A sufficiently negative LIVE hitbox would snap downward;
    this numeric candidate does not establish reachable Fly Guy scaling,
    contact registration, or survival into a later copy/query/warp. *)
Theorem ibp_negative_live_height_has_a_downward_candidate :
  Int.unsigned (Float32.to_bits
    (Float32.add (ibp_f32 1861) (ibp_f32 (-1093)))) = 1145044992 /\
  Float32.cmp Cgt (ibp_f32 1861)
    (Float32.add (ibp_f32 1861) (ibp_f32 (-1093))) = true /\
  1861 - 768 = 1093.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** This is an all-binary32 arithmetic obstruction UNDER explicit live-value
    bounds.  It does not replace actor-scale reachability with template data.
    It allows negative live hitbox heights, provided the represented values
    are finite and their sum remains in this stated ordinary numeric range. *)
Theorem ibp_bounded_live_snap_cannot_make_variant_height : forall object_y hitbox_h,
  rank9cf_finite object_y -> rank9cf_finite hitbox_h ->
  (-32768 <= rank9cf_real object_y <= 768)%R ->
  (-32768 <= rank9cf_real hitbox_h <= 250)%R ->
  rank9cf_finite (Float32.add object_y hitbox_h) /\
  (rank9cf_real (Float32.add object_y hitbox_h) <= 1018)%R /\
  Float32.cmp Clt (Float32.add object_y hitbox_h) (ibp_f32 1861) = true.
Proof.
  intros object_y hitbox_h Fy Fh Hy Hh.
  destruct (rank9cf_add_range object_y hitbox_h (-65536) 1018 Fy Fh
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lra)) as [Fsum Hsum].
  destruct (rank9cf_integer_exact 1861 ltac:(lia)) as [H1861 F1861].
  split; [exact Fsum|]. split; [lra|].
  unfold Float32.cmp, Float32.compare.
  rewrite Bcompare_correct by assumption.
  rewrite Rcompare_Lt.
  - reflexivity.
  - change (rank9cf_real (Float32.add object_y hitbox_h) <
      rank9cf_real (rank9cf_integer 1861))%R.
    rewrite H1861. cbn in Hsum. lra.
Qed.

Definition InkBounceBoundedProducerCheckpoint : Prop :=
  forall version m mb mo ob oo object_y hitbox_h velocity t m' result,
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle object_y) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h) ->
  rank9cf_finite object_y -> rank9cf_finite hitbox_h ->
  (-32768 <= rank9cf_real object_y <= 768)%R ->
  (-32768 <= rank9cf_real hitbox_h <= 250)%R ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ibp_body version)) [Vptr mb mo; Vptr ob oo; Vsingle velocity]
    t m' result ->
  exists start_le cut_le cut_m final_le out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env start_le m
      (ibp_height_stage version) E0 cut_le cut_m Out_normal /\
    Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
      Some (Vsingle (Float32.add object_y hitbox_h)) /\
    (rank9cf_real (Float32.add object_y hitbox_h) <= 1018)%R /\
    Float32.cmp Clt (Float32.add object_y hitbox_h) (ibp_f32 1861) = true /\
    (forall chunk b offset,
      b <> mb -> Mem.load chunk cut_m b offset = Mem.load chunk m b offset) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env cut_le cut_m
      (ibp_tail version) t final_le m' out.

(** This composes the numeric bound with the reached store in the actual
    US/JP call.  No premise requires movement/collision/display agreement. *)
Theorem ibp_completed_bounded_bounce_is_insufficient_at_snap :
  InkBounceBoundedProducerCheckpoint.
Proof.
  unfold InkBounceBoundedProducerCheckpoint.
  intros version m mb mo ob oo object_y hitbox_h velocity t m' result
    Hy Hh Fy Fh By Bh Hcall.
  destruct (ibp_completed_bounce_reaches_height_checkpoint version m mb mo ob oo
    object_y hitbox_h velocity t m' result Hy Hh Hcall)
    as (start_le & cut_le & cut_m & final_le & suffix & out &
      Htrace & Hstage & Hstore & Hframe & Htail).
  subst suffix.
  destruct (ibp_bounded_live_snap_cannot_make_variant_height object_y hitbox_h
    Fy Fh By Bh) as (_ & Hbound & Hsmall).
  exists start_le, cut_le, cut_m, final_le, out.
  split; [exact Hstage|].
  split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  repeat split; assumption.
Qed.

(** The two values consumed by the actual passed contact guard must still
    describe this bounce.  With zero down offsets, they are Mario's raw
    collision bottom and the actor's top.  We expose that exact read matching
    instead of assuming a whole collision-to-interaction memory frame. *)
Definition InkBounceFreshContactNoDownwardCheckpoint : Prop :=
  forall version e contact_le contact_m raw_y m mb mo ob oo object_y hitbox_h
    velocity t m' result,
  (exists initial_le initial_m contact_trace final_le final_m radius_le radius_m
      input_trace height_trace registration_trace,
    ocn_ordered_contact_checkpoints version e initial_le initial_m contact_trace
      final_le final_m radius_le radius_m contact_le contact_m input_trace
      height_trace registration_trace) ->
  contact_le ! RC._sp3C = Some (Vsingle raw_y) ->
  contact_le ! RC._sp1C = Some (Vsingle (Float32.add object_y hitbox_h)) ->
  rank9cf_finite raw_y -> rank9cf_finite (Float32.add object_y hitbox_h) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle object_y) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ibp_body version)) [Vptr mb mo; Vptr ob oo; Vsingle velocity]
    t m' result ->
  exists start_le cut_le cut_m final_le out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env start_le m
      (ibp_height_stage version) E0 cut_le cut_m Out_normal /\
    Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
      Some (Vsingle (Float32.add object_y hitbox_h)) /\
    (rank9cf_real raw_y <= rank9cf_real (Float32.add object_y hitbox_h))%R /\
    (forall chunk b offset,
      b <> mb -> Mem.load chunk cut_m b offset = Mem.load chunk m b offset) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env cut_le cut_m
      (ibp_tail version) t final_le m' out.

Theorem ibp_fresh_contact_bounce_cannot_snap_below_collision :
  InkBounceFreshContactNoDownwardCheckpoint.
Proof.
  unfold InkBounceFreshContactNoDownwardCheckpoint.
  intros version e contact_le contact_m raw_y m mb mo ob oo object_y hitbox_h
    velocity t m' result Hcontact Hraw Htop Fraw Fsum Hy Hh Hcall.
  destruct Hcontact as (initial_le & initial_m & contact_trace & contact_final_le &
    contact_final_m & radius_le & radius_m & input_trace & height_trace &
    registration_trace & Hordered).
  destruct Hordered as (_ & _ & _ & _ & Htest & _).
  pose proof (ocn_float_test_is_the_actual_comparison _ _ _ _ _ _ true _ _ _
    Hraw Htop Htest) as Hcmp.
  change (Float32.cmp (swap_comparison Clt) raw_y
    (Float32.add object_y hitbox_h) = false) in Hcmp.
  rewrite Float32.cmp_swap in Hcmp.
  pose proof (rank9cf_less_false (Float32.add object_y hitbox_h) raw_y
    Fsum Fraw Hcmp) as Hbound.
  destruct (ibp_completed_bounce_reaches_height_checkpoint version m mb mo ob oo
    object_y hitbox_h velocity t m' result Hy Hh Hcall)
    as (start_le & cut_le & cut_m & final_le & suffix & out &
      Htrace & Hstage & Hstore & Hframe & Htail).
  subst suffix. exists start_le, cut_le, cut_m, final_le, out.
  split; [exact Hstage|].
  split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  repeat split; assumption.
Qed.
