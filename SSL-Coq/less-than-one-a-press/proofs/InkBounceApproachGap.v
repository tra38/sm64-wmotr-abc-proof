(** A placement-independent bound on the first ordinary bounce snap.

    Stock spawn height is not a live bound: enemies can move and an ordinary
    fake-object pickup can relocate a pool slot.  Instead this file uses the
    actual falling-contact height guard.  If its compared movement height
    still matches the movement height at the bounce, and its actor read still
    matches the bounce's actor read, the upward snap is bounded by the LIVE
    hitbox height, with one conservative unit of binary32 rounding allowance.

    The guard branch is extracted from generated US/JP determine_interaction.
    No claim that every completed handler follows this branch or preserves
    its values is hidden here; those read matches are explicit.  The completed
    bounce really reaches the height store.  No display agreement, world-space
    actor upper bound, or absence of clones is assumed. *)
From Coq Require Import Bool Lia List ZArith Reals Lra.
From Flocq Require Import BinarySingleNaN Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_interaction jp_interaction.
From LessThanOneAPress.Proofs Require Import GameTypes InkBounceProducerEffect
  InkCopyCaller InkFloorResetSource InkFloorResetExecution InkBackwardExecution
  ObjectContactNecessity ContactConsumerExecution Area2Rank9ACoinFlight
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Float32.cmp Float32.compare.
Module BAG := us_interaction.

Definition ibag_determine_body version := match version with
| VersionUS => us_interaction.f_determine_interaction
| VersionJP => jp_interaction.f_determine_interaction end.

(** Follow the concrete initializer/attack/fallback branch layout.  The checked
    equality below prevents a fallback extraction from being passed off as a
    generated branch. *)
Definition ibag_extracted_above_branch version :=
  match fn_body (ibag_determine_body version) with
  | Ssequence _ (Ssequence _ (Ssequence _
      (Ssequence (Ssequence _
        (Sifthenelse _ (Ssequence _ (Sifthenelse _ above _)) _)) _))) => above
  | _ => Sskip
  end.
Definition ibag_above_test := Ebinop Ogt
  (Etempvar BAG._t'16 tfloat) (Etempvar BAG._t'17 tfloat) tint.
Definition ibag_above_set := Sset BAG._interaction
  (Ebinop Oshl (Econst_int Int.one tint) (Econst_int (Int.repr 6) tint) tint).
Definition ibag_above_fragment version :=
  Ssequence (Sset BAG._t'16 ifr_y_cell)
    (Ssequence (Sset BAG._t'17 (ibp_object_y version))
      (Sifthenelse ibag_above_test ibag_above_set Sskip)).

Theorem ibag_above_branch_is_generated : forall version,
  ibag_extracted_above_branch version = ibag_above_fragment version /\
  ibk_normal (ibag_above_fragment version) = true.
Proof. intros []; split; reflexivity. Qed.

Lemma ibag_actual_movement_read : forall version e le m mb mo y answer,
  le ! BAG._m = Some (Vptr mb mo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle y) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ifr_y_cell answer -> answer = Vsingle y.
Proof.
  intros version e le m mb mo y answer Hm Hload Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ ifr_y_cell _ _ _ |- _ =>
    destruct (ifr_state_y_location version _ _ _ _ _ _ _ _ Hm Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn [typeof access_mode] in Hmode; inversion Hmode; subst end.
  match goal with Hread : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m mb
      (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) = Some answer)
      in Hread; congruence end.
Qed.

(** On this actual reached branch, an initially zero interaction becomes the
    hit-from-above mask only by passing the generated movement > actor test.
    This is a branch result, not a classification of every handler history. *)
Theorem ibag_executed_above_branch_requires_higher_movement :
  forall version e le m mb mo ob oo movement_y actor_y t le' m' out,
  le ! BAG._m = Some (Vptr mb mo) ->
  le ! BAG._o = Some (Vptr ob oo) ->
  le ! BAG._interaction = Some (Vint Int.zero) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibag_extracted_above_branch version) t le' m' out ->
  le' ! BAG._interaction = Some (Vint (Int.repr 64)) ->
  Float32.cmp Cgt movement_y actor_y = true.
Proof.
  intros version e le m mb mo ob oo movement_y actor_y t le' m' out
    Hm Ho Hzero Hmovement Hactor Hrun Hresult.
  rewrite (proj1 (ibag_above_branch_is_generated version)) in Hrun.
  unfold ibag_above_fragment in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset BAG._t'16 ifr_y_cell)
    _ _ _ _ _ eq_refl Hrun)
    as (height_le & height_m & height_t & rest_t & Htrace & Hread & Hrest).
  inversion Hread; subst; clear Hread.
  match goal with Hr : eval_expr _ _ _ _ ifr_y_cell ?v |- _ =>
    assert (v = Vsingle movement_y) by
      (eapply ibag_actual_movement_read; eauto); subst v end.
  destruct (ibk_split_sequence _ _ _ _ (Sset BAG._t'17 (ibp_object_y version))
    _ _ _ _ _ eq_refl Hrest)
    as (actor_le & actor_m & actor_t & guard_t & Hresttrace & Hread & Hguard).
  inversion Hread; subst; clear Hread.
  match goal with Hr : eval_expr _ ?environment ?actor_locals ?actor_memory
    (ibp_object_y version) ?v |- _ =>
    assert (v = Vsingle actor_y) by
      (eapply (ibp_object_y_read version environment actor_locals actor_memory
        ob oo actor_y v); [rewrite PTree.gso by discriminate; exact Ho|
        exact Hactor|exact Hr]); subst v end.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hguard.
  inversion Hguard; subst; clear Hguard.
  destruct b.
  - match goal with
    | Hexpr : eval_expr ?ge ?environment ?test_le ?test_m ibag_above_test ?value,
      Hbool : bool_val ?value ?ty ?test_m = Some true |- _ =>
        change (bool_val value tint test_m = Some true) in Hbool;
        eapply (ocn_float_test_is_the_actual_comparison ge environment test_le test_m
          BAG._t'16 BAG._t'17 true movement_y actor_y true)
    end.
    + rewrite PTree.gso by discriminate. apply PTree.gss.
    + apply PTree.gss.
    + unfold ocn_test_value, ibag_above_test. eauto.
  - match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion Hskip; subst; clear Hskip end.
    repeat rewrite PTree.gso in Hresult by discriminate.
    rewrite Hzero in Hresult. discriminate.
Qed.

Lemma ibag_greater_true : forall x y,
  rank9cf_finite x -> rank9cf_finite y ->
  Float32.cmp Cgt x y = true -> (rank9cf_real y < rank9cf_real x)%R.
Proof.
  intros x y Fx Fy H. unfold Float32.cmp, Float32.compare in H.
  rewrite (Bcompare_correct 24 128 x y Fx Fy) in H.
  unfold rank9cf_real. destruct (Rcompare_spec (B2R 24 128 x) (B2R 24 128 y));
    simpl in H; try discriminate; lra.
Qed.

(** The integer ceiling is a proof device, not a game-state assumption.
    Representable integer endpoints bound the rounded sum without asserting
    translation-invariant float rounding.  The deliberately loose 251 bound
    is useful for excluding 1093/1170-unit newly created snap gaps. *)
Theorem ibag_live_snap_rise_is_at_most_251 : forall movement_y actor_y hitbox_h,
  rank9cf_finite movement_y -> rank9cf_finite actor_y -> rank9cf_finite hitbox_h ->
  (-32768 <= rank9cf_real movement_y <= 32768)%R ->
  (-32768 <= rank9cf_real actor_y)%R ->
  (-32768 <= rank9cf_real hitbox_h <= 250)%R ->
  Float32.cmp Cgt movement_y actor_y = true ->
  rank9cf_finite (Float32.add actor_y hitbox_h) /\
  (rank9cf_real (Float32.add actor_y hitbox_h) -
    rank9cf_real movement_y <= 251)%R.
Proof.
  intros movement_y actor_y hitbox_h Fmovement Factor Fhitbox
    Bmovement Bactor Bheight Hcmp.
  pose proof (ibag_greater_true _ _ Fmovement Factor Hcmp) as Hbelow.
  pose proof (archimed (rank9cf_real movement_y)) as [Hup Hallowance].
  assert (HupLow : -32768 <= up (rank9cf_real movement_y)).
  { apply le_IZR. cbn. lra. }
  assert (HupHigh : up (rank9cf_real movement_y) <= 32769).
  { apply le_IZR. cbn. lra. }
  assert (Hsum : (IZR (-65536) <= rank9cf_real actor_y + rank9cf_real hitbox_h <=
    IZR (up (rank9cf_real movement_y) + 250))%R).
  { rewrite plus_IZR. cbn. lra. }
  destruct (rank9cf_add_range actor_y hitbox_h (-65536)
    (up (rank9cf_real movement_y) + 250) Factor Fhitbox
    ltac:(lia) ltac:(lia) ltac:(lia) Hsum) as [Fsum Bsum].
  split; [exact Fsum|]. rewrite plus_IZR in Bsum. cbn in Bsum. lra.
Qed.

(** Pair the passed real guard with the completed real bounce.  The branch's
    actor and movement reads must match the bounce-entry values.  This is not
    a blanket frame for attack_object, bounce_back_from_attack or sound. *)
Definition InkBouncePlacementIndependentGapCheckpoint : Prop :=
  forall version e guard_le guard_m mb mo ob oo movement_y actor_y hitbox_h
    guard_t guard_le' guard_m' guard_out bounce_m velocity t m' result,
  guard_le ! BAG._m = Some (Vptr mb mo) ->
  guard_le ! BAG._o = Some (Vptr ob oo) ->
  guard_le ! BAG._interaction = Some (Vint Int.zero) ->
  Mem.load Mfloat32 guard_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 guard_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e guard_le guard_m
    (ibag_extracted_above_branch version) guard_t guard_le' guard_m' guard_out ->
  guard_le' ! BAG._interaction = Some (Vint (Int.repr 64)) ->
  Mem.load Mfloat32 bounce_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 bounce_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  Mem.load Mfloat32 bounce_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h) ->
  rank9cf_finite movement_y -> rank9cf_finite actor_y -> rank9cf_finite hitbox_h ->
  (-32768 <= rank9cf_real movement_y <= 32768)%R ->
  (-32768 <= rank9cf_real actor_y)%R ->
  (-32768 <= rank9cf_real hitbox_h <= 250)%R ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) bounce_m
    (Internal (ibp_body version)) [Vptr mb mo; Vptr ob oo; Vsingle velocity]
    t m' result ->
  exists start_le cut_le cut_m final_le out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env start_le bounce_m
      (ibp_height_stage version) E0 cut_le cut_m Out_normal /\
    Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
      Some (Vsingle (Float32.add actor_y hitbox_h)) /\
    (rank9cf_real (Float32.add actor_y hitbox_h) -
      rank9cf_real movement_y <= 251)%R /\
    (forall chunk b offset,
      b <> mb -> Mem.load chunk cut_m b offset = Mem.load chunk bounce_m b offset) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env cut_le cut_m
      (ibp_tail version) t final_le m' out.

Theorem ibag_completed_fresh_guard_bounce_has_bounded_rise :
  InkBouncePlacementIndependentGapCheckpoint.
Proof.
  unfold InkBouncePlacementIndependentGapCheckpoint.
  intros version e guard_le guard_m mb mo ob oo movement_y actor_y hitbox_h
    guard_t guard_le' guard_m' guard_out bounce_m velocity t m' result
    Hm Ho Hzero HguardMovement HguardActor Hguard Hresult Hmovement Hy Hh
    Fmovement Factor Fheight Bmovement Bactor Bheight Hcall.
  pose proof (ibag_executed_above_branch_requires_higher_movement version e guard_le guard_m
    mb mo ob oo movement_y actor_y guard_t guard_le' guard_m' guard_out
    Hm Ho Hzero HguardMovement HguardActor Hguard Hresult) as Hcmp.
  destruct (ibag_live_snap_rise_is_at_most_251 _ _ _ Fmovement Factor Fheight
    Bmovement Bactor Bheight Hcmp) as [_ Hbound].
  destruct (ibp_completed_bounce_reaches_height_checkpoint version bounce_m mb mo ob oo
    actor_y hitbox_h velocity t m' result Hy Hh Hcall)
    as (start_le & cut_le & cut_m & final_le & suffix & out &
      Htrace & Hstage & Hstore & Hframe & Htail).
  subst suffix. exists start_le, cut_le, cut_m, final_le, out.
  split; [exact Hstage|].
  split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  repeat split; assumption.
Qed.

(** If the displayed Y was synchronized with the actually compared movement
    Y on entry to this bounce, the other-block frame turns the displacement
    bound into a bound on the NEW upward movement/display gap at the snap.
    The display receiver is obtained from MarioState's real marioObj field.
    No assumption says that all earlier histories were synchronized. *)
Definition InkBounceFreshDisplayGapCheckpoint : Prop :=
  forall version e guard_le guard_m mb mo ob oo movement_y actor_y hitbox_h
    guard_t guard_le' guard_m' guard_out bounce_m display_b display_ofs velocity t m' result,
  guard_le ! BAG._m = Some (Vptr mb mo) ->
  guard_le ! BAG._o = Some (Vptr ob oo) ->
  guard_le ! BAG._interaction = Some (Vint Int.zero) ->
  Mem.load Mfloat32 guard_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 guard_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e guard_le guard_m
    (ibag_extracted_above_branch version) guard_t guard_le' guard_m' guard_out ->
  guard_le' ! BAG._interaction = Some (Vint (Int.repr 64)) ->
  Mem.load Mfloat32 bounce_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 bounce_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  Mem.load Mfloat32 bounce_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h) ->
  Mem.load Mint32 bounce_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) =
    Some (Vptr display_b display_ofs) ->
  mb <> display_b ->
  Mem.load Mfloat32 bounce_m display_b
    (Ptrofs.unsigned (Ptrofs.add display_ofs (Ptrofs.repr 36))) =
    Some (Vsingle movement_y) ->
  rank9cf_finite movement_y -> rank9cf_finite actor_y -> rank9cf_finite hitbox_h ->
  (-32768 <= rank9cf_real movement_y <= 32768)%R ->
  (-32768 <= rank9cf_real actor_y)%R ->
  (-32768 <= rank9cf_real hitbox_h <= 250)%R ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) bounce_m
    (Internal (ibp_body version)) [Vptr mb mo; Vptr ob oo; Vsingle velocity]
    t m' result ->
  exists start_le cut_le cut_m final_le out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env start_le bounce_m
      (ibp_height_stage version) E0 cut_le cut_m Out_normal /\
    Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
      Some (Vsingle (Float32.add actor_y hitbox_h)) /\
    Mem.load Mfloat32 cut_m display_b
      (Ptrofs.unsigned (Ptrofs.add display_ofs (Ptrofs.repr 36))) =
      Some (Vsingle movement_y) /\
    (rank9cf_real (Float32.add actor_y hitbox_h) -
      rank9cf_real movement_y <= 251)%R /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env cut_le cut_m
      (ibp_tail version) t final_le m' out.

Theorem ibag_completed_bounce_creates_at_most_251_display_gap :
  InkBounceFreshDisplayGapCheckpoint.
Proof.
  unfold InkBounceFreshDisplayGapCheckpoint.
  intros version e guard_le guard_m mb mo ob oo movement_y actor_y hitbox_h
    guard_t guard_le' guard_m' guard_out bounce_m display_b display_ofs velocity t m' result
    Hm Ho Hzero HguardMovement HguardActor Hguard Hresult Hmovement Hy Hh
    HdisplayReceiver Hseparate Hdisplay Fmovement Factor Fheight Bmovement Bactor Bheight Hcall.
  destruct (ibag_completed_fresh_guard_bounce_has_bounded_rise version e guard_le guard_m
    mb mo ob oo movement_y actor_y hitbox_h guard_t guard_le' guard_m' guard_out
    bounce_m velocity t m' result Hm Ho Hzero HguardMovement HguardActor Hguard Hresult
    Hmovement Hy Hh Fmovement Factor Fheight Bmovement Bactor Bheight Hcall)
    as (start_le & cut_le & cut_m & final_le & out & Hstage & Hsnap & Hbound & Hframe & Htail).
  exists start_le, cut_le, cut_m, final_le, out.
  split; [exact Hstage|]. split; [exact Hsnap|]. split.
  - rewrite Hframe; [exact Hdisplay|congruence].
  - split; assumption.
Qed.

(** The stronger fresh-contact case starts with all three Y records equal.
    Its raw collision Y and display Y belong to the actual incoming marioObj
    receiver, on a block separate from MarioState.  The height-store frame
    therefore bounds both newly created M-C and M-D gaps.  This does not
    bound an already inherited low collision record or the later tail. *)
Definition InkBounceFreshSynchronizedGapCheckpoint : Prop :=
  forall version e guard_le guard_m mb mo ob oo movement_y actor_y hitbox_h
    guard_t guard_le' guard_m' guard_out bounce_m mario_b mario_ofs velocity t m' result,
  guard_le ! BAG._m = Some (Vptr mb mo) ->
  guard_le ! BAG._o = Some (Vptr ob oo) ->
  guard_le ! BAG._interaction = Some (Vint Int.zero) ->
  Mem.load Mfloat32 guard_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 guard_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e guard_le guard_m
    (ibag_extracted_above_branch version) guard_t guard_le' guard_m' guard_out ->
  guard_le' ! BAG._interaction = Some (Vint (Int.repr 64)) ->
  Mem.load Mfloat32 bounce_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 bounce_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 164))) =
    Some (Vsingle actor_y) ->
  Mem.load Mfloat32 bounce_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle hitbox_h) ->
  Mem.load Mint32 bounce_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) =
    Some (Vptr mario_b mario_ofs) ->
  mb <> mario_b ->
  Mem.load Mfloat32 bounce_m mario_b
    (Ptrofs.unsigned (Ptrofs.add mario_ofs (Ptrofs.repr 36))) =
    Some (Vsingle movement_y) ->
  Mem.load Mfloat32 bounce_m mario_b
    (Ptrofs.unsigned (Ptrofs.add mario_ofs (Ptrofs.repr 164))) =
    Some (Vsingle movement_y) ->
  rank9cf_finite movement_y -> rank9cf_finite actor_y -> rank9cf_finite hitbox_h ->
  (-32768 <= rank9cf_real movement_y <= 32768)%R ->
  (-32768 <= rank9cf_real actor_y)%R ->
  (-32768 <= rank9cf_real hitbox_h <= 250)%R ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) bounce_m
    (Internal (ibp_body version)) [Vptr mb mo; Vptr ob oo; Vsingle velocity]
    t m' result ->
  exists start_le cut_le cut_m final_le out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env start_le bounce_m
      (ibp_height_stage version) E0 cut_le cut_m Out_normal /\
    Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
      Some (Vsingle (Float32.add actor_y hitbox_h)) /\
    Mem.load Mfloat32 cut_m mario_b
      (Ptrofs.unsigned (Ptrofs.add mario_ofs (Ptrofs.repr 36))) =
      Some (Vsingle movement_y) /\
    Mem.load Mfloat32 cut_m mario_b
      (Ptrofs.unsigned (Ptrofs.add mario_ofs (Ptrofs.repr 164))) =
      Some (Vsingle movement_y) /\
    (rank9cf_real (Float32.add actor_y hitbox_h) -
      rank9cf_real movement_y <= 251)%R /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env cut_le cut_m
      (ibp_tail version) t final_le m' out.

Theorem ibag_completed_bounce_creates_at_most_251_synchronized_gap :
  InkBounceFreshSynchronizedGapCheckpoint.
Proof.
  unfold InkBounceFreshSynchronizedGapCheckpoint.
  intros version e guard_le guard_m mb mo ob oo movement_y actor_y hitbox_h
    guard_t guard_le' guard_m' guard_out bounce_m mario_b mario_ofs velocity t m' result
    Hm Ho Hzero HguardMovement HguardActor Hguard Hresult Hmovement Hy Hh
    HmarioReceiver Hseparate Hdisplay Hraw Fmovement Factor Fheight
    Bmovement Bactor Bheight Hcall.
  destruct (ibag_completed_fresh_guard_bounce_has_bounded_rise version e guard_le guard_m
    mb mo ob oo movement_y actor_y hitbox_h guard_t guard_le' guard_m' guard_out
    bounce_m velocity t m' result Hm Ho Hzero HguardMovement HguardActor Hguard Hresult
    Hmovement Hy Hh Fmovement Factor Fheight Bmovement Bactor Bheight Hcall)
    as (start_le & cut_le & cut_m & final_le & out & Hstage & Hsnap & Hbound & Hframe & Htail).
  exists start_le, cut_le, cut_m, final_le, out.
  split; [exact Hstage|]. split; [exact Hsnap|]. split.
  - rewrite Hframe; [exact Hdisplay|congruence].
  - split.
    + rewrite Hframe; [exact Hraw|congruence].
    + split; assumption.
Qed.
