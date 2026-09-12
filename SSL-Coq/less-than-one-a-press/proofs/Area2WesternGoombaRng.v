(** The western Goomba's random jump is not a moving jump. Execute the
    actual generated velocity tail, after the sound call and action store:
    it clears forward speed and supplies the regular Goomba's vertical kick.
    Neither the caller checkpoint nor a whole terrain route is assumed proved.
    The wall coordinates below come from both complete generated meshes. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_obj_behaviors_2 jp_obj_behaviors_2.
From LessThanOneAPress.Proofs Require Import GameTypes Area2GoombaApproach Area2Rank12BContact
  EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module WG := us_obj_behaviors_2.

Definition wgr_jump_body version := match version with
| VersionUS => us_obj_behaviors_2.f_goomba_begin_jump
| VersionJP => jp_obj_behaviors_2.f_goomba_begin_jump end.
Definition wgr_velocity_tail_from_body version :=
  match fn_body (wgr_jump_body version) with
  | Ssequence _ (Ssequence _ tail) => tail | _ => Sskip end.
Definition wgr_cell version temporary index := rank15_raw_float_expression
  version temporary (Econst_int (Int.repr index) tint).
Definition wgr_single bits := Econst_single (Float32.of_bits (Int.repr bits)) tfloat.
Definition wgr_velocity_tail version := Ssequence
  (Ssequence (Sset WG._t'4 rank15_current_object_expression)
    (Sassign (wgr_cell version WG._t'4 12) (wgr_single 0)))
  (Ssequence (Sset WG._t'1 rank15_current_object_expression)
    (Ssequence (Sset WG._t'2 rank15_current_object_expression)
      (Ssequence (Sset WG._t'3 (wgr_cell version WG._t'2 28))
        (Sassign (wgr_cell version WG._t'1 10)
          (Ebinop Omul (Ebinop Odiv (wgr_single 1112014848)
            (wgr_single 1077936128) tfloat) (Etempvar WG._t'3 tfloat) tfloat))))).
Theorem wgr_velocity_tail_is_generated : forall version,
  wgr_velocity_tail_from_body version = wgr_velocity_tail version.
Proof. intros []; reflexivity. Qed.

Definition wgr_scale := Float32.of_bits (Int.repr 1069547520).
Definition wgr_kick := Float32.mul
  (Float32.div (Float32.of_bits (Int.repr 1112014848))
    (Float32.of_bits (Int.repr 1077936128))) wgr_scale.
Lemma wgr_kick_is_25 : wgr_kick = Float32.of_bits (Int.repr 1103626240).
Proof. rewrite <- (Float32.of_to_bits wgr_kick). vm_compute; reflexivity. Qed.
Definition wgr_offset oo index :=
  Ptrofs.unsigned (rank15_raw_address oo (Int.repr index)).
Definition wgr_outside (ob : block) oo index chunk (b : block) ofs :=
  b <> ob \/ ofs + size_chunk chunk <= wgr_offset oo index \/
    wgr_offset oo index + 4 <= ofs.
Definition wgr_locals le object :=
  PTree.set WG._t'3 (Vsingle wgr_scale) (PTree.set WG._t'2 object
    (PTree.set WG._t'1 object (PTree.set WG._t'4 object le))).

(** Explicit ordinary storage conditions; no promise about intervening calls.
    This tail contains no calls. Its final frame covers position, action and
    all other cells outside the two velocity destinations. *)
Definition WesternGoombaJumpVelocityExecution : Prop :=
  forall version e le m cb ob oo,
  e ! WG._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    WG._gCurrentObject = Some cb ->
  Mem.load Mptr m cb 0 = Some (Vptr ob oo) -> cb <> ob ->
  Mem.load Mfloat32 m ob (wgr_offset oo 28) = Some (Vsingle wgr_scale) ->
  Mem.valid_access m Mfloat32 ob (wgr_offset oo 12) Writable ->
  Mem.valid_access m Mfloat32 ob (wgr_offset oo 10) Writable ->
  wgr_offset oo 10 + 4 <= wgr_offset oo 12 ->
  wgr_offset oo 12 + 4 <= wgr_offset oo 28 ->
  exists after,
    ClightBigstep.Clight2.exec_stmt
      (Clight.globalenv (selected_clight_target version)) e le m
      (wgr_velocity_tail_from_body version) E0 (wgr_locals le (Vptr ob oo))
      after Out_normal /\
    Mem.load Mfloat32 after ob (wgr_offset oo 12) =
      Some (Vsingle (Float32.of_bits Int.zero)) /\
    Mem.load Mfloat32 after ob (wgr_offset oo 10) =
      Some (Vsingle (Float32.of_bits (Int.repr 1103626240))) /\
    (forall chunk b ofs,
      wgr_outside ob oo 12 chunk b ofs -> wgr_outside ob oo 10 chunk b ofs ->
      Mem.load chunk after b ofs = Mem.load chunk m b ofs).

Theorem wgr_random_jump_resets_forward_speed : WesternGoombaJumpVelocityExecution.
Proof.
  intros version e le m cb ob oo Hlocal Hsymbol Hcurrent Hsep Hscale
    Hforward Hvertical H10 H28.
  destruct (Mem.valid_access_store m Mfloat32 ob (wgr_offset oo 12)
    (Vsingle (Float32.of_bits Int.zero)) Hforward) as [middle Sforward].
  assert (Vvertical : Mem.valid_access middle Mfloat32 ob (wgr_offset oo 10) Writable).
  { eapply Mem.store_valid_access_1; eauto. }
  destruct (Mem.valid_access_store middle Mfloat32 ob (wgr_offset oo 10)
    (Vsingle wgr_kick) Vvertical) as [after Svertical].
  assert (Cmiddle : Mem.load Mptr middle cb 0 = Some (Vptr ob oo)).
  { erewrite Mem.load_store_other; [exact Hcurrent|exact Sforward|left; exact Hsep]. }
  assert (Smiddle : Mem.load Mfloat32 middle ob (wgr_offset oo 28) = Some (Vsingle wgr_scale)).
  { erewrite Mem.load_store_other; [exact Hscale|exact Sforward|right; right; exact H28]. }
  exists after. split.
  - rewrite wgr_velocity_tail_is_generated. unfold wgr_velocity_tail, wgr_locals,
      wgr_cell, wgr_single.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply rank15_current_object_read; eauto.
      * eapply exec_Sassign with (loc := ob)
          (ofs := rank15_raw_address oo (Int.repr 12)) (bf := Full)
          (v := Vsingle (Float32.of_bits Int.zero))
          (v2 := Vsingle (Float32.of_bits Int.zero)).
        -- eapply rank15_raw_float_lvalue; [apply PTree.gss|constructor|reflexivity].
        -- constructor.
        -- reflexivity.
        -- eapply assign_loc_value with (chunk := Mfloat32); [reflexivity|exact Sforward].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply rank15_current_object_read; eauto.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_Sset. eapply rank15_current_object_read; eauto.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_Sset. eapply rank15_raw_float_read;
                [apply PTree.gss|constructor|reflexivity|exact Smiddle].
           ++ eapply exec_Sassign with (loc := ob)
                (ofs := rank15_raw_address oo (Int.repr 10)) (bf := Full)
                (v := Vsingle wgr_kick) (v2 := Vsingle wgr_kick).
              ** eapply rank15_raw_float_lvalue.
                 --- repeat rewrite PTree.gso by discriminate. apply PTree.gss.
                 --- constructor.
                 --- reflexivity.
              ** eapply eval_Ebinop.
                 --- eapply eval_Ebinop; [constructor|constructor|reflexivity].
                 --- apply eval_Etempvar. apply PTree.gss.
                 --- reflexivity.
              ** reflexivity.
              ** eapply assign_loc_value with (chunk := Mfloat32);
                   [reflexivity|exact Svertical].
  - split.
    + erewrite Mem.load_store_other.
      * exact (Mem.load_store_same _ _ _ _ _ _ Sforward).
      * exact Svertical.
      * right; right; exact H10.
    + split.
      * rewrite <- wgr_kick_is_25. exact (Mem.load_store_same _ _ _ _ _ _ Svertical).
      * intros chunk b ofs Fforward Fvertical.
        erewrite Mem.load_store_other; [|exact Svertical|exact Fvertical].
        erewrite Mem.load_store_other; [reflexivity|exact Sforward|exact Fforward].
Qed.

(** The formerly floor-only outline crosses these real vertical faces before
    reaching its 72..113 slope. This checks geometry, not a live wall list. *)
Definition WesternGoombaRimWallGeometry : Prop := forall version,
  nth_error (rank12b_faces version) 336 = Some (336%nat,
    Some ((-3112,72,2970),(-3112,72,1434),(-3112,0,1434))) /\
  nth_error (rank12b_faces version) 337 = Some (337%nat,
    Some ((-3112,72,2970),(-3112,0,1434),(-3112,0,2970))) /\
  -3112 - 40 = -3152 /\ -3071 - (-3152) = 81.
Theorem wgr_rim_wall_geometry_checked : WesternGoombaRimWallGeometry.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Definition Area2WesternGoombaRngBoundary : Prop :=
  WesternGoombaJumpVelocityExecution /\ WesternGoombaRimWallGeometry.
Theorem wgr_rng_boundary_checked : Area2WesternGoombaRngBoundary.
Proof. split; [exact wgr_random_jump_resets_forward_speed|exact wgr_rim_wall_geometry_checked]. Qed.
