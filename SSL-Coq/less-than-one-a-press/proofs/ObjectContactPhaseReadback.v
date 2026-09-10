(** Replace the old six-temporary contact readback with actual Object loads.
    X/Y/Z, radii and bottom offsets are read before sqrtf; heights afterwards.
    Thus general successful overlap still needs precisely the two height-load
    frames in addition to sqrtf's numeric result. No wider frame is assumed. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes CollisionRegions
  Area2Rank12BContact ObjectContactNecessity ObjectContactReadback
  EyerokRank15LiveMovement InkCopyCaller SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ocp_height_read memory block offset := Mem.load Mfloat32 memory block
  (Ptrofs.unsigned (Ptrofs.add offset (Ptrofs.repr 508))).

Definition ocp_sqrt_height_frame version memory argument ab ao bb bo : Prop :=
  forall function_block fd trace after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    RC._sqrtf = Some function_block ->
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
    function_block = Some fd ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) memory fd
    [Vsingle argument] trace after result ->
  ocp_height_read after ab ao = ocp_height_read memory ab ao /\
  ocp_height_read after bb bo = ocp_height_read memory bb bo.

Lemma ocp_selected_height : forall version,
  ibcc_field_ok (prog_comp_env (selected_clight_target version))
    RC._Object RC._hitboxHeight 508 = true.
Proof.
  intro version. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Definition ocp_height_prefix version :=
  ocn_prepend (ocn_before_vertical version) Sskip.
Definition ocp_height_locals le ap ah bp bh value :=
  PTree.set RC._sp1C (Vsingle (hitbox_top bp bh))
  (PTree.set RC._t'12 (Vsingle (hitbox_height bh))
  (PTree.set RC._sp20 (Vsingle (hitbox_top ap ah))
  (PTree.set RC._t'13 (Vsingle (hitbox_height ah))
    (ocr_distance_locals le ap ah bp bh value)))).

Lemma ocp_height_prefix_is_readonly : forall version,
  ocr_readonly_prefix (ocp_height_prefix version) = true.
Proof. intros []; reflexivity. Qed.

Lemma ocp_height_prefix_executes :
  forall version e le memory ab ao ap ah bb bo bp bh value,
  le ! RC._a = Some (Vptr ab ao) -> le ! RC._b = Some (Vptr bb bo) ->
  ocp_height_read memory ab ao = Some (Vsingle (hitbox_height ah)) ->
  ocp_height_read memory bb bo = Some (Vsingle (hitbox_height bh)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e
    (ocr_distance_locals le ap ah bp bh value) memory (ocp_height_prefix version)
    E0 (ocp_height_locals le ap ah bp bh value) memory Out_normal.
Proof.
  intros version e le memory ab ao ap ah bb bo bp bh value Ha Hb Hah Hbh.
  pose proof (ocp_selected_height version) as Hfield.
  replace (ocp_height_prefix version) with
    (ocn_prepend
      [Ssequence (Sset RC._t'13 (ocr_field RC._a RC._hitboxHeight))
        (Sset RC._sp20 (Ebinop Oadd (Etempvar RC._t'13 tfloat) (Etempvar RC._sp3C tfloat) tfloat));
       Ssequence (Sset RC._t'12 (ocr_field RC._b RC._hitboxHeight))
        (Sset RC._sp1C (Ebinop Oadd (Etempvar RC._t'12 tfloat) (Etempvar RC._sp38 tfloat) tfloat))]
      Sskip) by (destruct version; reflexivity).
  unfold ocn_prepend, ocp_height_locals, ocr_distance_locals, ocr_input_locals, hitbox_top.
  repeat first
    [ apply exec_Sskip
    | eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    | apply exec_Sset
    | eapply ocr_field_read; [exact Hfield|repeat (rewrite PTree.gso by discriminate); eassumption|eassumption]
    | eapply eval_Ebinop; [apply eval_Etempvar; rank15_temporary|apply eval_Etempvar; rank15_temporary|reflexivity] ].
Qed.

Lemma ocp_six_samples_are_derived : forall le phase,
  let ap := collision_mario_position phase in
  let ah := collision_mario_hitbox phase in
  let bp := collision_target_position phase in
  let bh := collision_target_hitbox phase in
  let value := Vsingle (horizontal_distance ap bp) in
  ocn_samples_match_phase phase (ocr_distance_locals le ap ah bp bh value)
    (ocp_height_locals le ap ah bp bh value).
Proof.
  intros. unfold ocn_samples_match_phase, ocp_height_locals,
    ocr_distance_locals, ocr_input_locals. repeat split; rank15_temporary.
Qed.

(** Every checkpoint used here is a subexecution of Hrun. In particular,
    a different hypothetical sqrtf execution cannot supply the height frame. *)
Theorem ocp_successful_body_overlap_from_memory :
  forall version e le memory ab ao bb bo trace final_locals final_memory phase,
  ocr_sqrt_numeric_effect version memory
    (ocr_squared_distance (collision_mario_position phase) (collision_target_position phase)) ->
  ocp_sqrt_height_frame version memory
    (ocr_squared_distance (collision_mario_position phase) (collision_target_position phase)) ab ao bb bo ->
  e ! RC._sqrtf = None ->
  le ! RC._a = Some (Vptr ab ao) -> le ! RC._b = Some (Vptr bb bo) ->
  ocr_object_inputs memory ab ao (collision_mario_position phase) (collision_mario_hitbox phase) ->
  ocr_object_inputs memory bb bo (collision_target_position phase) (collision_target_hitbox phase) ->
  ocp_height_read memory ab ao = Some (Vsingle (hitbox_height (collision_mario_hitbox phase))) ->
  ocp_height_read memory bb bo = Some (Vsingle (hitbox_height (collision_target_hitbox phase))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le memory
    (fn_body (rank12b_body version)) trace final_locals final_memory
    (Out_return (Some (Vint Int.one, tint))) ->
  hitboxes_overlap (collision_mario_position phase) (collision_mario_hitbox phase)
    (collision_target_position phase) (collision_target_hitbox phase) = true.
Proof.
  intros version e le memory ab ao bb bo trace final_locals final_memory phase
    Hsqrt Hframe Hlocal Ha Hb Hain Hbin Hah Hbh Hrun.
  destruct (ocr_body_has_same_run_distance_cut version e le memory ab ao
    (collision_mario_position phase) (collision_mario_hitbox phase) bb bo
    (collision_target_position phase) (collision_target_hitbox phase)
    trace final_locals final_memory _ Hlocal Ha Hb Hain Hbin Hrun)
    as (function_block & fd & value & ct & cm & st & Htrace & Hsymbol & Hfunction & Htype & Hcall & Hsuffix).
  assert (value = Vsingle (horizontal_distance
    (collision_mario_position phase) (collision_target_position phase))) as Hvalue
    by (exact (Hsqrt _ _ _ _ _ Hsymbol Hfunction Hcall)).
  destruct (Hframe _ _ _ _ _ Hsymbol Hfunction Hcall) as [Haf Hbf].
  subst value.
  destruct (ocn_successful_radius_tail _ _ _ _ _ _ _ _ Hsuffix) as [Hr Hinside].
  destruct (ocn_generated_contact_checkpoints version)
    as (_ & _ & Hinside_shape & Hnormal & Hvertical).
  rewrite Hinside_shape in Hinside.
  destruct (ocn_successful_prefix_decomposition _ _ _ _ _ _ _ _ _ _ Hnormal Hinside)
    as (vl & vm & ht & rt & Hrest & Hheight & Hguards).
  pose proof (ocp_height_prefix_executes version e le cm ab ao
    (collision_mario_position phase) (collision_mario_hitbox phase) bb bo
    (collision_target_position phase) (collision_target_hitbox phase)
    (Vsingle (horizontal_distance (collision_mario_position phase) (collision_target_position phase)))
    Ha Hb ltac:(rewrite Haf; exact Hah) ltac:(rewrite Hbf; exact Hbh)) as Hconstructed.
  destruct (ocr_readonly_unique _ _ _ _ _ _ _ _ _ Hheight
    (ocp_height_prefix_is_readonly version) _ _ _ _ Hconstructed)
    as (? & ? & ? & _). subst ht vl vm.
  rewrite Hvertical in Hguards.
  destruct (ocn_rejecting_guard_must_pass _ _ _ _ _ _ _ _ _ Hguards) as [Habove Hnext].
  destruct (ocn_rejecting_guard_must_pass _ _ _ _ _ _ _ _ _ Hnext) as [Hbelow _].
  eapply ocn_actual_tests_imply_reported_overlap;
    [apply ocp_six_samples_are_derived|exact Hr|exact Habove|exact Hbelow].
Qed.

(** This is the exact geometric predicate consumed by the existing star and
    secret accounting. Object roles, counts, registration and scheduler phase
    are still separate premises, not inferred from coordinates alone. *)
Theorem ocp_memory_reads_supply_collection_geometry :
  forall version e le memory ab ao bb bo trace final_locals final_memory phase,
  ocr_sqrt_numeric_effect version memory
    (ocr_squared_distance (collision_mario_position phase) (collision_target_position phase)) ->
  ocp_sqrt_height_frame version memory
    (ocr_squared_distance (collision_mario_position phase) (collision_target_position phase)) ab ao bb bo ->
  e ! RC._sqrtf = None ->
  le ! RC._a = Some (Vptr ab ao) -> le ! RC._b = Some (Vptr bb bo) ->
  ocr_object_inputs memory ab ao (collision_mario_position phase) (collision_mario_hitbox phase) ->
  ocr_object_inputs memory bb bo (collision_target_position phase) (collision_target_hitbox phase) ->
  ocp_height_read memory ab ao = Some (Vsingle (hitbox_height (collision_mario_hitbox phase))) ->
  ocp_height_read memory bb bo = Some (Vsingle (hitbox_height (collision_target_hitbox phase))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le memory
    (fn_body (rank12b_body version)) trace final_locals final_memory
    (Out_return (Some (Vint Int.one, tint))) ->
  ocn_other_phase_facts phase -> collision_phase_overlap phase.
Proof.
  intros version e le memory ab ao bb bo trace final_locals final_memory phase
    Hsqrt Hframe Hlocal Ha Hb Hain Hbin Hah Hbh Hrun Hother.
  pose proof (ocp_successful_body_overlap_from_memory version e le memory ab ao bb bo
    trace final_locals final_memory phase Hsqrt Hframe Hlocal Ha Hb Hain Hbin Hah Hbh Hrun) as Hgeometry.
  destruct Hother as (Hplayer & Harea & Hafter & Hbefore & Hwarp & Hmc & Htc & Hpair).
  unfold collision_phase_overlap.
  exact (conj Hplayer (conj Harea (conj Hafter (conj Hbefore (conj Hwarp
    (conj Hmc (conj Htc (conj Hgeometry Hpair)))))))).
Qed.
