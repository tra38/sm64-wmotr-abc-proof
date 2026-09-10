(** Same-memory continuation from the reached button call through joystick
    processing to geometry. Actual completed calls are execution evidence,
    not assumed frames. No later scheduler or controller history is granted. *)
From Coq Require Import Bool List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes ClightRefinement InputSemantics EntryMemory
  InkBackwardSource InkActionPassHistory InkInputSharedConstruction InkMarioInputReset
  InkControllerSource InkControllerBackward InkMarioInputFlag InkButtonTailFrame
  InkInputContinuationSource InkJoystickFrame InkScheduledSharedHistory InkSharedReadings
  InkBackwardExecution Area2Rank12BContact InkAcceptedInitialStorage
  DefaultArea1StartBoundary OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iig_call kind := Scall None
  (Evar (iis_ident kind) (Tfunction [tptr (Tstruct IBM._MarioState noattr)] tvoid cc_default))
  [Etempvar IBM._m (tptr (Tstruct IBM._MarioState noattr))].
Definition iig_after_joystick version := match imr_after_buttons version with
| Ssequence _ rest => rest | _ => Sskip end.
Definition iig_after_geometry version := match iig_after_joystick version with
| Ssequence _ rest => rest | _ => Sskip end.
Definition iig_joystick_cont version ready k := Kcall None (ics_body version ICInputs)
  empty_env ready (Kseq (iig_after_joystick version) k).
Definition iig_geometry_cont version ready k := Kcall None (ics_body version ICInputs)
  empty_env ready (Kseq (iig_after_geometry version) k).
Definition iig_geometry_ready version mb := PTree.set IBM._m (Vptr mb Ptrofs.zero)
  (create_undef_temps (fn_temps (iis_body version IIGeometry))).
Definition iig_first_wall version := ibk_head (fn_body (iis_body version IIGeometry)).
Definition iig_after_first_wall version := rank12b_drop_sequences 1 (fn_body (iis_body version IIGeometry)).
Definition iig_pos_component n := Ebinop Oadd
  (ics_field IBM._m IBM._MarioState IBM._pos (tarray tfloat 3))
  (Econst_int (Int.repr n) tint) (tptr tfloat).

Lemma iig_first_wall_source : forall version,
  fn_body (iis_body version IIGeometry) =
    Ssequence (iig_first_wall version) (iig_after_first_wall version) /\
  iig_first_wall version = Scall None
    (Evar IBM._f32_find_wall_collision
      (Tfunction [tptr tfloat; tptr tfloat; tptr tfloat; tfloat; tfloat] tint cc_default))
    [iig_pos_component 0; iig_pos_component 1; iig_pos_component 2;
     Econst_single (Float32.of_bits (Int.repr 1114636288)) tfloat;
     Econst_single (Float32.of_bits (Int.repr 1112014848)) tfloat].
Proof. intros []; split; reflexivity. Qed.

Lemma iig_geometry_enters_first_wall_statement : forall version m mb k,
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (iis_body version IIGeometry)) [Vptr mb Ptrofs.zero] k m) E0
    (State (iis_body version IIGeometry) (iig_first_wall version)
      (Kseq (iig_after_first_wall version) k) empty_env (iig_geometry_ready version mb) m).
Proof.
  intros version m mb k.
  eapply star_left.
  - apply step_internal_function. constructor; destruct version;
      try reflexivity; try apply alloc_variables_nil;
      try (repeat constructor; cbn; tauto); vm_compute; intuition congruence.
  - rewrite (proj1 (iig_first_wall_source version)). apply star_one. apply step_seq.
  - reflexivity.
Qed.

Lemma iig_actual_input_order : forall version,
  imr_after_buttons version = Ssequence (iig_call IIJoystick) (iig_after_joystick version) /\
  iig_after_joystick version = Ssequence (iig_call IIGeometry) (iig_after_geometry version).
Proof. intros []; split; reflexivity. Qed.

Lemma iig_named_call_step : forall version kind m ready mb k,
  kind = IIJoystick \/ kind = IIGeometry ->
  ready ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (ics_body version ICInputs) (iig_call kind) k empty_env ready m) E0
    (Callstate (Internal (iis_body version kind)) [Vptr mb Ptrofs.zero]
      (Kcall None (ics_body version ICInputs) empty_env ready k) m).
Proof.
  intros version kind m ready mb k Hkind Hm.
  destruct (iis_selected_helpers_resolve version kind) as (fb & Hsymbol & Hfunction).
  unfold iig_call. eapply step_call with (vf := Vptr fb Ptrofs.zero).
  - reflexivity.
  - eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
    + apply eval_Evar_global; [reflexivity|exact Hsymbol].
    + apply deref_loc_reference. reflexivity.
  - econstructor; [apply eval_Etempvar; exact Hm|reflexivity|constructor].
  - exact Hfunction.
  - destruct version; destruct Hkind as [->| ->]; reflexivity.
Qed.

Lemma iig_return_then_next_call : forall version previous next rest m after result t ready mb k,
  next = IIJoystick \/ next = IIGeometry ->
  ready ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal previous) [Vptr mb Ptrofs.zero] t after result ->
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal previous) [Vptr mb Ptrofs.zero]
      (Kcall None (ics_body version ICInputs) empty_env ready (Kseq (Ssequence (iig_call next) rest) k)) m) t
    (Callstate (Internal (iis_body version next)) [Vptr mb Ptrofs.zero]
      (Kcall None (ics_body version ICInputs) empty_env ready (Kseq rest k)) after).
Proof.
  intros version previous next rest m after result t ready mb k Hnext Hm Hcall.
  eapply star_trans.
  - eapply (ClightBigstep.eval_funcall_steps Clight.function_entry2 (selected_clight_target version)).
    + exact Hcall.
    + simpl. auto.
  - eapply star_left; [apply step_returnstate| |reflexivity].
    eapply star_left; [apply step_skip_seq| |reflexivity].
    eapply star_left; [apply step_seq| |reflexivity].
    apply star_one. apply iig_named_call_step; assumption.
  - change (t = t ++ []). rewrite app_nil_r. reflexivity.
Qed.

Theorem iig_buttons_then_joystick_same_steps :
  forall version m middle after mb ready k bt br jt jr,
  ready ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ics_body version ICButtons)) [Vptr mb Ptrofs.zero] bt middle br ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    middle (Internal (iis_body version IIJoystick)) [Vptr mb Ptrofs.zero] jt after jr ->
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (ics_body version ICButtons)) [Vptr mb Ptrofs.zero]
      (iih_button_cont version ready k) m) (bt ++ jt)
    (Callstate (Internal (iis_body version IIGeometry)) [Vptr mb Ptrofs.zero]
      (iig_geometry_cont version ready k) after).
Proof.
  intros version m middle after mb ready k bt br jt jr Hm Hb Hj.
  eapply star_trans with (s2 := Callstate (Internal (iis_body version IIJoystick))
    [Vptr mb Ptrofs.zero] (iig_joystick_cont version ready k) middle).
  - unfold iih_button_cont, iig_joystick_cont. rewrite (proj1 (iig_actual_input_order version)).
    eapply iig_return_then_next_call; [left; reflexivity|exact Hm|exact Hb].
  - unfold iig_joystick_cont, iig_geometry_cont. rewrite (proj2 (iig_actual_input_order version)).
    eapply iig_return_then_next_call; [right; reflexivity|exact Hm|exact Hj].
  - reflexivity.
Qed.

Lemma iig_mask_two_clear_bit : forall flags,
  Int.and flags (Int.repr 2) = Int.zero -> Int.testbit flags 1 = false.
Proof.
  intros flags Hmask.
  pose proof (f_equal (fun word => Int.testbit word 1) Hmask) as Hbit.
  change (Int.testbit (Int.and flags (Int.repr 2)) 1 = Int.testbit Int.zero 1) in Hbit.
  rewrite Int.bits_and in Hbit by (change (0 <= 1 < 32); lia).
  change (andb (Int.testbit flags 1) true = false) in Hbit.
  rewrite andb_true_r in Hbit. exact Hbit.
Qed.

(** Both calls are from one consecutive piece of game execution. This
    classification applies to later passes too, once their live input and
    sampled controller facts have been derived rather than re-assumed. *)
Theorem iig_consecutive_calls_keep_negative_depth_inputs :
  forall version m middle after mb cb pressed bt br jt jr,
  Mem.load Mint16unsigned m mb 2 = Some (Vint Int.zero) ->
  Mem.load Mint32 m mb 156 = Some (Vptr cb Ptrofs.zero) ->
  Mem.load Mint16unsigned m cb 18 = Some (Vint pressed) ->
  Int.testbit pressed 15 = false ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ics_body version ICButtons)) [Vptr mb Ptrofs.zero] bt middle br ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    middle (Internal (iis_body version IIJoystick)) [Vptr mb Ptrofs.zero] jt after jr ->
  exists flags, bt = E0 /\ jt = E0 /\ Mem.load Mint16unsigned after mb 2 = Some (Vint flags) /\
    Int.and flags (Int.repr 2) = Int.zero /\
    Mem.load Mfloat32 after mb 192 = Mem.load Mfloat32 m mb 192 /\
    Mem.load Mint32 after mb 12 = Mem.load Mint32 m mb 12 /\
    Mem.load Mint16unsigned after mb 26 = Mem.load Mint16unsigned m mb 26.
Proof.
  intros version m middle after mb cb pressed bt br jt jr Hzero Hcontroller Hpressed Hclear Hb Hj.
  destruct (icb_actual_button_call_no_a version m mb Ptrofs.zero cb Ptrofs.zero pressed bt middle br
    ltac:(change (200 <= 4294967295); lia) Hzero Hcontroller Hpressed Hclear Hb)
    as (button_flags & Hbutton & Hbit & Hbt).
  destruct (ibt_complete_no_edge_button_frame _ _ _ _ _ _ _ _ Hcontroller Hpressed Hclear Hb)
    as (_ & Hbuttonframe).
  destruct (iij_completed_joystick_call_effect _ _ _ _ _ _ _ Hbutton Hj)
    as (flags & Hflags & Hsamebit & Hjt & Hframe).
  exists flags. split; [exact Hbt|]. split; [exact Hjt|]. split; [exact Hflags|]. split.
  - apply (imf_single_bit_mask_clear flags 1); [lia|].
    rewrite Hsamebit. apply iig_mask_two_clear_bit. exact Hbit.
  - assert (forall chunk offset, 42 <= offset \/
      (4 <= offset /\ offset + size_chunk chunk <= 32) ->
      Mem.load chunk after mb offset = Mem.load chunk m mb offset) as Hprotected.
    { intros chunk offset Hrange.
      change (ink_read after (ink_cell chunk mb offset) = ink_read m (ink_cell chunk mb offset)).
      rewrite Hframe.
      - apply (Hbuttonframe chunk offset). unfold ibt_protected.
        destruct Hrange as [Hhigh|[Hlow Hupper]]; [right; right; exact Hhigh|right; left; split; lia].
      - unfold iij_protected. right. cbn [ink_cell ink_cell_offset ink_cell_chunk]. lia. }
    repeat split; apply Hprotected; cbn [size_chunk]; lia.
Qed.

Definition InkInitialInputGeometryHistory : Prop :=
  forall version m world previous current body k,
  DefaultArea1StartBoundary version (selected_clight_target version) m world previous current ->
  InkAcceptedInitialStorage version m (default_area1_entry_addresses world) body ->
  InkAcceptedInitialInputStorage m (default_area1_entry_addresses world) ->
  let a := default_area1_entry_addresses world in
  exists prefix before ready input_k,
    run_program prefix = selected_clight_target version /\
    run_start prefix = Callstate (Internal (iap_body version))
      [object_slot_pointer a (area1_mario_slot a)] k m /\ run_trace prefix = E0 /\
    run_final prefix = Callstate (Internal (ics_body version ICButtons))
      [Vptr (area1_state_storage_block a) Ptrofs.zero] (iih_button_cont version ready input_k) before /\
    forall bt middle br jt after jr,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      before (Internal (ics_body version ICButtons)) [Vptr (area1_state_storage_block a) Ptrofs.zero]
      bt middle br ->
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      middle (Internal (iis_body version IIJoystick)) [Vptr (area1_state_storage_block a) Ptrofs.zero]
      jt after jr ->
    exists run flags,
      run_program run = selected_clight_target version /\ run_start run = run_start prefix /\
      run_trace run = E0 /\
      run_final run = State (iis_body version IIGeometry) (iig_first_wall version)
        (Kseq (iig_after_first_wall version) (iig_geometry_cont version ready input_k))
        empty_env (iig_geometry_ready version (area1_state_storage_block a)) after /\
      (exists cut : InkRunCut run, ink_cut_state run cut = run_final prefix /\
        ink_cut_before run cut = E0 /\ ink_cut_after run cut = E0) /\
      Mem.load Mint16unsigned after (area1_state_storage_block a) 2 = Some (Vint flags) /\
      Int.and flags (Int.repr 2) = Int.zero /\
      Mem.load Mfloat32 after (area1_state_storage_block a) 192 = Some (Vsingle positive_f32_zero) /\
      Mem.load Mint32 after (area1_state_storage_block a) 12 = Some (Vint spin_airborne_entry_action) /\
      Mem.load Mint16unsigned after (area1_state_storage_block a) 26 = Some (Vint Int.zero).

Theorem iig_initial_history_connects_buttons_joystick_geometry : InkInitialInputGeometryHistory.
Proof.
  intros version m world previous current body k Hstart Hstorage Hinput. cbn zeta.
  set (a := default_area1_entry_addresses world) in *.
  destruct (iih_accepted_initial_action_reaches_buttons version m world previous current body k
    Hstart Hstorage Hinput)
    as (prefix & before & button_k & Hp & Hs & Ht & Hf & Hframe & Hinitial & Hzero &
      Hcontroller & Hpressed & Hclear & ready & input_k & Hcontext & Hready).
  subst button_k. exists prefix, before, ready, input_k.
  split; [exact Hp|]. split; [exact Hs|]. split; [exact Ht|]. split; [exact Hf|].
  intros bt middle br jt after jr Hb Hj.
  destruct (iig_consecutive_calls_keep_negative_depth_inputs _ _ _ _ _ _ _ _ _ _ _
    Hzero Hcontroller Hpressed Hclear Hb Hj)
    as (flags & Hbt & Hjt & Hflags & Hnoa & Hdepth & Haction & Htimer).
  subst bt jt.
  pose proof (iig_buttons_then_joystick_same_steps version before middle after
    (area1_state_storage_block a) ready input_k E0 br E0 jr Hready Hb Hj) as Hsteps.
  assert (star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (ics_body version ICButtons)) [Vptr (area1_state_storage_block a) Ptrofs.zero]
      (iih_button_cont version ready input_k) before) E0
    (State (iis_body version IIGeometry) (iig_first_wall version)
      (Kseq (iig_after_first_wall version) (iig_geometry_cont version ready input_k))
      empty_env (iig_geometry_ready version (area1_state_storage_block a)) after)) as Hcomplete.
  { eapply star_trans; [exact Hsteps|apply iig_geometry_enters_first_wall_statement|reflexivity]. }
  destruct (ish_append_actual_run _ _ _ _ _ Hp Hf Hcomplete)
    as (joined & Hjp & Hjs & Hjt & Hjf & Hcut).
  exists joined, flags. split; [exact Hjp|]. split; [exact Hjs|].
  split; [rewrite Hjt, Ht; reflexivity|]. split; [exact Hjf|]. split.
  - destruct Hcut as (cut & Hcs & Hct & Hcu). exists cut.
    split; [exact Hcs|]. split; [rewrite Hct; exact Ht|exact Hcu].
  - split; [exact Hflags|]. split; [exact Hnoa|]. split.
    + etransitivity; [exact Hdepth|exact (proj1 Hinitial)].
    + pose proof (default_area1_start_entry_memory _ _ _ _ _ _ Hstart) as Hmemory.
      split.
      * etransitivity; [exact Haction|]. change (ink_read before (ink_cell Mint32 (area1_state_storage_block a) 12) =
          Some (Vint spin_airborne_entry_action)).
        rewrite Hframe; [exact (ordinary_area1_action _ _ _ _ _ _ Hmemory)|].
        cbn [ink_shared_cells In]. auto 20.
      * etransitivity; [exact Htimer|]. change (ink_read before (ink_cell Mint16unsigned (area1_state_storage_block a) 26) =
          Some (Vint Int.zero)).
        rewrite Hframe; [exact (ordinary_area1_action_timer_zero _ _ _ _ _ _ Hmemory)|].
        cbn [ink_shared_cells In]. auto 20.
Qed.
