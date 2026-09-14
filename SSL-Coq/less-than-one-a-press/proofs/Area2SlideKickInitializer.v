(** Rank 10A: carry the generated slide-kick launch through the complete
    airborne initializer call. Incoming vertical speed is not a premise:
    the real store replaces it. This does not prove subsequent flight,
    live support, or controller reachability. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Floats Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import
  Area2SlideKickEnvelope Area2Rank11FallingInitializer Area2Rank11PoleExitSplit
  Area2Rank11BodyResolution Area2Rank11LivePoleExit Area2Rank9ACoinFlight
  GameTypes SelectedClightTarget EyerokRank15LiveMovement
  InkBodyResetFrame InkCopyCaller InkLandingHistoryReturn
  Area2Rank12BContact ContactConsumerExecution ObjectContactNecessity.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ski_action := Int.repr 25168042.
Definition ski_launch := Float32.of_bits (Int.repr 1094713344).
Definition ski_min_forward := Float32.of_bits (Int.repr 1107296256).
Definition ski_velocity := Ederef
  (Ebinop Oadd (rank11_mario_field_expression R11MU._vel (tarray tfloat 3))
    (Econst_int Int.one tint) (tptr tfloat)) tfloat.
Definition ski_forward := rank11_mario_field_expression R11MU._forwardVel tfloat.
Definition ski_raise_forward speed := Float32.cmp Clt speed ski_min_forward.
Definition ski_speed speed := if ski_raise_forward speed then ski_min_forward else speed.
Definition ski_case := Ssequence
  (Sassign ski_velocity (Econst_single ski_launch tfloat))
  (Ssequence
    (Ssequence (Sset R11MU._t'8 ski_forward)
      (Sifthenelse (Ebinop Olt (Etempvar R11MU._t'8 tfloat)
        (Econst_single ski_min_forward tfloat) tint)
        (Sassign ski_forward (Econst_single ski_min_forward tfloat)) Sskip))
    Sbreak).

Lemma ski_case_is_generated : forall version,
  sk_initializer_case version = ski_case /\
  exists rest, seq_of_labeled_statement
    (select_switch (Int.unsigned ski_action) (rank11_airborne_switch_cases version)) =
    Ssequence ski_case rest.
Proof. intros []; (split; [reflexivity|eexists; reflexivity]). Qed.

Lemma ski_field_layout : forall version field offset,
  In (field,offset) [(R11MU._vel,72);(R11MU._forwardVel,84)] ->
  exists description,
    (genv_cenv (Clight.globalenv (selected_clight_target version))) ! R11MU._MarioState = Some description /\
    field_offset (Clight.globalenv (selected_clight_target version)) field
      (co_members description) = Errors.OK (offset,Full).
Proof.
  intros version field offset Hin.
  assert (H : match (rank15_selected_header_environment version) ! R11MU._MarioState with
    | Some d => forallb (fun p => rank11_field_offset_check
        (rank15_selected_header_environment version) (co_members d) (fst p) (snd p))
        [(R11MU._vel,72);(R11MU._forwardVel,84)] = true
    | None => False end) by (destruct version; vm_compute; reflexivity).
  rewrite rank15_selected_header_environment_exact in H.
  destruct ((prog_comp_env (selected_clight_target version)) ! R11MU._MarioState)
    as [description|] eqn:E; [|contradiction].
  exists description. split; [exact E|]. apply rank11_field_offset_check_sound.
  rewrite forallb_forall in H. exact (H (field,offset) Hin).
Qed.

Lemma ski_field_lvalue : forall version environment locals memory mario field ty offset,
  locals ! R11MU._m = Some (Vptr mario Ptrofs.zero) ->
  In (field,offset) [(R11MU._vel,72);(R11MU._forwardVel,84)] ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) environment locals memory
    (rank11_mario_field_expression field ty) mario (Ptrofs.repr offset) Full.
Proof.
  intros version environment locals memory mario field ty offset Hm Hin.
  destruct (ski_field_layout version field offset Hin) as (d & Hd & Hoffset).
  replace (Ptrofs.repr offset) with (Ptrofs.add Ptrofs.zero (Ptrofs.repr offset))
    by (rewrite Ptrofs.add_zero_l; reflexivity).
  unfold rank11_mario_field_expression. eapply eval_Efield_struct with (co := d).
  - eapply eval_Elvalue; [apply eval_Ederef; apply eval_Etempvar; exact Hm|].
    apply deref_loc_copy. reflexivity.
  - reflexivity.
  - exact Hd.
  - exact Hoffset.
Qed.

Lemma ski_forward_read : forall version environment locals memory mario speed,
  locals ! R11MU._m = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mfloat32 memory mario 84 = Some (Vsingle speed) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) environment locals memory
    ski_forward (Vsingle speed).
Proof.
  intros version environment locals memory mario speed Hm Hload.
  eapply eval_Elvalue with (ofs := Ptrofs.repr 84) (bf := Full).
  - apply ski_field_lvalue; [exact Hm|cbn; tauto].
  - eapply deref_loc_value with (chunk := Mfloat32); eauto.
Qed.

Lemma ski_velocity_lvalue : forall version environment locals memory mario,
  locals ! R11MU._m = Some (Vptr mario Ptrofs.zero) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version))
    environment locals memory ski_velocity mario (Ptrofs.repr 76) Full.
Proof.
  intros version environment locals memory mario Hm. unfold ski_velocity.
  apply eval_Ederef. eapply eval_Ebinop.
  - eapply eval_Elvalue.
    + eapply ski_field_lvalue; [exact Hm|cbn; auto].
    + apply deref_loc_reference. reflexivity.
  - constructor.
  - reflexivity.
Qed.

(** The two possible write ranges in this switch case, including the optional
    forward-speed minimum. This frame is proved from its actual stores. *)
Definition SKICaseOutsideStores (mario : block) chunk (b : block) offset : Prop :=
  forall write, In write [76; 84] ->
    b <> mario \/ offset + size_chunk chunk <= write \/ write + 4 <= offset.

Lemma ski_case_executes : forall version environment locals memory mario speed,
  locals ! R11MU._m = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mfloat32 memory mario 84 = Some (Vsingle speed) ->
  Mem.valid_access memory Mfloat32 mario 76 Writable ->
  Mem.valid_access memory Mfloat32 mario 84 Writable ->
  exists after,
    ClightBigstep.Clight2.exec_stmt
      (Clight.globalenv (selected_clight_target version)) environment locals memory
      ski_case E0 (PTree.set R11MU._t'8 (Vsingle speed) locals) after Out_break /\
    Mem.load Mfloat32 after mario 76 = Some (Vsingle ski_launch) /\
    Mem.load Mfloat32 after mario 84 = Some (Vsingle (ski_speed speed)) /\
    (forall chunk b offset, SKICaseOutsideStores mario chunk b offset ->
      Mem.load chunk after b offset = Mem.load chunk memory b offset) /\
    (forall chunk b offset permission, Mem.valid_access memory chunk b offset permission ->
      Mem.valid_access after chunk b offset permission).
Proof.
  intros version environment locals memory mario speed Hm Hspeed Hvaccess Hfaccess.
  destruct (Mem.valid_access_store memory Mfloat32 mario 76 (Vsingle ski_launch) Hvaccess)
    as [launched Hlaunch].
  assert (Hspeed' : Mem.load Mfloat32 launched mario 84 = Some (Vsingle speed)).
  { rewrite <- Hspeed. eapply Mem.load_store_other; [exact Hlaunch|right; right; cbn; lia]. }
  assert (Hlaunch_exec : ClightBigstep.Clight2.exec_stmt
    (Clight.globalenv (selected_clight_target version)) environment locals memory
    (Sassign ski_velocity (Econst_single ski_launch tfloat)) E0 locals launched Out_normal).
  { eapply exec_Sassign with (loc := mario) (ofs := Ptrofs.repr 76)
      (bf := Full) (v2 := Vsingle ski_launch) (v := Vsingle ski_launch).
    - apply ski_velocity_lvalue. exact Hm.
    - constructor.
    - reflexivity.
    - eapply assign_loc_value with (chunk := Mfloat32); [reflexivity|exact Hlaunch]. }
  assert (Hread : ClightBigstep.Clight2.exec_stmt
    (Clight.globalenv (selected_clight_target version)) environment locals launched
    (Sset R11MU._t'8 ski_forward) E0
    (PTree.set R11MU._t'8 (Vsingle speed) locals) launched Out_normal).
  { apply exec_Sset. eapply ski_forward_read; eauto. }
  assert (Htest : eval_expr (Clight.globalenv (selected_clight_target version))
    environment (PTree.set R11MU._t'8 (Vsingle speed) locals) launched
    (Ebinop Olt (Etempvar R11MU._t'8 tfloat)
      (Econst_single ski_min_forward tfloat) tint) (Val.of_bool (ski_raise_forward speed))).
  { eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|constructor|reflexivity]. }
  destruct (ski_raise_forward speed) eqn:Hraise.
  - assert (Hfaccess' : Mem.valid_access launched Mfloat32 mario 84 Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store launched Mfloat32 mario 84 (Vsingle ski_min_forward)
      Hfaccess') as [after Hforward].
    exists after. split.
    + unfold ski_case. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Hlaunch_exec|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|constructor].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Hread|].
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
      * exact Htest.
      * reflexivity.
      * eapply exec_Sassign with (loc := mario) (ofs := Ptrofs.repr 84)
          (bf := Full) (v2 := Vsingle ski_min_forward) (v := Vsingle ski_min_forward).
        -- eapply ski_field_lvalue; [rewrite PTree.gso by discriminate; exact Hm|cbn; tauto].
        -- constructor.
        -- reflexivity.
        -- eapply assign_loc_value with (chunk := Mfloat32); [reflexivity|exact Hforward].
    + split.
      * erewrite Mem.load_store_other; [rewrite (Mem.load_store_same _ _ _ _ _ _ Hlaunch); reflexivity|exact Hforward|right; left; cbn; lia].
      * split.
        -- unfold ski_speed. rewrite Hraise, (Mem.load_store_same _ _ _ _ _ _ Hforward). reflexivity.
        -- split.
           ++ intros chunk b offset Houtside. erewrite Mem.load_store_other;
                [eapply Mem.load_store_other; [exact Hlaunch|apply Houtside; cbn; auto]|exact Hforward|apply Houtside; cbn; auto].
           ++ intros. eapply Mem.store_valid_access_1; [exact Hforward|].
              eapply Mem.store_valid_access_1; eauto.
  - exists launched. split.
    + unfold ski_case. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Hlaunch_exec|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|constructor].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Hread|].
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false); [exact Htest|reflexivity|constructor].
    + split; [rewrite (Mem.load_store_same _ _ _ _ _ _ Hlaunch); reflexivity|].
      split; [unfold ski_speed; rewrite Hraise; exact Hspeed'|]. split.
      * intros chunk b offset Houtside. eapply Mem.load_store_other; [exact Hlaunch|apply Houtside; cbn; auto].
      * intros. eapply Mem.store_valid_access_1; eauto.
Qed.

Lemma ski_tail_executes : forall version environment locals memory mario y flags,
  locals ! R11MU._m = Some (Vptr mario Ptrofs.zero) ->
  locals ! R11MU._action = Some (Vint ski_action) ->
  Mem.load Mfloat32 memory mario 64 = Some (Vsingle y) ->
  Mem.load Mint32 memory mario 4 = Some (Vint flags) ->
  Mem.valid_access memory Mfloat32 mario 188 Writable ->
  Mem.valid_access memory Mint32 mario 4 Writable ->
  exists after,
    ClightBigstep.Clight2.exec_stmt
      (Clight.globalenv (selected_clight_target version)) environment locals memory
      (rank11_airborne_tail version) E0 (rank11_tail_locals locals y flags) after
      (Out_return (Some (Vint ski_action, tuint))) /\
    (forall chunk b offset, Rank11OutsideInitializerStores mario chunk b offset ->
      Mem.load chunk after b offset = Mem.load chunk memory b offset).
Proof.
  intros version environment locals memory mario y flags Hm Ha Hy Hflags Hpa Hfa.
  destruct (Mem.valid_access_store memory Mfloat32 mario 188 (Vsingle y) Hpa)
    as [middle Hpeak].
  assert (Hflags' : Mem.load Mint32 middle mario 4 = Some (Vint flags)).
  { rewrite <- Hflags. eapply Mem.load_store_other; [exact Hpeak|right; left; cbn; lia]. }
  assert (Hfa' : Mem.valid_access middle Mint32 mario 4 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store middle Mint32 mario 4
    (Vint (Int.or flags (Int.repr 256))) Hfa') as [after Hflagstore].
  exists after. split.
  - rewrite rank11_initializer_tail_is_generated.
    unfold rank11_initializer_tail_statement, rank11_tail_locals.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply rank11_mario_y_read; eauto.
      * eapply exec_Sassign with (loc := mario) (ofs := Ptrofs.repr 188)
          (bf := Full) (v2 := Vsingle y) (v := Vsingle y).
        -- eapply rank11_mario_field_lvalue; [rewrite PTree.gso by discriminate; exact Hm|cbn; auto 12].
        -- apply eval_Etempvar. apply PTree.gss.
        -- reflexivity.
        -- eapply assign_loc_value with (chunk := Mfloat32); [reflexivity|exact Hpeak].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_Sset. eapply rank11_mario_field_read with (offset := 4) (chunk := Mint32).
           ++ rewrite PTree.gso by discriminate. exact Hm.
           ++ cbn; auto 12.
           ++ reflexivity.
           ++ reflexivity.
           ++ exact Hflags'.
        -- eapply exec_Sassign with (loc := mario) (ofs := Ptrofs.repr 4)
             (bf := Full) (v2 := Vint (Int.or flags (Int.repr 256)))
             (v := Vint (Int.or flags (Int.repr 256))).
           ++ eapply rank11_mario_field_lvalue; [repeat rewrite PTree.gso by discriminate; exact Hm|cbn; auto 12].
           ++ eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|constructor|reflexivity].
           ++ reflexivity.
           ++ eapply assign_loc_value with (chunk := Mint32); [reflexivity|exact Hflagstore].
      * apply exec_Sreturn_some. apply eval_Etempvar.
        repeat rewrite PTree.gso by discriminate. exact Ha.
  - intros chunk b offset [Hflags_out Hpeak_out].
    erewrite Mem.load_store_other; [eapply Mem.load_store_other; eauto|exact Hflagstore|exact Hflags_out].
Qed.

Definition SKIOutsideStores mario chunk b offset : Prop :=
  SKICaseOutsideStores mario chunk b offset /\
  Rank11OutsideInitializerStores mario chunk b offset.
Definition ski_body_locals locals speed y flags :=
  rank11_tail_locals (PTree.set R11MU._t'8 (Vsingle speed)
    (rank11_zero_depth_prefix_locals locals)) y flags.

Theorem ski_complete_body_establishes_launch :
  forall version environment locals memory mario speed y flags,
  locals ! R11MU._m = Some (Vptr mario Ptrofs.zero) ->
  locals ! R11MU._action = Some (Vint ski_action) ->
  Mem.load Mint8unsigned memory mario 180 = Some (Vint Int.zero) ->
  Mem.load Mfloat32 memory mario 192 = Some (Vsingle Float32.zero) ->
  Mem.load Mfloat32 memory mario 84 = Some (Vsingle speed) ->
  Mem.load Mfloat32 memory mario 64 = Some (Vsingle y) ->
  Mem.load Mint32 memory mario 4 = Some (Vint flags) ->
  Mem.valid_access memory Mfloat32 mario 76 Writable ->
  Mem.valid_access memory Mfloat32 mario 84 Writable ->
  Mem.valid_access memory Mfloat32 mario 188 Writable ->
  Mem.valid_access memory Mint32 mario 4 Writable ->
  exists after,
    ClightBigstep.Clight2.exec_stmt
      (Clight.globalenv (selected_clight_target version)) environment locals memory
      (fn_body (rank11_airborne_body version)) E0
      (ski_body_locals locals speed y flags) after
      (Out_return (Some (Vint ski_action, tuint))) /\
    Mem.load Mfloat32 after mario 76 = Some (Vsingle ski_launch) /\
    Mem.load Mfloat32 after mario 84 = Some (Vsingle (ski_speed speed)) /\
    (forall chunk b offset, SKIOutsideStores mario chunk b offset ->
      Mem.load chunk after b offset = Mem.load chunk memory b offset).
Proof.
  intros version environment locals memory mario speed y flags
    Hm Ha Hsquish Hdepth Hspeed Hy Hflags Hva Hfa Hpa Hflagsa.
  pose proof (rank11_zero_depth_initializer_prefix_executes version environment
    locals memory mario Hm Hsquish Hdepth) as Hprefix.
  assert (Hm' : (rank11_zero_depth_prefix_locals locals) ! R11MU._m = Some (Vptr mario Ptrofs.zero))
    by (unfold rank11_zero_depth_prefix_locals; repeat rewrite PTree.gso by discriminate; exact Hm).
  assert (Ha' : (rank11_zero_depth_prefix_locals locals) ! R11MU._action = Some (Vint ski_action))
    by (unfold rank11_zero_depth_prefix_locals; repeat rewrite PTree.gso by discriminate; exact Ha).
  destruct (ski_case_executes version environment (rank11_zero_depth_prefix_locals locals)
    memory mario speed Hm' Hspeed Hva Hfa) as (launched & Hcase & Hv & Hspeed' & Hframe & Haccess).
  assert (Hy' : Mem.load Mfloat32 launched mario 64 = Some (Vsingle y)).
  { rewrite Hframe; [exact Hy|unfold SKICaseOutsideStores; cbn; intros; intuition subst; cbn; lia]. }
  assert (Hflags' : Mem.load Mint32 launched mario 4 = Some (Vint flags)).
  { rewrite Hframe; [exact Hflags|unfold SKICaseOutsideStores; cbn; intros; intuition subst; cbn; lia]. }
  destruct (ski_tail_executes version environment
    (PTree.set R11MU._t'8 (Vsingle speed) (rank11_zero_depth_prefix_locals locals))
    launched mario y flags ltac:(rewrite PTree.gso by discriminate; exact Hm')
    ltac:(rewrite PTree.gso by discriminate; exact Ha') Hy' Hflags'
    (Haccess _ _ _ _ Hpa) (Haccess _ _ _ _ Hflagsa)) as (after & Htail & Htailframe).
  exists after. split.
  - rewrite rank11_airborne_body_decomposition.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Hprefix|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|exact Htail].
    eapply exec_Sswitch with (v := Vint ski_action) (n := Int.unsigned ski_action) (out := Out_break).
    + apply eval_Etempvar. exact Ha'.
    + reflexivity.
    + destruct (ski_case_is_generated version) as [_ [rest Hselect]]. rewrite Hselect.
      eapply exec_Sseq_2; [exact Hcase|discriminate].
  - split.
    + rewrite Htailframe; [exact Hv|unfold Rank11OutsideInitializerStores; cbn; intuition lia].
    + split.
      * rewrite Htailframe; [exact Hspeed'|unfold Rank11OutsideInitializerStores; cbn; intuition lia].
      * intros chunk b offset [Hcase_out Htail_out].
        rewrite Htailframe by exact Htail_out. apply Hframe. exact Hcase_out.
Qed.

Definition ski_entry_locals version mario arg : temp_env :=
  PTree.set R11MU._actionArg (Vint arg)
    (PTree.set R11MU._action (Vint ski_action)
      (PTree.set R11MU._m (Vptr mario Ptrofs.zero)
        (create_undef_temps (fn_temps (rank11_airborne_body version))))).
Lemma ski_real_function_entry : forall version mario arg memory,
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (rank11_airborne_body version) [Vptr mario Ptrofs.zero; Vint ski_action; Vint arg]
    memory empty_env (ski_entry_locals version mario arg) memory.
Proof.
  intros version mario arg memory. constructor.
  - destruct version; constructor.
  - assert (H : list_norepet [R11MU._m; R11MU._action; R11MU._actionArg]).
    { constructor; [vm_compute; intuition discriminate|].
      constructor; [vm_compute; intuition discriminate|].
      constructor; [cbn; tauto|constructor]. }
    destruct version; exact H.
  - unfold list_disjoint. intros parameter temporary Hp Ht Heq.
    subst temporary. destruct version; vm_compute in Hp, Ht; intuition congruence.
  - destruct version; constructor.
  - destruct version; reflexivity.
Qed.

Definition SlideKickInitializerCallBoundary : Prop :=
  forall version memory mario arg speed y flags,
  Mem.load Mint8unsigned memory mario 180 = Some (Vint Int.zero) ->
  Mem.load Mfloat32 memory mario 192 = Some (Vsingle Float32.zero) ->
  Mem.load Mfloat32 memory mario 84 = Some (Vsingle speed) ->
  Mem.load Mfloat32 memory mario 64 = Some (Vsingle y) ->
  Mem.load Mint32 memory mario 4 = Some (Vint flags) ->
  Mem.valid_access memory Mfloat32 mario 76 Writable ->
  Mem.valid_access memory Mfloat32 mario 84 Writable ->
  Mem.valid_access memory Mfloat32 mario 188 Writable ->
  Mem.valid_access memory Mint32 mario 4 Writable ->
  exists function_block after,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      R11MU._set_mario_action_airborne = Some function_block /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) function_block =
      Some (Internal (rank11_airborne_body version)) /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) memory
      (Internal (rank11_airborne_body version))
      [Vptr mario Ptrofs.zero; Vint ski_action; Vint arg] E0 after (Vint ski_action) /\
    Mem.load Mfloat32 after mario 76 = Some (Vsingle ski_launch) /\
    Mem.load Mfloat32 after mario 84 = Some (Vsingle (ski_speed speed)) /\
    (forall chunk b offset, SKIOutsideStores mario chunk b offset ->
      Mem.load chunk after b offset = Mem.load chunk memory b offset).

Theorem ski_selected_initializer_call_establishes_launch : SlideKickInitializerCallBoundary.
Proof.
  intros version memory mario arg speed y flags Hsquish Hdepth Hspeed Hy Hflags Hva Hfa Hpa Hflagsa.
  destruct (ski_complete_body_establishes_launch version empty_env
    (ski_entry_locals version mario arg) memory mario speed y flags
    ltac:(unfold ski_entry_locals; rank11_temp)
    ltac:(unfold ski_entry_locals; rank11_temp)
    Hsquish Hdepth Hspeed Hy Hflags Hva Hfa Hpa Hflagsa)
    as (after & Hbody & Hv & Hspeed' & Hframe).
  destruct (rank11_selected_native_body_resolves version R11AirborneInitializer)
    as (b & Hsymbol & Hfunction).
  exists b, after. split; [exact Hsymbol|]. split; [exact Hfunction|]. split.
  - eapply eval_funcall_internal.
    + apply ski_real_function_entry.
    + exact Hbody.
    + assert (Hr : fn_return (rank11_airborne_body version) = tuint)
        by (destruct version; reflexivity).
      rewrite Hr. split; [discriminate|reflexivity].
    + reflexivity.
  - auto.
Qed.

(** Position, selected support and horizontal velocity are among the framed
    cells. A separate later event must create any newly useful floor gap. *)
Lemma ski_launch_does_not_move_or_change_support : forall mario before after,
  (forall chunk b offset, SKIOutsideStores mario chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk before b offset) ->
  (forall offset, In offset [60;64;68;72;80;112] ->
    Mem.load Mfloat32 after mario offset = Mem.load Mfloat32 before mario offset) /\
  Mem.load Mint32 after mario 104 = Mem.load Mint32 before mario 104.
Proof.
  intros mario before after Hframe. split.
  - intros offset Hin. apply Hframe. unfold SKIOutsideStores, SKICaseOutsideStores,
      Rank11OutsideInitializerStores. cbn in Hin.
    repeat destruct Hin as [Hin|Hin]; try contradiction; subst offset.
    all: split.
    all: try (intros write Hwrite; cbn in Hwrite;
      destruct Hwrite as [Hwrite|[Hwrite|[]]]; subst write).
    all: cbn; intuition lia.
  - apply Hframe. unfold SKIOutsideStores, SKICaseOutsideStores, Rank11OutsideInitializerStores.
    split.
    + intros write Hwrite. cbn in Hwrite.
      destruct Hwrite as [Hwrite|[Hwrite|[]]]; subst write; cbn; intuition lia.
    + cbn; intuition lia.
Qed.

Lemma ski_launch_is_not_a_hard_fall_or_rebound :
  ski_launch = sk_float8 (sk_velocity8 sk_normal_start) /\
  ski_launch <> rank9cf_integer (-75) /\ ski_launch <> sk_float8 300.
Proof.
  split.
  - rewrite <- (Float32.of_to_bits ski_launch),
      <- (Float32.of_to_bits (sk_float8 (sk_velocity8 sk_normal_start))).
    f_equal; vm_compute; reflexivity.
  - split; intro H; apply (f_equal Float32.to_bits) in H; vm_compute in H; discriminate.
Qed.

(** The caller's actual post-initializer suffix cannot overwrite this launch
    or move Mario: all its writes are proved to lie in the control fields.
    No harmless-outside-call hypothesis is used. *)
Inductive SKIMetadata := SKIFlags | SKIPrevious | SKIAction | SKIArgument | SKIState | SKITimer.
Definition ski_meta_field k := match k with
| SKIFlags => R11MU._flags | SKIPrevious => R11MU._prevAction
| SKIAction => R11MU._action | SKIArgument => R11MU._actionArg
| SKIState => R11MU._actionState | SKITimer => R11MU._actionTimer end.
Definition ski_meta_type k := match k with SKIState | SKITimer => tushort | _ => tuint end.
Definition ski_meta_chunk k := match k with SKIState | SKITimer => Mint16unsigned | _ => Mint32 end.
Definition ski_meta_offset k : Z := match k with
| SKIFlags => 4 | SKIPrevious => 16 | SKIAction => 12 | SKIArgument => 28
| SKIState => 24 | SKITimer => 26 end.
Lemma ski_meta_layout : forall version k,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    R11MU._MarioState (ski_meta_field k) (ski_meta_offset k) = true /\
  access_mode (ski_meta_type k) = By_value (ski_meta_chunk k).
Proof.
  intros version k. split; [|destruct k; reflexivity].
  change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    R11MU._MarioState (ski_meta_field k) (ski_meta_offset k) = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version, k; vm_compute; reflexivity.
Qed.

Definition ski_setter_tail version := rank12b_drop_sequences 1
  (fn_body (ilh_set_action_body version)).
Inductive ski_tail_statement : statement -> Prop :=
| ski_tail_readonly : forall s, cce_readonly_keep R11MU._m s = true -> ski_tail_statement s
| ski_tail_write : forall k rhs, ski_tail_statement
    (Sassign (rank11_mario_field_expression (ski_meta_field k) (ski_meta_type k)) rhs)
| ski_tail_seq : forall first rest, ski_tail_statement first -> ski_tail_statement rest ->
    ski_tail_statement (Ssequence first rest)
| ski_tail_if : forall cond yes no, ski_tail_statement yes -> ski_tail_statement no ->
    ski_tail_statement (Sifthenelse cond yes no).
Lemma ski_setter_tail_is_classified : forall version, ski_tail_statement (ski_setter_tail version).
Proof.
  intros []; cbn [ski_setter_tail rank12b_drop_sequences ilh_set_action_body fn_body].
  all: repeat first [apply ski_tail_readonly; reflexivity
    |apply (ski_tail_write SKIFlags) |apply (ski_tail_write SKIPrevious)
    |apply (ski_tail_write SKIAction) |apply (ski_tail_write SKIArgument)
    |apply (ski_tail_write SKIState) |apply (ski_tail_write SKITimer)
    |apply ski_tail_seq |apply ski_tail_if].
Qed.

Definition ski_after_control (mario : block) chunk (b : block) offset :=
  b <> mario \/ offset + size_chunk chunk <= 4 \/ 32 <= offset.
Lemma ski_tail_statement_frames : forall s, ski_tail_statement s ->
  forall version le memory mario trace last after out,
  le ! R11MU._m = Some (Vptr mario Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le memory s trace last after out ->
  last ! R11MU._m = le ! R11MU._m /\
  (forall chunk b offset, ski_after_control mario chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk memory b offset).
Proof.
  intros s Hshape. induction Hshape; intros version le memory mario trace last after out Hm Hrun.
  - destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun H) as (-> & -> & Htemp).
    split; [exact Htemp|intros; reflexivity].
  - destruct (ski_meta_layout version k) as [Hlayout Hmode].
    destruct (ibr_field_assignment_store _ empty_env le memory R11MU._m R11MU._MarioState
      (ski_meta_field k) (ski_meta_type k) (ski_meta_offset k) (ski_meta_chunk k) rhs
      trace last after out mario Ptrofs.zero Hm Hlayout Hmode Hrun)
      as (-> & -> & -> & value & Hstore).
    assert (Hoffset : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero
      (Ptrofs.repr (ski_meta_offset k))) = ski_meta_offset k)
      by (destruct k; reflexivity).
    rewrite Hoffset in Hstore.
    split; [reflexivity|]. intros chunk b offset Houtside.
    eapply Mem.load_store_other; [exact Hstore|].
    unfold ski_after_control in Houtside. destruct k; cbn; intuition lia.
  - inversion Hrun; subst.
    + match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ first _ _ _ _,
        Hrest : ClightBigstep.exec_stmt _ _ _ _ _ rest _ _ _ _ |- _ =>
        destruct (IHHshape1 _ _ _ _ _ _ _ _ Hm Hfirst) as [Htemp1 Hframe1];
        destruct (IHHshape2 _ _ _ _ _ _ _ _ (eq_trans Htemp1 Hm) Hrest) as [Htemp2 Hframe2] end.
      split; [congruence|]. intros chunk rb offset Houtside.
      rewrite Hframe2, Hframe1; auto.
    + eapply IHHshape1; eauto.
  - inversion Hrun; subst. destruct b; [eapply IHHshape1|eapply IHHshape2]; eauto.
Qed.

Definition SlideKickSetterTailBoundary : Prop :=
  forall version le before mario trace last after out,
  le ! R11MU._m = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mfloat32 before mario 76 = Some (Vsingle ski_launch) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le before
    (ski_setter_tail version) trace last after out ->
  Mem.load Mfloat32 after mario 76 = Some (Vsingle ski_launch) /\
  (forall chunk b offset, ski_after_control mario chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk before b offset).
Theorem ski_actual_setter_tail_preserves_launch : SlideKickSetterTailBoundary.
Proof.
  intros version le before mario trace last after out Hm Hv Hrun.
  destruct (ski_tail_statement_frames _ (ski_setter_tail_is_classified version)
    _ _ _ _ _ _ _ _ Hm Hrun) as [_ Hframe]. split; [|exact Hframe].
  rewrite Hframe; [exact Hv|unfold ski_after_control; right; right; lia].
Qed.

Definition SlideKickLaunchBoundary : Prop :=
  SlideKickInitializerCallBoundary /\ SlideKickSetterTailBoundary /\
  ski_launch = sk_float8 (sk_velocity8 sk_normal_start) /\
  ski_launch <> rank9cf_integer (-75) /\ ski_launch <> sk_float8 300.
Theorem ski_launch_boundary_checked : SlideKickLaunchBoundary.
Proof.
  split; [exact ski_selected_initializer_call_establishes_launch|].
  split; [exact ski_actual_setter_tail_preserves_launch|].
  exact ski_launch_is_not_a_hard_fall_or_rebound.
Qed.
