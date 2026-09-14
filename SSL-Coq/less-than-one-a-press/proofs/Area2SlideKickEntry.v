(** Rank 10A: the slide-kick timeout is a genuine route to freefall,
    but it tests BOTH the updated timer and a 500-unit floor gap.

    This module executes the actual generated US/JP decision after the
    timer store. It also checks two vertical episodes with a selected,
    steadily descending elevator base, including the real one-time bounce.
    These are conditional vertical certificates, not live floor-list,
    all-controller-history, or whole-elevator impossibility theorems. *)
From Coq Require Import Bool Lia List ZArith Reals Lra.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_mario_actions_airborne
  jp_mario_actions_airborne us_mario jp_mario us_mario_step jp_mario_step.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts
  Area2Rank10AGroundPound Area2Rank10AEntryChecks Area2Rank9ACoinFlight
  Area2Rank11LivePoleExit Area2Rank12BContact UpperElevatorQueryResolution
  UpperElevatorQuarterStepClosure InkBackwardSource InkBackwardExecution
  InkControllerSource InkControllerEdge InkCopyCaller InkActionPassStart
  InkActionTimerReset ObjectContactNecessity ContactConsumerExecution
  InkLandingExecution
  InkLandingHistoryReturn SecretContactExecution SelectedClightTarget
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.

Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module SK := us_mario_actions_airborne.

Definition ske_body version := match version with
| VersionUS => SK.f_act_slide_kick
| VersionJP => jp_mario_actions_airborne.f_act_slide_kick end.
Definition ske_gate version := ibk_head
  (rank12b_drop_sequences 1 (fn_body (ske_body version))).
Definition ske_increment version := match ske_gate version with
| Ssequence (Ssequence increment _) _ => increment | _ => Sskip end.
Definition ske_test version := match ske_gate version with
| Ssequence (Ssequence _ test) _ => test | _ => Sskip end.
Definition ske_choice version := match ske_gate version with
| Ssequence _ choice => choice | _ => Sskip end.
Definition ske_yes version := match ske_choice version with
| Sifthenelse _ yes _ => yes | _ => Sskip end.
Definition ske_after_timer version :=
  Ssequence (ske_test version) (ske_choice version).
Definition ske_timer := ics_field SK._m SK._MarioState SK._actionTimer tushort.
Definition ske_height_test :=
  Ecast (Ebinop Ogt
    (Ebinop Osub (Etempvar SK._t'20 tfloat) (Etempvar SK._t'21 tfloat) tfloat)
    (Econst_single (Float32.of_bits (Int.repr 1140457472)) tfloat) tint) tbool.
Definition ske_height_reads :=
  Ssequence (Sset SK._t'20 rank11_mario_y_expression)
    (Ssequence (Sset SK._t'21 (rank11_mario_field_expression SK._floorHeight tfloat))
      (Sset SK._t'4 ske_height_test)).
Definition ske_late timer := Int.lt (Int.repr 30) timer.
Definition ske_high y floor :=
  Float32.cmp Cgt (Float32.sub y floor) (rank9cf_integer 500).
Definition ske_test_temps le timer y floor :=
  if ske_late timer then
    PTree.set SK._t'4 (Val.of_bool (ske_high y floor))
      (PTree.set SK._t'21 (Vsingle floor) (PTree.set SK._t'20 (Vsingle y) le))
  else PTree.set SK._t'4 (Vint Int.zero) le.

Theorem ske_generated_cuts : forall version,
  ske_gate version = Ssequence
    (Ssequence (ske_increment version) (ske_test version)) (ske_choice version) /\
  ske_increment version = Ssequence
    (Ssequence (Sset SK._t'22 ske_timer)
      (Sset SK._t'3 (Ecast (Ebinop Oadd (Etempvar SK._t'22 tushort)
        (Econst_int Int.one tint) tint) tushort)))
    (Sassign ske_timer (Etempvar SK._t'3 tushort)) /\
  ske_test version = Sifthenelse
    (Ebinop Ogt (Etempvar SK._t'3 tushort) (Econst_int (Int.repr 30) tint) tint)
    ske_height_reads (Sset SK._t'4 (Econst_int Int.zero tint)) /\
  ske_choice version =
    Sifthenelse (Etempvar SK._t'4 tint) (ske_yes version) Sskip /\
  ske_yes version = Ssequence
    (Scall (Some SK._t'2) (Evar SK._set_mario_action ilh_set_action_type)
      [Etempvar SK._m (tptr (Tstruct SK._MarioState noattr));
       Econst_int (Int.repr 16779404) tint; Econst_int (Int.repr 2) tint])
    (Sreturn (Some (Etempvar SK._t'2 tuint))).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ske_us_source :
  nth_error SK.global_definitions
    (ueqr_definition_index SK._act_slide_kick SK.global_definitions) =
  Some (SK._act_slide_kick, Gfun (Internal (ske_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma ske_us_member :
  In (SK._act_slide_kick, Gfun (Internal (ske_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 2 us_units).
  - exact (us_nlist_at_nIn _ 2 us_units).
  - eapply nth_error_In. exact ske_us_source.
Qed.
Lemma ske_us_selection :
  us_normalized_global_definition_map ! SK._act_slide_kick =
    Some (Gfun (Internal (ske_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact ske_us_member.
Qed.
Lemma ske_us_selected :
  In (SK._act_slide_kick, Gfun (Internal (ske_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact ske_us_selection.
Qed.
Lemma ske_jp_source :
  (prog_defmap (nlist_at 2 jp_cleaned_units)) ! SK._act_slide_kick =
    Some (Gfun (Internal (ske_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem ske_selected_body_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SK._act_slide_kick = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ske_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ske_us_selected.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 2 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 2 jp_cleaned_units).
    + exact ske_jp_source.
Qed.

Lemma ske_500_bits :
  Float32.of_bits (Int.repr 1140457472) = rank9cf_integer 500.
Proof. apply rank9cf_bits_injective; vm_compute; reflexivity. Qed.

Lemma ske_height_test_eval : forall ge e le m y floor,
  le ! SK._t'20 = Some (Vsingle y) ->
  le ! SK._t'21 = Some (Vsingle floor) ->
  eval_expr ge e le m ske_height_test (Val.of_bool (ske_high y floor)).
Proof.
  intros ge e le m y floor Hy Hf.
  unfold ske_height_test. eapply eval_Ecast.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop; [apply eval_Etempvar; exact Hy |
        apply eval_Etempvar; exact Hf | reflexivity].
    + constructor.
    + cbn. rewrite ske_500_bits. reflexivity.
  - unfold ske_high. destruct (Float32.cmp Cgt (Float32.sub y floor)
      (rank9cf_integer 500)); reflexivity.
Qed.

Theorem ske_actual_timer_and_height_test : forall version e le m mb timer y floor,
  le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
  le ! SK._t'3 = Some (Vint timer) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle floor) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ske_test version) E0 (ske_test_temps le timer y floor) m Out_normal.
Proof.
  intros version e le m mb timer y floor Hm Htimer Hy Hfloor.
  destruct (ske_generated_cuts version) as (_ & _ & Htest & _). rewrite Htest.
  unfold ske_test_temps. destruct (ske_late timer) eqn:Hlate.
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
    + eapply eval_Ebinop; [apply eval_Etempvar; exact Htimer|constructor|].
      change (Some (Val.of_bool (ske_late timer)) = Some (Vint Int.one)).
      rewrite Hlate; reflexivity.
    + reflexivity.
    + unfold ske_height_reads. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply rank11_mario_y_read; eauto.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_Sset. eapply rank10e_floor_read; eauto.
           rewrite PTree.gso by discriminate. exact Hm.
        -- apply exec_Sset. apply ske_height_test_eval.
           ++ rewrite PTree.gso by discriminate. apply PTree.gss.
           ++ apply PTree.gss.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; exact Htimer|constructor|].
      change (Some (Val.of_bool (ske_late timer)) = Some (Vint Int.zero)).
      rewrite Hlate; reflexivity.
    + reflexivity.
    + apply exec_Sset; constructor.
Qed.

(** This is the live US/JP decision, with the actual memory reads. The timer
    may have ANY value; expiration alone does not cause freefall. *)
Theorem ske_not_high_cannot_take_timeout : forall version e le m mb timer y floor,
  le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
  le ! SK._t'3 = Some (Vint timer) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle floor) ->
  ske_high y floor = false ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ske_after_timer version) E0 (ske_test_temps le timer y floor) m Out_normal.
Proof.
  intros version e le m mb timer y floor Hm Htimer Hy Hfloor Hhigh.
  unfold ske_after_timer. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - eapply ske_actual_timer_and_height_test; eauto.
  - destruct (ske_generated_cuts version) as (_ & _ & _ & Hchoice & _).
    rewrite Hchoice. eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + apply eval_Etempvar. unfold ske_test_temps.
      destruct (ske_late timer); rewrite PTree.gss; [rewrite Hhigh|]; reflexivity.
    + reflexivity.
    + constructor.
Qed.

(** Conversely, the taken decision reaches the REAL setter with FREEFALL,
    argument 2, and returns one if that call completes. Its call effects are
    retained, not replaced by a memory-frame assumption. *)
Theorem ske_high_timeout_calls_real_setter :
  forall version e le m mb timer y floor trace after result,
  le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
  le ! SK._t'3 = Some (Vint timer) ->
  e ! SK._set_mario_action = None ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle floor) ->
  ske_late timer = true -> ske_high y floor = true ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ilh_set_action_body version))
    [Vptr mb Ptrofs.zero; Vint (Int.repr 16779404); Vint (Int.repr 2)]
    trace after result ->
  exists last,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ske_after_timer version) trace last after
    (Out_return (Some (Vint Int.one, tuint))).
Proof.
  intros version e le m mb timer y floor trace after result
    Hm Htimer Hlocal Hy Hfloor Hlate Hhigh Hcall.
  pose proof (ilh_completed_set_action_call_returns_one _ _ _ _ _ _ Hcall) as ->.
  destruct (ilh_selected_set_action_resolves version) as (fb & Hsymbol & Hfun).
  set (ready := ske_test_temps le timer y floor).
  assert (ready ! SK._m = Some (Vptr mb Ptrofs.zero)) as Hready.
  { unfold ready, ske_test_temps. rewrite Hlate.
    repeat rewrite PTree.gso by discriminate. exact Hm. }
  exists (PTree.set SK._t'2 (Vint Int.one) ready).
  unfold ske_after_timer.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := trace).
  - eapply ske_actual_timer_and_height_test; eauto.
  - destruct (ske_generated_cuts version) as (_ & _ & _ & Hchoice & Hyes).
    rewrite Hchoice. eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
    + apply eval_Etempvar. unfold ready, ske_test_temps.
      rewrite Hlate, PTree.gss, Hhigh. reflexivity.
    + reflexivity.
    + rewrite Hyes.
      rewrite <- (app_nil_r trace) at 1.
      eapply exec_Sseq_1 with (t1 := trace) (t2 := E0).
      * eapply exec_Scall with
          (vf := Vptr fb Ptrofs.zero)
          (vargs := [Vptr mb Ptrofs.zero; Vint (Int.repr 16779404); Vint (Int.repr 2)])
          (f := Internal (ilh_set_action_body version)).
        -- reflexivity.
        -- eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
           ++ apply eval_Evar_global; [exact Hlocal | exact Hsymbol].
           ++ apply deref_loc_reference; reflexivity.
        -- econstructor; [apply eval_Etempvar; exact Hready | reflexivity |].
           econstructor; [constructor | reflexivity |].
           econstructor; [constructor | reflexivity | constructor].
        -- exact Hfun.
        -- destruct version; reflexivity.
        -- exact Hcall.
      * apply exec_Sreturn_some with (v := Vint Int.one).
        apply eval_Etempvar; apply PTree.gss.
Qed.


(** Complete the earlier timer read, narrowing and store too. The store is
    the actual writable-cell obligation, not a blanket safety condition. *)
Definition ske_next_timer before := Int.zero_ext 16 (Int.add before Int.one).
Definition ske_increment_temps le before :=
  PTree.set SK._t'3 (Vint (ske_next_timer before))
    (PTree.set SK._t'22 (Vint before) le).

Lemma ske_timer_location : forall version e le m mb,
  le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version))
    e le m ske_timer mb (Ptrofs.repr 26) Full.
Proof.
  intros version e le m mb Hm.
  destruct (ibcc_field_ok_sound _ _ _ _ (proj1 (imb_control_fields version)))
    as (co & Hco & Hoff).
  replace (Ptrofs.repr 26) with
    (Ptrofs.add Ptrofs.zero (Ptrofs.repr 26)) by reflexivity.
  unfold ske_timer, ics_field.
  eapply eval_Efield_struct with (co := co).
  - eapply eval_Elvalue; [apply eval_Ederef; apply eval_Etempvar; exact Hm|].
    apply deref_loc_copy; reflexivity.
  - reflexivity.
  - exact Hco.
  - exact Hoff.
Qed.

Theorem ske_actual_timer_store : forall version e le m mb before written,
  le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint16unsigned m mb 26 = Some (Vint before) ->
  Mem.store Mint16unsigned m mb 26 (Vint (ske_next_timer before)) = Some written ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ske_increment version) E0 (ske_increment_temps le before) written Out_normal.
Proof.
  intros version e le m mb before written Hm Hload Hstore.
  destruct (ske_generated_cuts version) as (_ & Hinc & _). rewrite Hinc.
  unfold ske_increment_temps.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply eval_Elvalue with (ofs := Ptrofs.repr 26) (bf := Full).
      * eapply ske_timer_location; exact Hm.
      * eapply deref_loc_value with (chunk := Mint16unsigned); eauto.
    + apply exec_Sset. eapply eval_Ecast.
      * eapply eval_Ebinop.
        -- apply eval_Etempvar; apply PTree.gss.
        -- constructor.
        -- reflexivity.
      * reflexivity.
  - eapply exec_Sassign with (loc := mb) (ofs := Ptrofs.repr 26) (bf := Full)
      (v := Vint (ske_next_timer before)) (v2 := Vint (ske_next_timer before)).
    + eapply ske_timer_location.
      repeat rewrite PTree.gso by discriminate. exact Hm.
    + apply eval_Etempvar; apply PTree.gss.
    + cbn. unfold ske_next_timer.
      rewrite Int.zero_ext_idem by lia. reflexivity.
    + eapply assign_loc_value with (chunk := Mint16unsigned); try reflexivity.
      exact Hstore.
Qed.

Theorem ske_full_gate_no_timeout : forall version e le m mb before written y floor,
  le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint16unsigned m mb 26 = Some (Vint before) ->
  Mem.store Mint16unsigned m mb 26 (Vint (ske_next_timer before)) = Some written ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle floor) ->
  ske_high y floor = false ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ske_gate version) E0
    (ske_test_temps (ske_increment_temps le before) (ske_next_timer before) y floor)
    written Out_normal /\
  Mem.load Mint32 written mb 12 = Mem.load Mint32 m mb 12.
Proof.
  intros version e le m mb before written y floor Hm Hload Hstore Hy Hfloor Hhigh.
  assert (HafterY : Mem.load Mfloat32 written mb 64 = Some (Vsingle y)).
  { rewrite <- Hy. eapply Mem.load_store_other; [exact Hstore|right; right; cbn; lia]. }
  assert (HafterFloor : Mem.load Mfloat32 written mb 112 = Some (Vsingle floor)).
  { rewrite <- Hfloor. eapply Mem.load_store_other; [exact Hstore|right; right; cbn; lia]. }
  split.
  - destruct (ske_generated_cuts version) as (Hgate & _ & _ & Hchoice & _).
    rewrite Hgate. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply ske_actual_timer_store; eauto.
      * eapply ske_actual_timer_and_height_test; eauto.
        -- unfold ske_increment_temps. repeat rewrite PTree.gso by discriminate. exact Hm.
        -- unfold ske_increment_temps. apply PTree.gss.
    + rewrite Hchoice. eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      * apply eval_Etempvar. unfold ske_test_temps.
        destruct (ske_late (ske_next_timer before)); rewrite PTree.gss;
          [rewrite Hhigh|]; reflexivity.
      * reflexivity.
      * constructor.
  - eapply Mem.load_store_other; [exact Hstore|right; left; cbn; lia].
Qed.
