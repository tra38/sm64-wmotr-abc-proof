(** Construct the real action-call prefix from the accepted memory facts.
    Unlike InkActionPassHistory this does not assume a completed pass.
    Scheduling this call with this memory remains a separate obligation. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop Ctypes
  Errors Events Floats Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Generated Require Import us_mario jp_mario.
From LessThanOneAPress.Proofs Require Import GameTypes EntryMemory
  OrdinaryArea1EntryMemory DefaultArea1StartBoundary SelectedClightTarget
  InkActionPassHistory InkBackwardSource InkCopyCaller EyerokRank15LiveMovement
  ObjectContactNecessity ClightRefinement InkActionPassResolution.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ias_global := Evar IBM._gMarioState (tptr (Tstruct IBM._MarioState noattr)).
Definition ias_field temp field ty := Efield
  (Ederef (Etempvar temp (tptr (Tstruct IBM._MarioState noattr)))
    (Tstruct IBM._MarioState noattr)) field ty.
Definition ias_return version := match fn_body (iap_body version) with
| Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition ias_visibility version := ibk_head (iap_enabled version).
Definition ias_after_visibility version := match iap_enabled version with
| Ssequence _ rest => rest | _ => Sskip end.
Definition ias_m1 version := match version with VersionUS => IBM._t'48 | VersionJP => jp_mario._t'44 end.
Definition ias_o1 version := match version with VersionUS => IBM._t'49 | VersionJP => jp_mario._t'45 end.
Definition ias_m2 version := match version with VersionUS => IBM._t'50 | VersionJP => jp_mario._t'46 end.
Definition ias_o2 version := match version with VersionUS => IBM._t'51 | VersionJP => jp_mario._t'47 end.
Definition ias_pointer_reads version :=
  [Sset (ias_m1 version) ias_global;
   Sset (ias_o1 version) (ias_field (ias_m1 version) IBM._marioObj (tptr (Tstruct IBM._Object noattr)));
   Sset (ias_m2 version) ias_global;
   Sset (ias_o2 version) (ias_field (ias_m2 version) IBM._marioObj (tptr (Tstruct IBM._Object noattr)))].
Definition ias_flag_frontier version :=
  Area2Rank12BContact.rank12b_drop_sequences 4 (ias_visibility version).

Lemma ias_generated_start : forall version,
  fn_vars (iap_body version) = [] /\
  fn_body (iap_body version) = Ssequence
    (Sset IBM._inLoop (Econst_int (Int.repr 1) tint))
    (Ssequence (Ssequence (Sset IBM._t'8 ias_global)
      (Ssequence (Sset IBM._t'9 (ias_field IBM._t'8 IBM._action tuint))
        (Sifthenelse (Etempvar IBM._t'9 tuint) (iap_enabled version) Sskip)))
      (ias_return version)) /\
  iap_enabled version = Ssequence
    (ocn_prepend (ias_pointer_reads version) (ias_flag_frontier version))
    (ias_after_visibility version).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ias_selected_action_field : forall version,
  ibcc_field_ok (prog_comp_env (selected_clight_target version)) IBM._MarioState IBM._action 12 = true.
Proof.
  intro version. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Lemma ias_global_read : forall (ge : genv) le memory cell mario,
  Genv.find_symbol ge IBM._gMarioState = Some cell ->
  Mem.load Mint32 memory cell 0 = Some (Vptr mario Ptrofs.zero) ->
  eval_expr ge empty_env le memory ias_global (Vptr mario Ptrofs.zero).
Proof.
  intros ge le memory cell mario Hsymbol Hload.
  eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
  - apply eval_Evar_global; [reflexivity|exact Hsymbol].
  - eapply deref_loc_value with (chunk := Mint32); [reflexivity|exact Hload].
Qed.

Lemma ias_field_read : forall (ge : genv) le memory temp field ty chunk offset mario value,
  ibcc_field_ok ge IBM._MarioState field offset = true ->
  access_mode ty = By_value chunk ->
  le ! temp = Some (Vptr mario Ptrofs.zero) ->
  Mem.load chunk memory mario (Ptrofs.unsigned (Ptrofs.repr offset)) = Some value ->
  eval_expr ge empty_env le memory (ias_field temp field ty) value.
Proof.
  intros ge le memory temp field ty chunk offset mario value Hfield Hmode Htemp Hload.
  destruct (ibcc_field_ok_sound _ _ _ _ Hfield) as (co & Hco & Hoff).
  eapply eval_Elvalue with (ofs := Ptrofs.add Ptrofs.zero (Ptrofs.repr offset)) (bf := Full).
  - unfold ias_field. eapply eval_Efield_struct with (co := co).
    + eapply eval_Elvalue; [apply eval_Ederef; apply eval_Etempvar; exact Htemp|].
      apply deref_loc_copy. reflexivity.
    + reflexivity.
    + exact Hco.
    + exact Hoff.
  - eapply deref_loc_value with (chunk := chunk); [exact Hmode|].
    change (Mem.load chunk memory mario
      (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr offset))) = Some value).
    rewrite Ptrofs.add_zero_l. exact Hload.
Qed.

Definition ias_initial_temps version object :=
  PTree.set IBM._o object (create_undef_temps (fn_temps (iap_body version))).

Lemma ias_call_entry : forall version memory object,
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (iap_body version) [object] memory empty_env
    (ias_initial_temps version object) memory.
Proof.
  intros version memory object. constructor.
  - destruct version; constructor.
  - destruct version; repeat constructor; cbn; tauto.
  - destruct version; vm_compute; intuition congruence.
  - destruct version; apply alloc_variables_nil.
  - destruct version; reflexivity.
Qed.

Definition InkActionCallStartConstruction : Prop :=
  forall version memory world previous current k,
  DefaultArea1StartBoundary version (selected_clight_target version)
    memory world previous current ->
  let addresses := default_area1_entry_addresses world in
  let object := object_slot_pointer addresses (area1_mario_slot addresses) in
  exists (run : ImportedClightRun) ready function_block,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      IBM._execute_mario_action = Some function_block /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) function_block =
      Some (Internal (iap_body version)) /\
    run_program run = selected_clight_target version /\
    run_start run = Callstate (Internal (iap_body version)) [object] k memory /\
    run_trace run = E0 /\
    run_final run = State (iap_body version) (ias_flag_frontier version)
      (Kseq (ias_after_visibility version) (Kseq (ias_return version) k))
      empty_env ready memory /\
    ready ! (ias_o1 version) = Some object /\
    ready ! (ias_o2 version) = Some object /\
    iap_depth memory (area1_state_storage_block addresses) =
      Some (Vsingle positive_f32_zero).

Definition ias_ready_temps version le mario object :=
  PTree.set (ias_o2 version) object
    (PTree.set (ias_m2 version) (Vptr mario Ptrofs.zero)
      (PTree.set (ias_o1 version) object
        (PTree.set (ias_m1 version) (Vptr mario Ptrofs.zero) le))).

Lemma ias_pointer_chain : forall version le memory cell mario object,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState = Some cell ->
  Mem.load Mint32 memory cell 0 = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mint32 memory mario 136 = Some object ->
  iap_stage_chain (Clight.globalenv (selected_clight_target version)) empty_env
    le memory (ias_pointer_reads version) E0 (ias_ready_temps version le mario object) memory.
Proof.
  intros version le memory cell mario object Hsymbol Hglobal Hobject.
  destruct (ibcc_selected_fields version) as (_ & Hfield & _).
  unfold ias_pointer_reads, ias_ready_temps.
  eapply iap_chain_cons with (t1 := E0) (t2 := E0).
  - apply exec_Sset. eapply ias_global_read; eauto.
  - eapply iap_chain_cons with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply ias_field_read with (chunk := Mint32) (offset := 136);
        [exact Hfield|reflexivity|apply PTree.gss|exact Hobject].
    + eapply iap_chain_cons with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply ias_global_read; eauto.
      * eapply iap_chain_cons with (t1 := E0) (t2 := E0).
        -- apply exec_Sset. eapply ias_field_read with (chunk := Mint32) (offset := 136);
             [exact Hfield|reflexivity|apply PTree.gss|exact Hobject].
        -- constructor.
Qed.

Lemma ias_body_reaches_flag_read : forall version le memory cell mario object k,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState = Some cell ->
  Mem.load Mint32 memory cell 0 = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mint32 memory mario 12 = Some (Vint spin_airborne_entry_action) ->
  Mem.load Mint32 memory mario 136 = Some object ->
  exists ready,
  @Smallstep.star _ _ Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (iap_body version) (fn_body (iap_body version)) k empty_env le memory) E0
    (State (iap_body version) (ias_flag_frontier version)
      (Kseq (ias_after_visibility version) (Kseq (ias_return version) k))
      empty_env ready memory) /\
  ready ! (ias_o1 version) = Some object /\ ready ! (ias_o2 version) = Some object.
Proof.
  intros version le memory cell mario object k Hsymbol Hglobal Haction Hobject.
  destruct (ias_generated_start version) as (_ & Hbody & Hvisible).
  eexists. split.
  - rewrite Hbody. eapply star_left; [apply step_seq| |reflexivity].
    eapply star_left; [apply step_set; constructor| |reflexivity].
    eapply star_left; [apply step_skip_seq| |reflexivity].
    eapply star_left; [apply step_seq| |reflexivity].
    eapply star_left; [apply step_seq| |reflexivity].
    eapply star_left; [apply step_set; eapply ias_global_read; eauto| |reflexivity].
    eapply star_left; [apply step_skip_seq| |reflexivity].
    eapply star_left; [apply step_seq| |reflexivity].
    eapply star_left.
    + apply step_set. eapply ias_field_read with (chunk := Mint32) (offset := 12);
        [apply ias_selected_action_field|reflexivity|apply PTree.gss|exact Haction].
    + eapply star_left; [apply step_skip_seq| |reflexivity].
      eapply star_left.
      * eapply step_ifthenelse with (v1 := Vint spin_airborne_entry_action) (b := true).
        -- apply eval_Etempvar. apply PTree.gss.
        -- reflexivity.
      * rewrite Hvisible. eapply star_left; [apply step_seq| |reflexivity].
        eapply iap_chain_steps. eapply ias_pointer_chain; eauto.
      * reflexivity.
    + reflexivity.
  - unfold ias_ready_temps. split.
    + assert (ias_o2 version <> ias_o1 version) by (destruct version; discriminate).
      assert (ias_m2 version <> ias_o1 version) by (destruct version; discriminate).
      rewrite PTree.gso by congruence. rewrite PTree.gso by congruence. apply PTree.gss.
    + apply PTree.gss.
Qed.

Theorem ias_boundary_constructs_action_call_start : InkActionCallStartConstruction.
Proof.
  unfold InkActionCallStartConstruction.
  intros version memory world previous current k Hstart.
  cbn zeta.
  pose proof (default_area1_start_entry_memory _ _ _ _ _ _ Hstart) as Hentry.
  pose proof (default_area1_world_entry_symbols _ _ _
    (default_area1_start_symbol_bindings _ _ _ _ _ _ Hstart)) as Hsymbols.
  assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState =
    Some (area1_state_pointer_cell_block (default_area1_entry_addresses world))) as Hsymbol.
  { destruct version; [exact (us_area1_state_pointer_symbol _ _ Hsymbols)|
      exact (jp_area1_state_pointer_symbol _ _ Hsymbols)]. }
  destruct (ias_body_reaches_flag_read version
    (ias_initial_temps version (object_slot_pointer (default_area1_entry_addresses world)
      (area1_mario_slot (default_area1_entry_addresses world)))) memory
    (area1_state_pointer_cell_block (default_area1_entry_addresses world))
    (area1_state_storage_block (default_area1_entry_addresses world))
    (object_slot_pointer (default_area1_entry_addresses world)
      (area1_mario_slot (default_area1_entry_addresses world))) k Hsymbol
    (ordinary_area1_state_global_pointer _ _ _ _ _ _ Hentry)
    (ordinary_area1_action _ _ _ _ _ _ Hentry)
    (ordinary_area1_state_object_pointer _ _ _ _ _ _ Hentry))
    as (ready & Hsteps & Hfirst & Hsecond).
  assert (@Smallstep.star _ _ Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (iap_body version))
      [object_slot_pointer (default_area1_entry_addresses world)
        (area1_mario_slot (default_area1_entry_addresses world))] k memory) E0
    (State (iap_body version) (ias_flag_frontier version)
      (Kseq (ias_after_visibility version) (Kseq (ias_return version) k))
      empty_env ready memory)) as Hcall.
  { eapply star_left; [apply step_internal_function; apply ias_call_entry|exact Hsteps|reflexivity]. }
  destruct (ias_selected_action_resolves version) as (function_block & Hfs & Hff).
  exists {| run_program := selected_clight_target version;
    run_start := Callstate (Internal (iap_body version))
      [object_slot_pointer (default_area1_entry_addresses world)
        (area1_mario_slot (default_area1_entry_addresses world))] k memory;
    run_trace := E0;
    run_final := State (iap_body version) (ias_flag_frontier version)
      (Kseq (ias_after_visibility version) (Kseq (ias_return version) k))
      empty_env ready memory; run_steps := Hcall |}, ready, function_block.
  split; [exact Hfs|]. split; [exact Hff|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [exact Hfirst|]. split; [exact Hsecond|].
  exact (ordinary_area1_quicksand_depth_zero _ _ _ _ _ _ Hentry).
Qed.
