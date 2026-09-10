(** One action/native continuation through visibility, body reset and input
    preparation, ending at the real button call.  No completed input helper
    or all-calls-are-safe premise is used. *)
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes ClightRefinement
  InkBackwardSource InkActionPassStart InkActionPassHistory InkBodyResetHistory
  InkBodyResetConstruction InkPreparationConstruction InkAcceptedInitialStorage
  InkScheduledSharedHistory InkSharedReadings InkInputPrefixConstruction
  InkControllerSource InkMarioInputReset ObjectContactNecessity
  DefaultArea1StartBoundary OrdinaryArea1EntryMemory SelectedClightTarget InputSemantics.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iih_call_temp version := match version with VersionUS => IBM._t'46 | VersionJP => IBM._t'42 end.
Definition iih_after_input version := match ibr_after_reset version with
| Ssequence _ rest => rest | _ => Sskip end.
Definition iih_input_call version := Scall None
  (Evar IBM._update_mario_inputs (Tfunction [tptr (Tstruct IBM._MarioState noattr)] tvoid cc_default))
  [Etempvar (iih_call_temp version) (tptr (Tstruct IBM._MarioState noattr))].
Definition iih_input_cont version le mb k := Kcall None (iap_body version) empty_env
  (PTree.set (iih_call_temp version) (Vptr mb Ptrofs.zero) le) (Kseq (iih_after_input version) k).
Definition iih_entry_temps version kind mb := PTree.set IBM._m (Vptr mb Ptrofs.zero)
  (create_undef_temps (fn_temps (ics_body version kind))).
Definition iih_button_cont version ready k := Kcall None (ics_body version ICInputs)
  empty_env ready (Kseq (imr_after_buttons version) k).

Lemma iih_source : forall version,
  ibr_after_reset version = Ssequence
    (Ssequence (Sset (iih_call_temp version) ias_global) (iih_input_call version))
    (iih_after_input version).
Proof. intros []; reflexivity. Qed.

Lemma iih_entry : forall version kind m mb,
  kind = ICInputs \/ kind = ICButtons ->
  function_entry2 (Clight.globalenv (selected_clight_target version)) (ics_body version kind)
    [Vptr mb Ptrofs.zero] m empty_env (iih_entry_temps version kind mb) m.
Proof.
  intros version kind m mb Hkind. destruct Hkind as [Hkind|Hkind]; subst kind; constructor;
    destruct version; try reflexivity; try apply alloc_variables_nil;
    try (repeat constructor; cbn; tauto); vm_compute; intuition congruence.
Qed.

Lemma iih_action_calls_inputs : forall version m le global mb k,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState = Some global ->
  Mem.load Mint32 m global 0 = Some (Vptr mb Ptrofs.zero) ->
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (iap_body version) (ibr_after_reset version) k empty_env le m) E0
    (Callstate (Internal (ics_body version ICInputs)) [Vptr mb Ptrofs.zero]
      (iih_input_cont version le mb k) m).
Proof.
  intros version m le global mb k Hsymbol Hglobal.
  destruct (ics_selected_bodies_resolve version ICInputs) as (fb & Hfs & Hff).
  rewrite iih_source. eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left; [apply step_set; eapply ias_global_read; eauto| |reflexivity].
  eapply star_left; [apply step_skip_seq| |reflexivity].
  apply star_one. unfold iih_input_call, iih_input_cont.
  eapply step_call with (vf := Vptr fb Ptrofs.zero).
  - reflexivity.
  - eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
    + apply eval_Evar_global; [reflexivity|exact Hfs].
    + apply deref_loc_reference. reflexivity.
  - econstructor; [apply eval_Etempvar; apply PTree.gss|reflexivity|constructor].
  - exact Hff.
  - destruct version; reflexivity.
Qed.

Lemma iih_frontier_calls_buttons : forall version m ready mb k,
  ready ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (ics_body version ICInputs) (iic_button_frontier version) k empty_env ready m) E0
    (Callstate (Internal (ics_body version ICButtons)) [Vptr mb Ptrofs.zero]
      (iih_button_cont version ready k) m).
Proof.
  intros version m ready mb k Hm.
  destruct (ics_selected_bodies_resolve version ICButtons) as (fb & Hfs & Hff).
  unfold iic_button_frontier. eapply star_left; [apply step_seq| |reflexivity].
  rewrite (proj1 (proj2 (imr_source version))). apply star_one. unfold iih_button_cont.
  eapply step_call with (vf := Vptr fb Ptrofs.zero).
  - reflexivity.
  - eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
    + apply eval_Evar_global; [reflexivity|exact Hfs].
    + apply deref_loc_reference. reflexivity.
  - econstructor; [apply eval_Etempvar; exact Hm|reflexivity|constructor].
  - exact Hff.
  - destruct version; reflexivity.
Qed.

Lemma iih_shared_cell_outside : forall a cell,
  area1_state_storage_block a <> area1_object_pool_block a ->
  In cell (ink_shared_cells a) ->
  ink_cell_block cell <> area1_state_storage_block a \/
    (iic_outside_cell Mint32 8 cell /\ iic_outside_cell Mint16unsigned 2 cell /\
     iic_outside_cell Mint32 164 cell /\ iic_outside_cell Mint32 4 cell).
Proof.
  intros a cell Hseparate Hin. cbn [ink_shared_cells In] in Hin.
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
    try contradiction; subst cell; unfold iic_outside_cell;
    cbn [ink_cell ink_cell_block ink_cell_offset ink_cell_chunk size_chunk];
    intuition (try congruence; lia).
Qed.

Theorem iih_action_reaches_buttons : forall version m a le global k,
  InkInputPrefixStorage m (area1_state_storage_block a) (area1_object_pool_block a)
    (Ptrofs.repr (mario_object_base a)) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState = Some global ->
  Mem.load Mint32 m global 0 = Some (Vptr (area1_state_storage_block a) Ptrofs.zero) ->
  exists after ready,
    star Clight.step2 (Clight.globalenv (selected_clight_target version))
      (State (iap_body version) (ibr_after_reset version) k empty_env le m) E0
      (Callstate (Internal (ics_body version ICButtons)) [Vptr (area1_state_storage_block a) Ptrofs.zero]
        (iih_button_cont version ready (iih_input_cont version le (area1_state_storage_block a) k)) after) /\
    InkSameReadings a m after /\
    Mem.load Mint16unsigned after (area1_state_storage_block a) 2 = Some (Vint Int.zero) /\
    (forall chunk b offset, b <> area1_state_storage_block a ->
      Mem.load chunk after b offset = Mem.load chunk m b offset) /\
    ready ! IBM._m = Some (Vptr (area1_state_storage_block a) Ptrofs.zero).
Proof.
  intros version m a le global k Hstorage Hsymbol Hglobal.
  destruct (iic_construct_input_prefix version m _ _ _
    (iih_entry_temps version ICInputs (area1_state_storage_block a)) Hstorage ltac:(apply PTree.gss))
    as (after & ready & Hchain & Hm & Hzero & Hframe & Hvalid).
  exists after, ready. split.
  - eapply star_trans; [eapply iih_action_calls_inputs; eauto| |reflexivity].
    eapply star_left; [apply step_internal_function; apply iih_entry; left; reflexivity| |reflexivity].
    rewrite iic_source.
    eapply star_trans; [eapply iap_chain_steps; exact Hchain| |reflexivity].
    apply iih_frontier_calls_buttons. exact Hm.
  - split.
    + intros cell Hin. apply Hframe.
      apply iih_shared_cell_outside; [exact (iic_state_object_separate _ _ _ _ Hstorage)|exact Hin].
    + split; [exact Hzero|]. split; [|exact Hm]. intros chunk b offset Hseparate.
      exact (Hframe (ink_cell chunk b offset) (or_introl Hseparate)).
Qed.

(** Additional normal writable INITIAL fields; the old contents of input,
    particles and copied interaction flags are deliberately not assumed safe. *)
Definition InkAcceptedInitialInputStorage m a : Prop :=
  Forall (fun cell => Mem.valid_access m (fst cell) (area1_state_storage_block a) (snd cell) Writable)
    [(Mint32, 8); (Mint16unsigned, 2); (Mint32, 164); (Mint32, 4)].

Definition InkAcceptedInitialInputConstruction : Prop :=
  forall version m world previous current body k,
  DefaultArea1StartBoundary version (selected_clight_target version) m world previous current ->
  InkAcceptedInitialStorage version m (default_area1_entry_addresses world) body ->
  InkAcceptedInitialInputStorage m (default_area1_entry_addresses world) ->
  let a := default_area1_entry_addresses world in
  exists (run : ImportedClightRun) after button_k,
    run_program run = selected_clight_target version /\
    run_start run = Callstate (Internal (iap_body version))
      [object_slot_pointer a (area1_mario_slot a)] k m /\ run_trace run = E0 /\
    run_final run = Callstate (Internal (ics_body version ICButtons))
      [Vptr (area1_state_storage_block a) Ptrofs.zero] button_k after /\
    InkSameReadings a m after /\ InkInitialProducerReadings after a /\
    Mem.load Mint16unsigned after (area1_state_storage_block a) 2 = Some (Vint Int.zero) /\
    Mem.load Mint32 after (area1_state_storage_block a) 156 =
      Some (Vptr (area1_controller_storage_block a) Ptrofs.zero) /\
    Mem.load Mint16unsigned after (area1_controller_storage_block a) 18 =
      Some (Vint (edge_pressed current previous)) /\
    Int.testbit (edge_pressed current previous) 15 = false /\
    (exists input_ready input_k,
      button_k = iih_button_cont version input_ready input_k /\
      input_ready ! IBM._m = Some (Vptr (area1_state_storage_block a) Ptrofs.zero)).

Theorem iih_accepted_initial_action_reaches_buttons : InkAcceptedInitialInputConstruction.
Proof.
  intros version m world previous current body k Hstart Hstorage Hinput. cbn zeta.
  set (a := default_area1_entry_addresses world) in *.
  destruct (ias_boundary_constructs_action_call_start version m world previous current k Hstart)
    as (prefix & ready & fb & Hfs & Hff & Hp & Hs & Ht & Hf & Ho1 & Ho2 & Hdepth).
  pose proof (ini_initial_storage_supplies_preparation _ _ _ _ _ _ Hstart Hstorage) as Hprep.
  pose proof (default_area1_world_entry_symbols _ _ _
    (default_area1_start_symbol_bindings _ _ _ _ _ _ Hstart)) as Hsymbols.
  pose proof (default_area1_start_entry_memory _ _ _ _ _ _ Hstart) as Hmemory.
  assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState =
    Some (area1_state_pointer_cell_block a)) as Hsymbol.
  { destruct version; [exact (us_area1_state_pointer_symbol _ _ Hsymbols)|
      exact (jp_area1_state_pointer_symbol _ _ Hsymbols)]. }
  destruct (ipc_construct_preparation version m a _ body ready (Kseq (ias_return version) k)
    Hprep Hsymbol (ordinary_area1_state_global_pointer _ _ _ _ _ _ Hmemory) Ho1 Ho2)
    as (middle & prepared & Hprepsteps & Hprepframe & Hglobal & Hvalid & Hflags & Hcollision & Hother).
  assert (InkInputPrefixStorage middle (area1_state_storage_block a) (area1_object_pool_block a)
    (Ptrofs.repr (mario_object_base a))) as Hinput'.
  { constructor.
    - exact (ipc_state_pool _ _ _ _ Hprep).
    - change (ink_read middle (ink_cell Mint32 (area1_state_storage_block a) 136) =
        Some (object_slot_pointer a (area1_mario_slot a))).
      rewrite Hprepframe.
      + exact (ordinary_area1_state_object_pointer _ _ _ _ _ _ Hmemory).
      + cbn [ink_shared_cells In]. auto 20.
    - exists Int.zero. rewrite (ipc_slot_address a 112 (ipc_slots _ _ _ _ Hprep))
        by (unfold object_size; lia). rewrite Hcollision.
      exact (ordinary_area1_mario_collided_types_zero _ _ _ _ _ _ Hmemory).
    - exact Hflags.
    - eapply Forall_impl; [|exact Hinput]. intros item Hitem. apply Hvalid. exact Hitem. }
  destruct (iih_action_reaches_buttons version middle a prepared _ (Kseq (ias_return version) k)
    Hinput' Hsymbol Hglobal) as (after & button_ready & Hinputsteps & Hinputframe & Hzero & Hinputother & Hready).
  assert (star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (run_final prefix) E0 (Callstate (Internal (ics_body version ICButtons))
      [Vptr (area1_state_storage_block a) Ptrofs.zero]
      (iih_button_cont version button_ready (iih_input_cont version prepared
        (area1_state_storage_block a) (Kseq (ias_return version) k))) after)) as Hextension.
  { rewrite Hf. eapply star_trans; [exact Hprepsteps|exact Hinputsteps|reflexivity]. }
  destruct (ish_append_actual_run _ _ _ _ _ Hp eq_refl Hextension)
    as (joined & Hjp & Hjs & Hjt & Hjf & Hcut).
  exists joined, after, (iih_button_cont version button_ready (iih_input_cont version prepared
    (area1_state_storage_block a) (Kseq (ias_return version) k))).
  assert (InkSameReadings a m after) as Hframe by (eapply ink_same_readings_trans; eauto).
  split; [exact Hjp|]. split; [rewrite Hjs; exact Hs|].
  split; [rewrite Hjt, Ht; reflexivity|]. split; [exact Hjf|]. split; [exact Hframe|].
  split.
  - eapply ink_same_readings_keep_initial_producers; [exact Hframe|].
    exact (ink_accepted_start_initializes_both_producers _ _ _ _ _ Hstart).
  - split; [exact Hzero|]. split.
    + change (ink_read after (ink_cell Mint32 (area1_state_storage_block a) 156) =
        Some (Vptr (area1_controller_storage_block a) Ptrofs.zero)).
      rewrite Hframe.
      * exact (ordinary_area1_state_controller_pointer _ _ _ _ _ _ Hmemory).
      * cbn [ink_shared_cells In]. auto 20.
    + split.
      2: { split; [exact (default_area1_start_no_a_edge _ _ _ _ _ _ Hstart)|].
        eexists; eexists. split; [reflexivity|exact Hready]. }
      assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gControllers =
        Some (area1_controller_storage_block a)) as Hcontrollers.
      { destruct version; [exact (us_area1_controller_storage_symbol _ _ Hsymbols)|
          exact (jp_area1_controller_storage_symbol _ _ Hsymbols)]. }
      assert (area1_controller_storage_block a <> area1_state_storage_block a /\
        area1_controller_storage_block a <> area1_object_pool_block a) as [Hcs Hcp].
      { destruct version.
        - destruct (us_area1_entry_storage_blocks_pairwise_distinct _ _ Hsymbols) as (Hsc & Hsp & Hcp).
          split; [intro Heq; apply Hsc; symmetry; exact Heq|exact Hcp].
        - destruct (jp_area1_entry_storage_blocks_pairwise_distinct _ _ Hsymbols) as (Hsc & Hsp & Hcp).
          split; [intro Heq; apply Hsc; symmetry; exact Heq|exact Hcp]. }
      assert (area1_controller_storage_block a <> body) as Hcb.
      { eapply Genv.global_addresses_distinct with
          (id1 := IBM._gControllers) (id2 := IBM._gBodyStates); [discriminate|exact Hcontrollers|].
        exact (ini_body_symbol _ _ _ _ Hstorage). }
      rewrite Hinputother by exact Hcs.
      rewrite Hother by assumption.
      exact (ordinary_area1_controller_pressed _ _ _ _ _ _ Hmemory).
Qed.
