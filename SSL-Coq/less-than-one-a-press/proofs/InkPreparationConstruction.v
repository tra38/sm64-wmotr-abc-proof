(** Remove completed-stage premises from the shared native/action prefix.
    Every write and the resolved body-reset call below is constructed. *)
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkActionPassStart InkActionPassHistory InkActionVisibilityFrame InkBodyResetFrame
  InkBodyResetConstruction InkVisibilityConstruction InkBodyResetResolution
  InkBodyResetHistory InkSharedReadings InkScheduledSharedHistory
  InkScheduledActionSource InkMarioCallbackHistory InkNativeActionHistory
  ObjectContactNecessity OrdinaryArea1EntryMemory SelectedClightTarget ClightRefinement.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ipc_after_temps version le mb :=
  PTree.set (ibr_call_temp version) (Vptr mb Ptrofs.zero) le.

Lemma ipc_slot_address : forall a delta,
  area1_entry_slots_valid a -> 0 <= delta < object_size ->
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (mario_object_base a)) (Ptrofs.repr delta)) =
    mario_object_base a + delta.
Proof.
  intros a delta [Hslot _] Hdelta. apply Nat2Z.inj_lt in Hslot.
  assert (0 <= mario_object_base a /\ mario_object_base a + delta <= Ptrofs.max_unsigned) as Hrange.
  { unfold mario_object_base, object_slot_offset, object_size, object_pool_capacity in *.
    change (0 <= 608 * Z.of_nat (area1_mario_slot a) /\
      608 * Z.of_nat (area1_mario_slot a) + delta <= 4294967295).
    pose proof (Nat2Z.is_nonneg (area1_mario_slot a)). nia. }
  unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (mario_object_base a)) by lia.
  rewrite (Ptrofs.unsigned_repr delta) by (unfold object_size in Hdelta; change (0 <= delta <= 4294967295); lia).
  apply Ptrofs.unsigned_repr. lia.
Qed.

Lemma ipc_named_reset_stage : forall version le m global mb after,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState = Some global ->
  Mem.load Mint32 m global 0 = Some (Vptr mb Ptrofs.zero) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ibr_body version)) [Vptr mb Ptrofs.zero] E0 after Vundef ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ibr_call_stage version) E0 (ipc_after_temps version le mb) after Out_normal.
Proof.
  intros version le m global mb after Hsymbol Hglobal Hcall.
  destruct (ibr_selected_reset_resolves version) as (fb & Hfs & Hff).
  unfold ibr_call_stage, ibr_call_statement, ipc_after_temps.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_Sset. eapply ias_global_read; eauto.
  - eapply exec_Scall with (vf := Vptr fb Ptrofs.zero)
      (f := Internal (ibr_body version)) (vargs := [Vptr mb Ptrofs.zero]) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
      * apply eval_Evar_global; [reflexivity|exact Hfs].
      * apply deref_loc_reference. reflexivity.
    + econstructor; [apply eval_Etempvar; apply PTree.gss|reflexivity|constructor].
    + exact Hff.
    + destruct version; reflexivity.
    + exact Hcall.
Qed.

(** Concrete storage at one entry.  This is accepted only at normal startup;
    any use at a later call must first establish it in that same live run. *)
Record InkPreparationStorage m a global body : Prop := {
  ipc_slots : area1_entry_slots_valid a;
  ipc_state_pool : area1_state_storage_block a <> area1_object_pool_block a;
  ipc_global_pool : global <> area1_object_pool_block a;
  ipc_global_state : global <> area1_state_storage_block a;
  ipc_global_body : global <> body;
  ipc_body_pool : body <> area1_object_pool_block a;
  ipc_body_storage : InkBodyResetStorage m (area1_state_storage_block a) body;
  ipc_visibility_read : exists flags, Mem.load Mint16signed m (area1_object_pool_block a)
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (mario_object_base a)) (Ptrofs.repr 2))) =
      Some (Vint flags);
  ipc_visibility_write : Mem.valid_access m Mint16signed (area1_object_pool_block a)
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (mario_object_base a)) (Ptrofs.repr 2))) Writable
}.

Theorem ipc_construct_preparation : forall version m a global body le k,
  InkPreparationStorage m a global body ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState = Some global ->
  Mem.load Mint32 m global 0 = Some (Vptr (area1_state_storage_block a) Ptrofs.zero) ->
  le ! (ias_o1 version) = Some (object_slot_pointer a (area1_mario_slot a)) ->
  le ! (ias_o2 version) = Some (object_slot_pointer a (area1_mario_slot a)) ->
  exists after last,
    star Clight.step2 (Clight.globalenv (selected_clight_target version))
      (State (iap_body version) (ias_flag_frontier version)
        (Kseq (ias_after_visibility version) k) empty_env le m) E0
      (State (iap_body version) (ibr_after_reset version) k empty_env last after) /\
    InkSameReadings a m after /\
    Mem.load Mint32 after global 0 = Some (Vptr (area1_state_storage_block a) Ptrofs.zero) /\
    (forall chunk b offset permission, Mem.valid_access m chunk b offset permission ->
      Mem.valid_access after chunk b offset permission) /\
    (exists flags, Mem.load Mint32 after (area1_state_storage_block a) 4 = Some (Vint flags)) /\
    Mem.load Mint32 after (area1_object_pool_block a) (mario_object_base a + 112) =
      Mem.load Mint32 m (area1_object_pool_block a) (mario_object_base a + 112) /\
    (forall chunk b offset, b <> area1_state_storage_block a -> b <> body ->
      b <> area1_object_pool_block a -> Mem.load chunk after b offset = Mem.load chunk m b offset).
Proof.
  intros version m a global body le k Hstorage Hsymbol Hglobal Ho1 Ho2.
  destruct Hstorage as [Hslots Hstatepool Hglobalpool Hglobalstate Hglobalbody Hbodypool
    Hbody [gfxflags Hgfx] Hgfxaccess].
  destruct (ivc_construct_visibility version empty_env le m (area1_object_pool_block a)
    (Ptrofs.repr (mario_object_base a)) gfxflags Ho1 Ho2 Hgfx Hgfxaccess)
    as (middle & Hstore & Hvisible).
  assert (InkBodyResetStorage middle (area1_state_storage_block a) body) as Hbody'.
  { destruct Hbody as [Hbodyref Hbodystate [flags Hflags] Hflagsaccess Hbodyaccess].
    constructor; try assumption.
    - rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore) by (left; congruence). exact Hbodyref.
    - exists flags. rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore) by (left; congruence).
      exact Hflags.
    - eapply Mem.store_valid_access_1; eauto.
    - eapply Forall_impl; [|exact Hbodyaccess]. intros spec Haccess.
      unfold ibc_access in *. eapply Mem.store_valid_access_1; eauto. }
  assert (Mem.load Mint32 middle global 0 = Some (Vptr (area1_state_storage_block a) Ptrofs.zero))
    as Hglobal'.
  { rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore) by (left; congruence). exact Hglobal. }
  destruct (ibc_construct_complete_reset version middle _ body Hbody') as (after & Hcall & Hvalid & Htyped).
  pose proof (ipc_named_reset_stage version (ivc_after_temps version le gfxflags) middle global
    (area1_state_storage_block a) after Hsymbol Hglobal' Hcall) as Hreset.
  destruct (ibr_visibility_then_reset_shared_extension version a global body Ptrofs.zero le m
    E0 (ivc_after_temps version le gfxflags) middle E0
    (ipc_after_temps version (ivc_after_temps version le gfxflags) (area1_state_storage_block a))
    after k Hslots Hstatepool Hglobalpool (ibc_body_is_separate _ _ _ Hbody) Hbodypool
    Hsymbol Hglobal (ibc_body_reference _ _ _ Hbody) Ho1 Hvisible Hreset)
    as (Hframe & Hsteps).
  exists after, (ipc_after_temps version (ivc_after_temps version le gfxflags)
    (area1_state_storage_block a)).
  split; [exact Hsteps|]. split; [exact Hframe|]. split.
  - destruct (ibr_completed_reset_exact_frame version middle _ body Ptrofs.zero E0 after Vundef
      (ibc_body_reference _ _ _ Hbody') Hcall) as (_ & Hresetframe).
    change (ink_read after {| ink_cell_chunk := Mint32; ink_cell_block := global;
      ink_cell_offset := 0 |} = Some (Vptr (area1_state_storage_block a) Ptrofs.zero)).
    rewrite Hresetframe.
    + exact Hglobal'.
    + apply Forall_forall. intros. unfold ibr_body_disjoint, ibr_cell_disjoint. left. exact Hglobalbody.
    + unfold ibr_cell_disjoint. left. exact Hglobalstate.
  - split; [intros; apply Hvalid; eapply Mem.store_valid_access_1; eauto|].
    split; [exact Htyped|]. split.
    2: {
      intros chunk b offset Hbstate Hbbody Hbpool.
      destruct (ibr_completed_reset_exact_frame version middle _ body Ptrofs.zero E0 after Vundef
        (ibc_body_reference _ _ _ Hbody') Hcall) as (_ & Hresetframe).
      change (ink_read after (ink_cell chunk b offset) = ink_read m (ink_cell chunk b offset)).
      rewrite Hresetframe.
      - unfold ink_read, ink_cell. cbn [ink_cell_block ink_cell_offset ink_cell_chunk].
        eapply Mem.load_store_other; [exact Hstore|left; exact Hbpool].
      - apply Forall_forall. intros. unfold ibr_body_disjoint, ibr_cell_disjoint. left. exact Hbbody.
      - unfold ibr_cell_disjoint. left. exact Hbstate.
    }
    destruct (ibr_completed_reset_exact_frame version middle _ body Ptrofs.zero E0 after Vundef
      (ibc_body_reference _ _ _ Hbody') Hcall) as (_ & Hresetframe).
    change (ink_read after (ink_cell Mint32 (area1_object_pool_block a) (mario_object_base a + 112)) =
      ink_read m (ink_cell Mint32 (area1_object_pool_block a) (mario_object_base a + 112))).
    rewrite Hresetframe.
    + unfold ink_read, ink_cell. cbn [ink_cell_block ink_cell_offset ink_cell_chunk].
      eapply Mem.load_store_other; [exact Hstore|]. right; right.
      rewrite (ipc_slot_address a 2 Hslots) by (unfold object_size; lia). cbn [size_chunk]. lia.
    + apply Forall_forall. intros. unfold ibr_body_disjoint, ibr_cell_disjoint. left. cbn. congruence.
    + unfold ibr_cell_disjoint. left. cbn. congruence.
Qed.

Definition InkConstructedNativePreparation : Prop :=
  forall version (prefix : ImportedClightRun) m a k
    command_cell command ofs callback current_cell argument state_cell action body,
  run_program prefix = selected_clight_target version ->
  run_final prefix = Callstate (Internal (isn_body version)) [] k m ->
  InkNativeEntryReadings version m a command_cell command ofs callback
    current_cell argument state_cell action ->
  InkPreparationStorage m a state_cell body ->
  exists (joined : ImportedClightRun) after last,
    run_program joined = selected_clight_target version /\
    run_start joined = run_start prefix /\ run_trace joined = run_trace prefix /\
    run_final joined = State (iap_body version) (ibr_after_reset version)
      (Kseq (ias_return version) (isn_action_cont version command ofs callback argument k))
      empty_env last after /\
    InkSameReadings a m after /\
    Mem.load Mint32 after state_cell 0 = Some (Vptr (area1_state_storage_block a) Ptrofs.zero) /\
    (InkInitialProducerReadings m a -> InkInitialProducerReadings after a) /\
    exists cut : InkRunCut joined,
      ink_cut_state joined cut = run_final prefix /\
      ink_cut_before joined cut = run_trace prefix /\ ink_cut_after joined cut = E0.

Theorem ipc_native_preparation_is_constructed : InkConstructedNativePreparation.
Proof.
  intros version prefix m a k command_cell command ofs callback current_cell argument state_cell
    action body Hprogram Hfinal Hentry Hstorage.
  destruct Hentry as [Hcommand_symbol Hcommand Hoperand Hcallback Hcurrent_symbol Hcurrent Hcast
    Hstate_symbol Hstate Haction Hactive Hobject].
  destruct (isn_native_constructs_action_prefix version m command_cell command ofs callback
    current_cell argument state_cell (area1_state_storage_block a)
    (object_slot_pointer a (area1_mario_slot a)) action k Hcommand_symbol Hcommand Hoperand Hcallback
    Hcurrent_symbol Hcurrent Hcast Hstate_symbol Hstate Haction Hactive Hobject)
    as (ready & Hnative & Ho1 & Ho2).
  destruct (ipc_construct_preparation version m a state_cell body ready
    (Kseq (ias_return version) (isn_action_cont version command ofs callback argument k))
    Hstorage Hstate_symbol Hstate Ho1 Ho2) as (after & last & Hsteps & Hframe & Hglobal & Hvalid).
  assert (star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (isn_body version)) [] k m) E0
    (State (iap_body version) (ibr_after_reset version)
      (Kseq (ias_return version) (isn_action_cont version command ofs callback argument k))
      empty_env last after)) as Hwhole.
  { eapply star_trans; [exact Hnative|exact Hsteps|reflexivity]. }
  destruct (ish_append_actual_run _ _ _ _ _ Hprogram Hfinal Hwhole)
    as (joined & Hp & Hs & Ht & Hf & Hcut).
  exists joined, after, last.
  split; [exact Hp|]. split; [exact Hs|]. split; [rewrite Ht; apply app_nil_r|].
  split; [exact Hf|]. split; [exact Hframe|]. split; [exact Hglobal|]. split; [|exact Hcut].
  intro Hinitial. eapply ink_same_readings_keep_initial_producers; eauto.
Qed.
