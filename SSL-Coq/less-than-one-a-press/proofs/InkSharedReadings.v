(** Shared memory observations for the two Ink producers. Failed loads and
    non-finite values are retained. These definitions do not assert a global
    invariant or supply missing entry/storage/scheduler premises. *)
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Clight Events Floats Integers Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes ClightRefinement
  EntryMemory OrdinaryArea1EntryMemory DefaultArea1StartBoundary SelectedClightTarget.
Import ListNotations.
Local Open Scope Z_scope.

Record InkReadCell := {
  ink_cell_chunk : memory_chunk;
  ink_cell_block : block;
  ink_cell_offset : Z
}.

Definition ink_read (m : mem) (cell : InkReadCell) : option val :=
  Mem.load (ink_cell_chunk cell) m (ink_cell_block cell) (ink_cell_offset cell).

Definition ink_cell chunk b ofs : InkReadCell :=
  {| ink_cell_chunk := chunk; ink_cell_block := b; ink_cell_offset := ofs |}.

(** This is the read set transported by the initial body-reset proof, not a
    claim that these are the only cells the whole game can ever depend on.
    The Mario flags at byte 4 deliberately need a separate update rule. *)
Definition ink_shared_cells (a : Area1EntryAddresses) : list InkReadCell :=
  let mb := area1_state_storage_block a in
  let ob := area1_object_pool_block a in
  let base := mario_object_base a in
  [ink_cell Mint32 mb 12; ink_cell Mint32 mb 16;
   ink_cell Mint16unsigned mb 24; ink_cell Mint16unsigned mb 26;
   ink_cell Mint32 mb 28; ink_cell Mint8unsigned mb 40;
   ink_cell Mfloat32 mb 60; ink_cell Mfloat32 mb 64; ink_cell Mfloat32 mb 68;
   ink_cell Mint32 mb 96; ink_cell Mint32 mb 100; ink_cell Mint32 mb 104;
   ink_cell Mfloat32 mb 108; ink_cell Mfloat32 mb 112;
   ink_cell Mint32 mb 136; ink_cell Mint32 mb 152; ink_cell Mint32 mb 156;
   ink_cell Mfloat32 mb 192;
   ink_cell Mfloat32 ob (base + 32); ink_cell Mfloat32 ob (base + 36);
   ink_cell Mfloat32 ob (base + 40);
   ink_cell Mfloat32 ob (base + 160); ink_cell Mfloat32 ob (base + 164);
   ink_cell Mfloat32 ob (base + 168)].

Definition InkSameReadings a before after : Prop :=
  forall cell, In cell (ink_shared_cells a) -> ink_read after cell = ink_read before cell.

Lemma ink_shared_cells_regions : forall a cell,
  In cell (ink_shared_cells a) ->
  (ink_cell_block cell = area1_state_storage_block a /\ 8 <= ink_cell_offset cell) \/
  (ink_cell_block cell = area1_object_pool_block a /\
    mario_object_base a + 4 <= ink_cell_offset cell).
Proof.
  intros a cell Hin. cbn [ink_shared_cells In] in Hin.
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
    try contradiction; subst cell; cbn [ink_cell ink_cell_block ink_cell_offset];
    (left; split; [reflexivity|lia]) || (right; split; [reflexivity|lia]).
Qed.

Lemma ink_same_readings_trans : forall a first middle last,
  InkSameReadings a first middle -> InkSameReadings a middle last ->
  InkSameReadings a first last.
Proof. intros a first middle last H1 H2 cell Hin. rewrite H2, H1; auto. Qed.

Definition InkInitialProducerReadings m a : Prop :=
  Mem.load Mfloat32 m (area1_state_storage_block a) 192 =
    Some (Vsingle positive_f32_zero) /\
  Mem.load Mfloat32 m (area1_state_storage_block a) 64 =
    Some (Vsingle default_area1_spawn_y) /\
  Mem.load Mfloat32 m (area1_object_pool_block a) (mario_object_base a + 36) =
    Some (Vsingle default_area1_spawn_y) /\
  Mem.load Mfloat32 m (area1_object_pool_block a) (mario_object_base a + 164) =
    Some (Vsingle default_area1_spawn_y).

Theorem ink_accepted_start_initializes_both_producers :
  forall version m world previous current,
  DefaultArea1StartBoundary version (selected_clight_target version) m world previous current ->
  InkInitialProducerReadings m (default_area1_entry_addresses world).
Proof.
  intros version m world previous current Hstart.
  pose proof (default_area1_start_entry_memory _ _ _ _ _ _ Hstart) as Hmemory.
  unfold InkInitialProducerReadings.
  split; [exact (ordinary_area1_quicksand_depth_zero _ _ _ _ _ _ Hmemory)|].
  split; [exact (ordinary_area1_state_y _ _ _ _ _ _ Hmemory)|].
  split; [exact (ordinary_area1_object_graphics_y _ _ _ _ _ _ Hmemory)|].
  exact (ordinary_area1_object_raw_y _ _ _ _ _ _ Hmemory).
Qed.

Lemma ink_same_readings_keep_initial_producers : forall a before after,
  InkSameReadings a before after -> InkInitialProducerReadings before a ->
  InkInitialProducerReadings after a.
Proof.
  intros a before after Hframe (Hd & Hm & Hg & Ho).
  unfold InkInitialProducerReadings.
  repeat split.
  - change (ink_read after (ink_cell Mfloat32 (area1_state_storage_block a) 192) =
      Some (Vsingle positive_f32_zero)).
    rewrite Hframe; [exact Hd|cbn [ink_shared_cells In]; tauto].
  - change (ink_read after (ink_cell Mfloat32 (area1_state_storage_block a) 64) =
      Some (Vsingle default_area1_spawn_y)).
    rewrite Hframe; [exact Hm|cbn [ink_shared_cells In]; tauto].
  - change (ink_read after (ink_cell Mfloat32 (area1_object_pool_block a)
      (mario_object_base a + 36)) = Some (Vsingle default_area1_spawn_y)).
    rewrite Hframe; [exact Hg|cbn [ink_shared_cells In]; tauto].
  - change (ink_read after (ink_cell Mfloat32 (area1_object_pool_block a)
      (mario_object_base a + 164)) = Some (Vsingle default_area1_spawn_y)).
    rewrite Hframe; [exact Ho|cbn [ink_shared_cells In]; tauto].
Qed.

(** A splice is made of real states and traces of one ImportedClightRun.
    It permits no replacement of a checkpoint by a matching-looking state. *)
Record InkRunCut (run : ImportedClightRun) := {
  ink_cut_state : Clight.state;
  ink_cut_before : trace;
  ink_cut_after : trace;
  ink_cut_trace : run_trace run = ink_cut_before ++ ink_cut_after;
  ink_cut_prefix : star Clight.step2 (Clight.globalenv (run_program run))
    (run_start run) ink_cut_before ink_cut_state;
  ink_cut_suffix : star Clight.step2 (Clight.globalenv (run_program run))
    ink_cut_state ink_cut_after (run_final run)
}.

(** The universal induction must establish each phase's concrete obligations
    described in docs/notes/ink-shared-history-invariants.md. No constructor
    below is evidence that a phase was reached or that its effects are safe. *)
Inductive InkHistoryPhase :=
| InkControllerSampling | InkVisibility | InkBodyReset | InkInputPreparation
| InkSpecialFloors | InkInteractions | InkActionDispatch
| InkGroundQueries | InkDisplayRefresh | InkFloorAlignment
| InkLandingSubtract | InkLandingClamp | InkLandingLateCalls
| InkSinkRead | InkObjectSynchronization | InkGraphicsRetry
| InkRemainingScheduler | InkAreaOrLifetimeChange.
