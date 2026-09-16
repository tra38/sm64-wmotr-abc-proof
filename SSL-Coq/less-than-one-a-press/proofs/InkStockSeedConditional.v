(** Conditional seed-to-A composition.  This is an explicit refinement
    contract for a finite history, not a proof that gameplay satisfies it.
    Steps end after a complete writer outcome; transient negatives before a
    clamp are deliberately not exposed as useful seeds. *)
From Coq Require Import List Reals ZArith Lra.
From compcert Require Import AST Clight ClightBigstep Floats Globalenvs Integers Maps Memory Values.
From Flocq Require Import Binary.
From LessThanOneAPress.Proofs Require Import GameTypes InputSemantics
  InkMovingBackwardSource InkLandingExecution InkNegativeDepthBackward
  JPBinary32DepthWrites ObjectContactNecessity SelectedClightTarget
  ZeroAQuicksandEntryBoundary LongJumpProvenanceBoundary.
Import ListNotations.
Local Open Scope Z_scope.

Definition InkPhysicalAPress (inputs : list FrameInput) : Prop :=
  exists input, In input inputs /\
    a_button_pressed (frame_current_down input) (frame_previous_down input) = true.

Definition InkPhysicalActionEdges (inputs : list FrameInput)
    (events : list action_event) : Prop :=
  forall event, In event events -> event_has_a_edge event = true ->
    InkPhysicalAPress inputs.

Definition InkLegitimateLongJumpHistory (inputs : list FrameInput) : Prop :=
  exists initial events,
    non_long_jump_target initial /\
    source_action_trace initial events act_long_jump_land /\
    no_forged_action_installs events /\
    InkPhysicalActionEdges inputs events.

Lemma isc_legitimate_long_jump_has_physical_a : forall inputs,
  InkLegitimateLongJumpHistory inputs -> InkPhysicalAPress inputs.
Proof.
  intros inputs [initial [events [Hinitial [Htrace [Hclean Hphysical]]]]].
  assert (Htarget : long_jump_target act_long_jump_land) by (right; reflexivity).
  pose proof (first_target_occurrence_requires_edge_or_forgery
    initial events act_long_jump_land Htrace Hinitial Htarget) as Hsome.
  apply Exists_exists in Hsome.
  destruct Hsome as [event [Hin [Hedge | Hforged]]].
  - exact (Hphysical event Hin Hedge).
  - unfold no_forged_action_installs in Hclean.
    rewrite Forall_forall in Hclean.
    specialize (Hclean event Hin). congruence.
Qed.

(** An explicit execution of the generated US/JP landing store.  The stock
    duration gate and the legitimate action/input prefix are assumptions
    about that execution, not conclusions of the source inventory. *)
Definition InkClassifiedLandingWrite (inputs : list FrameInput)
    (before after : float32) : Prop :=
  exists kind version e le m mb mo timer t le' m' out,
    le ! IMB._m = Some (Vptr mb mo) /\
    Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle before) /\
    Mem.load Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 26))) = Some (Vint timer) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (imb_landing_write version) t le' m' out /\
    Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle after) /\
    is_finite 24 128 after = true /\
    stock_landing_body_runs kind (Int.unsigned timer) /\
    (kind = StockLongJumpLand -> InkLegitimateLongJumpHistory inputs).

Inductive InkClassifiedDepthHistory (inputs : list FrameInput) :
    float32 -> float32 -> Prop :=
| ISCEmpty : forall depth, InkClassifiedDepthHistory inputs depth depth
| ISCSafe : forall before middle after,
    JPBinary32SafeDepthWriterOutcome before middle ->
    InkClassifiedDepthHistory inputs middle after ->
    InkClassifiedDepthHistory inputs before after
| ISCLanding : forall before middle after,
    InkClassifiedLandingWrite inputs before middle ->
    InkClassifiedDepthHistory inputs middle after ->
    InkClassifiedDepthHistory inputs before after.

Lemma isc_landing_nonnegative_or_a : forall inputs before after,
  InkClassifiedLandingWrite inputs before after ->
  JPBinary32FiniteNonnegative before ->
  JPBinary32FiniteNonnegative after \/ InkPhysicalAPress inputs.
Proof.
  intros inputs before after Hlanding Hbefore.
  destruct Hlanding as (kind & version & e & le & m & mb & mo & timer & t &
    le' & m' & out & Hm & Hd & Ht & Hrun & Ha & Hfinite & Hgate & Hhistory).
  destruct (Rle_dec 0 (B2R 24 128 after)) as [Hnonnegative | Hnegative].
  - left. split; assumption.
  - right.
    assert (Hlt : (B2R 24 128 after < 0)%R) by lra.
    pose proof (imb_actual_negative_landing_with_stock_gate_requires_long_jump
      kind version e le m mb mo before timer t le' m' out after
      Hm Hd Ht Hrun Ha Hbefore Hfinite Hlt Hgate) as [Hkind Htimer].
    apply isc_legitimate_long_jump_has_physical_a. exact (Hhistory Hkind).
Qed.

Lemma isc_classified_history_nonnegative_or_a : forall inputs before after,
  InkClassifiedDepthHistory inputs before after ->
  JPBinary32FiniteNonnegative before ->
  JPBinary32FiniteNonnegative after \/ InkPhysicalAPress inputs.
Proof.
  intros inputs before after Hhistory. induction Hhistory; intros Hbefore.
  - left; exact Hbefore.
  - apply IHHhistory.
    exact (jp_binary32_safe_writer_outcome_preserves_nonnegative _ _ Hbefore H).
  - destruct (isc_landing_nonnegative_or_a _ _ _ H Hbefore) as [Hmiddle | Ha].
    + exact (IHHhistory Hmiddle).
    + right; exact Ha.
Qed.

Definition InkStockSeedConditionalBoundary : Prop :=
  forall inputs before after,
    InkClassifiedDepthHistory inputs before after ->
    JPBinary32FiniteNonnegative before ->
    (B2R 24 128 after < 0)%R ->
    InkPhysicalAPress inputs.

Theorem isc_useful_negative_seed_requires_physical_a :
  InkStockSeedConditionalBoundary.
Proof.
  intros inputs before after Hhistory Hbefore Hnegative.
  destruct (isc_classified_history_nonnegative_or_a _ _ _ Hhistory Hbefore)
    as [[Hfinite Hnonnegative] | Ha]; [exfalso; lra | exact Ha].
Qed.

Corollary isc_no_a_excludes_classified_negative_seed : forall inputs before after,
  InkClassifiedDepthHistory inputs before after ->
  JPBinary32FiniteNonnegative before ->
  fewer_than_one_a_press inputs ->
  ~ (B2R 24 128 after < 0)%R.
Proof.
  intros inputs before after Hhistory Hbefore Hno Hnegative.
  destruct (isc_useful_negative_seed_requires_physical_a
    inputs before after Hhistory Hbefore Hnegative) as [input [Hin Ha]].
  unfold fewer_than_one_a_press in Hno. rewrite Forall_forall in Hno.
  specialize (Hno input Hin). unfold frame_has_no_a_press in Hno. congruence.
Qed.
