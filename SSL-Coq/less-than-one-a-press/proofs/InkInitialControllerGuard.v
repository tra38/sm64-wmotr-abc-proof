(** The initial physical-sample reading is carried through preparation to
    the actual A-pressed guard.  The complete-button result is instantiated
    at that same reached call, not at a separately chosen controller state. *)
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes ClightRefinement InputSemantics
  InkBackwardSource InkBodyResetConstruction InkActionPassStart InkActionPassHistory
  InkAcceptedInitialStorage InkInputSharedConstruction InkScheduledSharedHistory InkSharedReadings
  InkControllerSource InkControllerEdge InkMarioInputFlag InkControllerBackward InkButtonTailFrame
  ObjectContactNecessity DefaultArea1StartBoundary OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition icg_after_temps le cb pressed := PTree.set IBM._t'21 (Vint pressed)
  (PTree.set IBM._t'20 (Vptr cb Ptrofs.zero) le).

Lemma icg_construct_no_edge_guard : forall version m le mb cb pressed,
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 156 = Some (Vptr cb Ptrofs.zero) ->
  Mem.load Mint16unsigned m cb 18 = Some (Vint pressed) ->
  Int.testbit pressed 15 = false ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ics_mario_a version) E0 (icg_after_temps le cb pressed) m Out_normal.
Proof.
  intros version m le mb cb pressed Hm Hcontroller Hpressed Hclear.
  destruct (ice_selected_fields version) as (_ & _ & Hpf & _ & Hcf & _).
  destruct (ics_source_cuts version) as (_ & _ & _ & Hshape & _). rewrite Hshape.
  unfold icg_after_temps.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_Sset. eapply ibc_field_read with (delta := 156) (chunk := Mint32);
      [exact Hm|exact Hcf|reflexivity|exact Hcontroller].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply ibc_field_read with (delta := 18) (chunk := Mint16unsigned);
        [apply PTree.gss|exact Hpf|reflexivity|exact Hpressed].
    + eapply exec_Sifthenelse with (v1 := Vint (Int.and pressed (Int.repr 32768))) (b := false).
      * eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|constructor|reflexivity].
      * assert (Int.and pressed (Int.repr 32768) = Int.zero) as Hmask
          by (apply (imf_single_bit_mask_clear pressed 15); [lia|exact Hclear]).
        rewrite Hmask. reflexivity.
      * apply exec_Sskip.
Qed.

Lemma icg_call_passes_no_edge_guard : forall version m mb cb pressed k,
  Mem.load Mint32 m mb 156 = Some (Vptr cb Ptrofs.zero) ->
  Mem.load Mint16unsigned m cb 18 = Some (Vint pressed) ->
  Int.testbit pressed 15 = false ->
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (ics_body version ICButtons)) [Vptr mb Ptrofs.zero] k m) E0
    (State (ics_body version ICButtons) (ics_mario_tail version) k empty_env
      (icg_after_temps (iih_entry_temps version ICButtons mb) cb pressed) m).
Proof.
  intros version m mb cb pressed k Hcontroller Hpressed Hclear.
  eapply star_left; [apply step_internal_function; apply iih_entry; right; reflexivity| |reflexivity].
  rewrite (proj1 (proj2 (proj2 (ics_source_cuts version)))).
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_trans.
  - eapply iap_normal_statement_steps. eapply icg_construct_no_edge_guard;
      [apply PTree.gss|exact Hcontroller|exact Hpressed|exact Hclear].
  - apply star_one. apply step_skip_seq.
  - reflexivity.
Qed.

Definition InkInitialControllerGuardConstruction : Prop :=
  forall version m world previous current body k,
  DefaultArea1StartBoundary version (selected_clight_target version) m world previous current ->
  InkAcceptedInitialStorage version m (default_area1_entry_addresses world) body ->
  InkAcceptedInitialInputStorage m (default_area1_entry_addresses world) ->
  let a := default_area1_entry_addresses world in
  exists (run : ImportedClightRun) after button_k ready,
    run_program run = selected_clight_target version /\
    run_start run = Callstate (Internal (iap_body version))
      [object_slot_pointer a (area1_mario_slot a)] k m /\ run_trace run = E0 /\
    run_final run = State (ics_body version ICButtons) (ics_mario_tail version)
      button_k empty_env ready after /\
    InkSameReadings a m after /\ InkInitialProducerReadings after a /\
    Mem.load Mint16unsigned after (area1_state_storage_block a) 2 = Some (Vint Int.zero) /\
    (exists cut : InkRunCut run,
      ink_cut_state run cut = Callstate (Internal (ics_body version ICButtons))
        [Vptr (area1_state_storage_block a) Ptrofs.zero] button_k after /\
      ink_cut_before run cut = E0 /\ ink_cut_after run cut = E0) /\
    (forall t final result,
      ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
        after (Internal (ics_body version ICButtons)) [Vptr (area1_state_storage_block a) Ptrofs.zero]
        t final result ->
      exists input, Mem.load Mint16unsigned final (area1_state_storage_block a) 2 = Some (Vint input) /\
        Int.and input (Int.repr 2) = Int.zero /\ t = E0) /\
    (forall t last final out,
      ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env ready after
        (ics_mario_tail version) t last final out ->
      Mem.load Mfloat32 final (area1_state_storage_block a) 192 =
        Mem.load Mfloat32 after (area1_state_storage_block a) 192 /\
      Mem.load Mint32 final (area1_state_storage_block a) 12 =
        Mem.load Mint32 after (area1_state_storage_block a) 12 /\
      Mem.load Mint16unsigned final (area1_state_storage_block a) 26 =
        Mem.load Mint16unsigned after (area1_state_storage_block a) 26).

Theorem icg_initial_history_passes_real_a_guard : InkInitialControllerGuardConstruction.
Proof.
  intros version m world previous current body k Hstart Hstorage Hinput. cbn zeta.
  set (a := default_area1_entry_addresses world) in *.
  destruct (iih_accepted_initial_action_reaches_buttons version m world previous current body k
    Hstart Hstorage Hinput)
    as (prefix & after & button_k & Hp & Hs & Ht & Hf & Hframe & Hinitial & Hzero & Hcontroller & Hpressed & Hclear).
  pose proof (icg_call_passes_no_edge_guard version after (area1_state_storage_block a)
    (area1_controller_storage_block a) (edge_pressed current previous) button_k
    Hcontroller Hpressed Hclear) as Hsteps.
  destruct (ish_append_actual_run _ _ _ _ _ Hp Hf Hsteps)
    as (joined & Hjp & Hjs & Hjt & Hjf & Hcut).
  exists joined, after, button_k,
    (icg_after_temps (iih_entry_temps version ICButtons (area1_state_storage_block a))
      (area1_controller_storage_block a) (edge_pressed current previous)).
  split; [exact Hjp|]. split; [rewrite Hjs; exact Hs|].
  split; [rewrite Hjt, Ht; reflexivity|]. split; [exact Hjf|].
  split; [exact Hframe|]. split; [exact Hinitial|]. split; [exact Hzero|]. split.
  - destruct Hcut as (cut & Hcs & Hct & Hcu). exists cut.
    split; [rewrite Hcs; exact Hf|]. split; [rewrite Hct; exact Ht|exact Hcu].
  - split.
    + intros t final result Hcall.
      eapply icb_actual_button_call_no_a with (mo := Ptrofs.zero)
        (cb := area1_controller_storage_block a) (co := Ptrofs.zero)
        (pressed := edge_pressed current previous) (result := result).
      * change (200 <= 4294967295). lia.
      * exact Hzero.
      * exact Hcontroller.
      * exact Hpressed.
      * exact Hclear.
      * exact Hcall.
    + intros t last final out Htail.
      eapply ibt_actual_button_tail_keeps_depth_action_timer; [|exact Htail].
      unfold icg_after_temps, iih_entry_temps.
      repeat rewrite PTree.gso by discriminate. apply PTree.gss.
Qed.
