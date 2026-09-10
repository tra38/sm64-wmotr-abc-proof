(** User-authorized normal post-initialization facts used by the Ink proof.
    These are scope-declared INITIAL conditions, not preservation axioms.
    The stock init_mario_from_save_file installs &gBodyStates[0]; the normal
    records have integer flags and writable field storage.  No later value,
    gameplay branch, or absence of a negative-depth producer is granted. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight Clightdefs Ctypes Events Globalenvs Integers
  Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes ClightRefinement
  DefaultArea1StartBoundary OrdinaryArea1EntryMemory SelectedClightTarget
  InkBackwardSource InkActionPassStart InkActionPassHistory InkBodyResetFrame
  InkBodyResetConstruction InkBodyResetHistory InkPreparationConstruction
  InkScheduledSharedHistory InkSharedReadings.
Import ListNotations.
Local Open Scope Z_scope.

Record InkAcceptedInitialStorage version m a body : Prop := {
  ini_body_symbol : Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IBM._gBodyStates = Some body;
  ini_body_reference : Mem.load Mint32 m (area1_state_storage_block a) 152 =
    Some (Vptr body Ptrofs.zero);
  ini_state_flags : exists flags, Mem.load Mint32 m (area1_state_storage_block a) 4 = Some (Vint flags);
  ini_state_flags_writable : Mem.valid_access m Mint32 (area1_state_storage_block a) 4 Writable;
  ini_body_writable : Forall (ibc_access m body) ibr_stores;
  ini_graphical_flags : exists flags, Mem.load Mint16signed m (area1_object_pool_block a)
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (mario_object_base a)) (Ptrofs.repr 2))) =
      Some (Vint flags);
  ini_graphical_flags_writable : Mem.valid_access m Mint16signed (area1_object_pool_block a)
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (mario_object_base a)) (Ptrofs.repr 2))) Writable
}.

(** Separation follows from the actual selected global names.  In particular,
    it is not justified by the informal label "body record" alone. *)
Lemma ini_initial_storage_supplies_preparation : forall version m world previous current body,
  DefaultArea1StartBoundary version (selected_clight_target version) m world previous current ->
  InkAcceptedInitialStorage version m (default_area1_entry_addresses world) body ->
  InkPreparationStorage m (default_area1_entry_addresses world)
    (area1_state_pointer_cell_block (default_area1_entry_addresses world)) body.
Proof.
  intros version m world previous current body Hstart Hstorage.
  pose proof (default_area1_world_entry_symbols _ _ _
    (default_area1_start_symbol_bindings _ _ _ _ _ _ Hstart)) as Hsymbols.
  pose proof (default_area1_start_entry_memory _ _ _ _ _ _ Hstart) as Hmemory.
  set (a := default_area1_entry_addresses world) in *.
  assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) ULU._gMarioStates =
    Some (area1_state_storage_block a)) as Hstate.
  { destruct version; [exact (us_area1_state_storage_symbol _ _ Hsymbols)|
      exact (jp_area1_state_storage_symbol _ _ Hsymbols)]. }
  assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState =
    Some (area1_state_pointer_cell_block a)) as Hglobal.
  { destruct version; [exact (us_area1_state_pointer_symbol _ _ Hsymbols)|
      exact (jp_area1_state_pointer_symbol _ _ Hsymbols)]. }
  assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) UOL._gObjectPool =
    Some (area1_object_pool_block a)) as Hpool.
  { destruct version; [exact (us_area1_object_pool_symbol _ _ Hsymbols)|
      exact (jp_area1_object_pool_symbol _ _ Hsymbols)]. }
  destruct Hstorage as [Hbody Hreference Hflags Hflagsaccess Hbodyaccess Hgfx Hgfxaccess].
  constructor.
  - exact (ordinary_area1_slots_valid _ _ _ _ _ _ Hmemory).
  - eapply Genv.global_addresses_distinct; [|exact Hstate|exact Hpool]. discriminate.
  - eapply Genv.global_addresses_distinct; [|exact Hglobal|exact Hpool]. discriminate.
  - eapply Genv.global_addresses_distinct; [|exact Hglobal|exact Hstate]. discriminate.
  - eapply Genv.global_addresses_distinct; [|exact Hglobal|exact Hbody]. discriminate.
  - eapply Genv.global_addresses_distinct; [|exact Hbody|exact Hpool]. discriminate.
  - constructor; try assumption.
    eapply Genv.global_addresses_distinct; [|exact Hbody|exact Hstate]. discriminate.
  - exact Hgfx.
  - exact Hgfxaccess.
Qed.

(** A fully constructed action-call prefix using the newly accepted initial
    storage, with the caller's continuation retained verbatim.  This does NOT
    replace the surrounding scheduler by repeated independent calls. *)
Definition InkAcceptedInitialActionConstruction : Prop :=
  forall version m world previous current body k,
  DefaultArea1StartBoundary version (selected_clight_target version) m world previous current ->
  InkAcceptedInitialStorage version m (default_area1_entry_addresses world) body ->
  let a := default_area1_entry_addresses world in
  exists (run : ImportedClightRun) after last,
    run_program run = selected_clight_target version /\
    run_start run = Clight.Callstate (Internal (iap_body version))
      [object_slot_pointer a (area1_mario_slot a)] k m /\ run_trace run = E0 /\
    run_final run = Clight.State (iap_body version) (ibr_after_reset version)
      (Clight.Kseq (ias_return version) k) empty_env last after /\
    InkSameReadings a m after /\ InkInitialProducerReadings after a.

Theorem ini_accepted_action_prefix_constructed : InkAcceptedInitialActionConstruction.
Proof.
  intros version m world previous current body k Hstart Hstorage. cbn zeta.
  destruct (ias_boundary_constructs_action_call_start version m world previous current k Hstart)
    as (prefix & ready & fb & Hfs & Hff & Hp & Hs & Ht & Hf & Ho1 & Ho2 & Hdepth).
  pose proof (ini_initial_storage_supplies_preparation _ _ _ _ _ _ Hstart Hstorage) as Hprep.
  pose proof (default_area1_world_entry_symbols _ _ _
    (default_area1_start_symbol_bindings _ _ _ _ _ _ Hstart)) as Hsymbols.
  pose proof (default_area1_start_entry_memory _ _ _ _ _ _ Hstart) as Hmemory.
  assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState =
    Some (area1_state_pointer_cell_block (default_area1_entry_addresses world))) as Hsymbol.
  { destruct version; [exact (us_area1_state_pointer_symbol _ _ Hsymbols)|
      exact (jp_area1_state_pointer_symbol _ _ Hsymbols)]. }
  destruct (ipc_construct_preparation version m _ _ body ready (Clight.Kseq (ias_return version) k)
    Hprep Hsymbol (ordinary_area1_state_global_pointer _ _ _ _ _ _ Hmemory) Ho1 Ho2)
    as (after & last & Hsteps & Hframe & Hglobal & Hvalid).
  destruct (ish_append_actual_run _ _ _ _ _ Hp Hf Hsteps)
    as (joined & Hjp & Hjs & Hjt & Hjf & Hcut).
  exists joined, after, last.
  split; [exact Hjp|]. split; [rewrite Hjs; exact Hs|].
  split; [rewrite Hjt, Ht; reflexivity|]. split; [exact Hjf|]. split; [exact Hframe|].
  eapply ink_same_readings_keep_initial_producers; [exact Hframe|].
  exact (ink_accepted_start_initializes_both_producers _ _ _ _ _ Hstart).
Qed.
