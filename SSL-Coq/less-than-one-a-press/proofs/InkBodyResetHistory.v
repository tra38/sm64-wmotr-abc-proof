(** Join the checked body reset to the already constructed action prefix.
    The actual next-stage execution is used, not a blanket helper frame.
    Scheduling the call and establishing the live body reference remain
    explicit entry/history obligations. *)
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkActionPassStart InkActionPassHistory
  InkActionVisibilityFrame InkBodyResetFrame InkBodyResetResolution InkSharedReadings
  ObjectContactNecessity SecretContactExecution SelectedClightTarget ClightRefinement
  EntryMemory OrdinaryArea1EntryMemory DefaultArea1StartBoundary EyerokRank15LiveMovement.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ibr_call_temp version := match version with
| VersionUS => IBM._t'47 | VersionJP => IBM._t'43 end.
Definition ibr_call_statement version := Scall None
  (Evar IBM._mario_reset_bodystate
    (Tfunction [tptr (Tstruct IBM._MarioState noattr)] tvoid cc_default))
  [Etempvar (ibr_call_temp version) (tptr (Tstruct IBM._MarioState noattr))].
Definition ibr_call_stage version := Ssequence
  (Sset (ibr_call_temp version) ias_global) (ibr_call_statement version).
Definition ibr_after_reset version := match ias_after_visibility version with
| Ssequence _ rest => rest | _ => Sskip end.

Lemma ibr_stage_source : forall version,
  ias_after_visibility version = Ssequence (ibr_call_stage version) (ibr_after_reset version).
Proof. intros []; reflexivity. Qed.

(** Authenticate the named State fields underlying the shared byte reads.
    Vector components use the accepted position record at offsets 60/64/68. *)
Definition ibr_shared_state_layout version :=
  forallb (fun entry => ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState (fst entry) (snd entry))
    [(IBM._action, 12); (IBM._prevAction, 16); (IBM._actionState, 24);
     (IBM._actionTimer, 26); (IBM._actionArg, 28); (IBM._framesSinceA, 40);
     (IBM._pos, 60); (IBM._wall, 96); (IBM._ceil, 100); (IBM._floor, 104);
     (IBM._ceilHeight, 108); (IBM._floorHeight, 112); (IBM._marioObj, 136);
     (IBM._marioBodyState, 152); (IBM._controller, 156); (IBM._quicksandDepth, 192)].

Lemma ibr_shared_state_layout_checked : forall version, ibr_shared_state_layout version = true.
Proof.
  intro version. unfold ibr_shared_state_layout.
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Lemma ibr_global_read_value : forall (ge : genv) le m cell mb answer,
  Genv.find_symbol ge IBM._gMarioState = Some cell ->
  Mem.load Mint32 m cell 0 = Some (Vptr mb Ptrofs.zero) ->
  eval_expr ge empty_env le m ias_global answer -> answer = Vptr mb Ptrofs.zero.
Proof.
  intros ge le m cell mb answer Hsymbol Hload Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl; subst end;
    try discriminate.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ (Vptr ?loc _) = Some _ |- _ =>
    assert (loc = cell) by congruence; subst loc;
    change (Mem.load Mint32 m cell 0 = Some answer) in Hr; congruence end.
Qed.


Lemma ibr_actual_stage_calls_reset : forall version le m cell mb t le' m' out,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState = Some cell ->
  Mem.load Mint32 m cell 0 = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ibr_call_stage version) t le' m' out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m (Internal (ibr_body version))
    [Vptr mb Ptrofs.zero] t m' result.
Proof.
  intros version le m cell mb t le' m' out Hsymbol Hglobal Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset (ibr_call_temp version) ias_global)
    _ _ _ _ _ eq_refl Hrun) as (middle & memory & first & last & Htrace & Hread & Hcall).
  inversion Hread; subst; clear Hread.
  match goal with Hr : eval_expr ?ge _ ?temps ?memory ias_global ?v |- _ =>
    pose proof (ibr_global_read_value ge temps memory cell mb v Hsymbol Hglobal Hr) as -> end.
  unfold ibr_call_statement in Hcall. inversion Hcall; subst; clear Hcall.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (ibr_selected_reset_resolves version) as (fb & Hfs & Hff).
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar ?id (Tfunction ?args ?result ?cc)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory id args result cc fb vf
        eq_refl Hfs Hr)); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hff in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hargs : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Hargs; subst; clear Hargs end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vptr mb Ptrofs.zero) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  eexists; eassumption.
Qed.

Lemma ibr_slot_flag_offset : forall a,
  area1_entry_slots_valid a ->
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (mario_object_base a)) (Ptrofs.repr 2)) =
    mario_object_base a + 2.
Proof.
  intros a [Hslot _]. apply Nat2Z.inj_lt in Hslot.
  assert (145919 <= Ptrofs.max_unsigned) as Hmax.
  { destruct Archi.ptr64 eqn:Hptr; unfold Ptrofs.max_unsigned.
    - rewrite (Ptrofs.modulus_eq64 Hptr). change (145919 <= 18446744073709551615). lia.
    - rewrite (Ptrofs.modulus_eq32 Hptr). change (145919 <= 4294967295). lia. }
  assert (0 <= mario_object_base a /\ mario_object_base a + 2 <= Ptrofs.max_unsigned) as Hbase.
  { unfold mario_object_base, object_slot_offset, object_size, object_pool_capacity in *.
    pose proof (Nat2Z.is_nonneg (area1_mario_slot a)). nia. }
  unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (mario_object_base a)) by lia.
  rewrite (Ptrofs.unsigned_repr 2) by lia.
  apply Ptrofs.unsigned_repr. lia.
Qed.

Lemma ibr_visibility_shared_frame : forall version a le m t le' m' out,
  area1_entry_slots_valid a -> area1_state_storage_block a <> area1_object_pool_block a ->
  le ! (ias_o1 version) = Some (object_slot_pointer a (area1_mario_slot a)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ias_flag_frontier version) t le' m' out -> InkSameReadings a m m'.
Proof.
  intros version a le m t le' m' out Hslots Hseparate Hobject Hrun.
  destruct (iav_first_graphical_store_exact _ _ _ _ _ _ _ _ _ _ Hobject Hrun)
    as [value Hstore].
  change (Mem.store Mint16signed m (area1_object_pool_block a)
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (mario_object_base a)) (Ptrofs.repr 2))) value = Some m')
    in Hstore.
  rewrite (ibr_slot_flag_offset a Hslots) in Hstore.
  intros cell Hin. eapply ibr_single_store_frames; [exact Hstore|].
  destruct (ink_shared_cells_regions a cell Hin) as [[Hb Ho]|[Hb Ho]];
    unfold ibr_cell_disjoint.
  - left. congruence.
  - right; right. cbn [size_chunk]. lia.
Qed.

(** The two completed stages share a memory endpoint and form one genuine
    small-step extension. The result transports all 24 observations, including
    the cached floor inputs, not only quicksand depth. It does not identify a
    later quarter-step query's new floor with that cached floor. *)
Theorem ibr_visibility_then_reset_shared_extension :
  forall version a global_cell body bo le m t1 le1 m1 t2 le2 m2 k,
  area1_entry_slots_valid a ->
  area1_state_storage_block a <> area1_object_pool_block a ->
  global_cell <> area1_object_pool_block a ->
  body <> area1_state_storage_block a -> body <> area1_object_pool_block a ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState = Some global_cell ->
  Mem.load Mint32 m global_cell 0 = Some (Vptr (area1_state_storage_block a) Ptrofs.zero) ->
  Mem.load Mint32 m (area1_state_storage_block a) 152 = Some (Vptr body bo) ->
  le ! (ias_o1 version) = Some (object_slot_pointer a (area1_mario_slot a)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ias_flag_frontier version) t1 le1 m1 Out_normal ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le1 m1
    (ibr_call_stage version) t2 le2 m2 Out_normal ->
  InkSameReadings a m m2 /\
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (iap_body version) (ias_flag_frontier version)
      (Kseq (ias_after_visibility version) k) empty_env le m)
    (t1 ++ t2)
    (State (iap_body version) (ibr_after_reset version) k empty_env le2 m2).
Proof.
  intros version a global_cell body bo le m t1 le1 m1 t2 le2 m2 k
    Hslots Hstatepool Hglobalpool Hbodystate Hbodypool Hsymbol Hglobal Hbody Hobject Hvisibility Hreset.
  pose proof (ibr_visibility_shared_frame _ _ _ _ _ _ _ _ Hslots Hstatepool Hobject Hvisibility)
    as Hvisibilityframe.
  assert (Mem.load Mint32 m1 global_cell 0 = Some (Vptr (area1_state_storage_block a) Ptrofs.zero)) as Hglobal1.
  { rewrite (iav_first_graphical_store_preserves_other_blocks _ _ _ _ _ _ _ _ _ _
      Hobject Hvisibility Mint32 global_cell 0 Hglobalpool). exact Hglobal. }
  assert (Mem.load Mint32 m1 (area1_state_storage_block a) 152 = Some (Vptr body bo)) as Hbody1.
  { rewrite (iav_first_graphical_store_preserves_other_blocks _ _ _ _ _ _ _ _ _ _
      Hobject Hvisibility Mint32 (area1_state_storage_block a) 152 Hstatepool). exact Hbody. }
  destruct (ibr_actual_stage_calls_reset _ _ _ _ _ _ _ _ _ Hsymbol Hglobal1 Hreset) as [result Hcall].
  destruct (ibr_completed_reset_preserves_shared_readings _ _ _ _ _ _ _ _
    Hstatepool Hbodystate Hbodypool Hbody1 Hcall) as [_ Hresetframe].
  split; [eapply ink_same_readings_trans; eauto|].
  eapply star_trans.
  - eapply iap_normal_statement_steps. exact Hvisibility.
  - eapply star_left; [apply step_skip_seq| |reflexivity].
    rewrite ibr_stage_source.
    eapply star_left; [apply step_seq| |reflexivity].
    eapply star_trans.
    + eapply iap_normal_statement_steps. exact Hreset.
    + eapply star_left; [apply step_skip_seq|apply star_refl|reflexivity].
    + unfold Eapp; rewrite ?app_nil_r; reflexivity.
  - unfold Eapp; rewrite ?app_nil_r; reflexivity.
Qed.

(** This extends the same call built from the accepted memory. It does not
    strengthen DefaultArea1StartBoundary with an unproved body pointer, or
    assert that the real scheduler has selected this call. *)
Definition InkSharedActionPrefixConstruction : Prop :=
  forall version m world previous current k,
  DefaultArea1StartBoundary version (selected_clight_target version) m world previous current ->
  let a := default_area1_entry_addresses world in
  exists (prefix : ImportedClightRun) ready,
    ibr_shared_state_layout version = true /\
    run_program prefix = selected_clight_target version /\
    run_start prefix = Callstate (Internal (iap_body version))
      [object_slot_pointer a (area1_mario_slot a)] k m /\
    run_trace prefix = E0 /\
    run_final prefix = State (iap_body version) (ias_flag_frontier version)
      (Kseq (ias_after_visibility version) (Kseq (ias_return version) k)) empty_env ready m /\
    forall body bo t1 le1 m1 t2 le2 m2,
    body <> area1_state_storage_block a -> body <> area1_object_pool_block a ->
    Mem.load Mint32 m (area1_state_storage_block a) 152 = Some (Vptr body bo) ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env ready m
      (ias_flag_frontier version) t1 le1 m1 Out_normal ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le1 m1
      (ibr_call_stage version) t2 le2 m2 Out_normal ->
    exists joined : ImportedClightRun,
      run_program joined = selected_clight_target version /\
      run_start joined = run_start prefix /\ run_trace joined = t1 ++ t2 /\
      run_final joined = State (iap_body version) (ibr_after_reset version)
        (Kseq (ias_return version) k) empty_env le2 m2 /\
      InkSameReadings a m m2 /\ InkInitialProducerReadings m2 a.

Theorem ibr_accepted_call_extends_through_body_reset : InkSharedActionPrefixConstruction.
Proof.
  intros version m world previous current k Hstart. cbn zeta.
  destruct (ias_boundary_constructs_action_call_start version m world previous current k Hstart)
    as (prefix & ready & function_block & Hfs & Hff & Hprogram & Hfirst & Htrace & Hfinal &
      Hobject & Hobject2 & Hdepth).
  exists prefix, ready.
  split; [apply ibr_shared_state_layout_checked|].
  split; [exact Hprogram|]. split; [exact Hfirst|]. split; [exact Htrace|].
  split; [exact Hfinal|].
  intros body bo t1 le1 m1 t2 le2 m2 Hbodystate Hbodypool Hbody Hvisibility Hreset.
  pose proof (default_area1_start_entry_memory _ _ _ _ _ _ Hstart) as Hmemory.
  pose proof (default_area1_world_entry_symbols _ _ _
    (default_area1_start_symbol_bindings _ _ _ _ _ _ Hstart)) as Hsymbols.
  assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioState =
    Some (area1_state_pointer_cell_block (default_area1_entry_addresses world))) as Hsymbol.
  { destruct version; [exact (us_area1_state_pointer_symbol _ _ Hsymbols)|
      exact (jp_area1_state_pointer_symbol _ _ Hsymbols)]. }
  assert (Genv.find_symbol (Clight.globalenv (selected_clight_target version)) UOL._gObjectPool =
    Some (area1_object_pool_block (default_area1_entry_addresses world))) as Hpoolsymbol.
  { destruct version; [exact (us_area1_object_pool_symbol _ _ Hsymbols)|
      exact (jp_area1_object_pool_symbol _ _ Hsymbols)]. }
  assert (area1_state_storage_block (default_area1_entry_addresses world) <>
    area1_object_pool_block (default_area1_entry_addresses world)) as Hstatepool.
  { destruct version.
    - exact (proj1 (proj2 (us_area1_entry_storage_blocks_pairwise_distinct _ _ Hsymbols))).
    - exact (proj1 (proj2 (jp_area1_entry_storage_blocks_pairwise_distinct _ _ Hsymbols))). }
  assert (area1_state_pointer_cell_block (default_area1_entry_addresses world) <>
    area1_object_pool_block (default_area1_entry_addresses world)) as Hglobalpool.
  { eapply Genv.global_addresses_distinct with
      (id1 := IBM._gMarioState) (id2 := UOL._gObjectPool);
      [discriminate|exact Hsymbol|exact Hpoolsymbol]. }
  destruct (ibr_visibility_then_reset_shared_extension version (default_area1_entry_addresses world)
    (area1_state_pointer_cell_block (default_area1_entry_addresses world)) body bo ready m
    t1 le1 m1 t2 le2 m2 (Kseq (ias_return version) k)
    (ordinary_area1_slots_valid _ _ _ _ _ _ Hmemory) Hstatepool Hglobalpool Hbodystate Hbodypool
    Hsymbol (ordinary_area1_state_global_pointer _ _ _ _ _ _ Hmemory)
    Hbody Hobject Hvisibility Hreset) as [Hframe Hextension].
  pose proof (run_steps prefix) as Hprefix.
  rewrite Hprogram, Hfirst, Htrace, Hfinal in Hprefix.
  assert (star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (iap_body version))
      [object_slot_pointer (default_area1_entry_addresses world)
        (area1_mario_slot (default_area1_entry_addresses world))] k m)
    (t1 ++ t2)
    (State (iap_body version) (ibr_after_reset version) (Kseq (ias_return version) k)
      empty_env le2 m2)) as Hwhole.
  { eapply star_trans; [exact Hprefix|exact Hextension|reflexivity]. }
  exists {| run_program := selected_clight_target version;
    run_start := Callstate (Internal (iap_body version))
      [object_slot_pointer (default_area1_entry_addresses world)
        (area1_mario_slot (default_area1_entry_addresses world))] k m;
    run_trace := t1 ++ t2;
    run_final := State (iap_body version) (ibr_after_reset version)
      (Kseq (ias_return version) k) empty_env le2 m2;
    run_steps := Hwhole |}.
  split; [reflexivity|]. split; [symmetry; exact Hfirst|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hframe|].
  eapply ink_same_readings_keep_initial_producers; [exact Hframe|].
  exact (ink_accepted_start_initializes_both_producers _ _ _ _ _ Hstart).
Qed.
