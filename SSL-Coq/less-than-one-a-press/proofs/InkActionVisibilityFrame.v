(** The first action-pass store is a graphical flag update, not a depth
    producer. Its object reference comes from the constructed call prefix. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkActionPassStart
  InkActionPassHistory InkBackwardSource InkBackwardExecution InkCopyCaller
  ObjectContactNecessity EyerokRank15LiveMovement SelectedClightTarget
  DefaultArea1StartBoundary OrdinaryArea1EntryMemory EntryMemory ClightRefinement.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition iav_object temp := Ederef (Etempvar temp (tptr (Tstruct IBM._Object noattr)))
  (Tstruct IBM._Object noattr).
Definition iav_header temp := Efield (iav_object temp) IBM._header (Tstruct IBM._ObjectNode noattr).
Definition iav_gfx temp := Efield (iav_header temp) IBM._gfx (Tstruct IBM._GraphNodeObject noattr).
Definition iav_node temp := Efield (iav_gfx temp) IBM._node (Tstruct IBM._GraphNode noattr).
Definition iav_flags temp := Efield (iav_node temp) IBM._flags tshort.
Definition iav_read_temp version := match version with
| VersionUS => IBM._t'52 | VersionJP => IBM._t'48 end.
Definition iav_write_rhs version := match ias_flag_frontier version with
| Ssequence _ (Sassign _ rhs) => rhs | _ => Econst_int Int.zero tint end.

Lemma iav_source : forall version,
  ias_flag_frontier version = Ssequence
    (Sset (iav_read_temp version) (iav_flags (ias_o2 version)))
    (Sassign (iav_flags (ias_o1 version)) (iav_write_rhs version)).
Proof. intros []; reflexivity. Qed.

Lemma iav_layout : forall version,
  let ce := prog_comp_env (selected_clight_target version) in
  ibcc_field_ok ce IBM._Object IBM._header 0 = true /\
  ibcc_field_ok ce IBM._ObjectNode IBM._gfx 0 = true /\
  ibcc_field_ok ce IBM._GraphNodeObject IBM._node 0 = true /\
  ibcc_field_ok ce IBM._GraphNode IBM._flags 2 = true.
Proof.
  intro version. cbn zeta. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Lemma iav_zero_field : forall ge e le m base tag field ty b ofs answer,
  typeof base = Tstruct tag noattr ->
  (forall v, eval_expr ge e le m base v -> v = Vptr b ofs) ->
  ibcc_field_ok ge tag field 0 = true -> access_mode ty = By_copy ->
  eval_expr ge e le m (Efield base field ty) answer -> answer = Vptr b ofs.
Proof.
  intros ge e le m base tag field ty b ofs answer Hty Hbase Hfield Hmode Hread.
  pose proof (ibcc_aggregate_field _ _ _ _ _ _ _ _ _ _ _ _
    Hty Hbase Hfield (or_intror Hmode) Hread) as H.
  rewrite Ptrofs.add_zero in H. exact H.
Qed.

Lemma iav_node_read : forall version e le m temp pool ofs answer,
  le ! temp = Some (Vptr pool ofs) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m (iav_node temp) answer ->
  answer = Vptr pool ofs.
Proof.
  intros version e le m temp pool ofs answer Htemp Hread.
  destruct (iav_layout version) as (Hheader & Hgfx & Hnode & Hflags).
  eapply (iav_zero_field (Clight.globalenv (selected_clight_target version)) e le m
    (iav_gfx temp) IBM._GraphNodeObject IBM._node (Tstruct IBM._GraphNode noattr) pool ofs answer);
    [reflexivity| |exact Hnode|reflexivity|exact Hread].
  intros v Hv. eapply (iav_zero_field (Clight.globalenv (selected_clight_target version)) e le m
    (iav_header temp) IBM._ObjectNode IBM._gfx (Tstruct IBM._GraphNodeObject noattr) pool ofs v);
    [reflexivity| |exact Hgfx|reflexivity|exact Hv].
  intros v' Hv'. eapply (iav_zero_field (Clight.globalenv (selected_clight_target version)) e le m
    (iav_object temp) IBM._Object IBM._header (Tstruct IBM._ObjectNode noattr) pool ofs v');
    [reflexivity| |exact Hheader|reflexivity|exact Hv'].
  intros v'' Hv''. eapply ibcc_deref_struct; eauto.
Qed.

Theorem iav_first_graphical_store_exact :
  forall version e le m t le' m' out pool ofs,
  le ! (ias_o1 version) = Some (Vptr pool ofs) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ias_flag_frontier version) t le' m' out ->
  exists value, Mem.store Mint16signed m pool
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 2))) value = Some m'.
Proof.
  intros version e le m t le' m' out pool ofs Hobject Hrun.
  rewrite iav_source in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sset (iav_read_temp version) (iav_flags (ias_o2 version))) _ _ _ _ _ eq_refl Hrun)
    as (mid_le & mid_m & pre & suf & Htrace & Hread & Hwrite).
  inversion Hread; subst; clear Hread.
  assert (iav_read_temp version <> ias_o1 version) as Htemp by (destruct version; discriminate).
  inversion Hwrite; subst; clear Hwrite.
  lazymatch goal with Hl : eval_lvalue ?ge ?env ?temps ?memory _ _ _ _ |- _ =>
    assert (forall v, eval_expr ge env temps memory (iav_node (ias_o1 version)) v ->
      v = Vptr pool ofs) as Hnode by
      (intros node_answer Hnode_read;
        eapply (iav_node_read version env temps memory (ias_o1 version) pool ofs node_answer);
        [rewrite PTree.gso by congruence; exact Hobject|exact Hnode_read]);
    destruct (ibcc_field_location ge env temps memory (iav_node (ias_o1 version))
      IBM._GraphNode IBM._flags tshort pool ofs 2 _ _ _ eq_refl Hnode
      (proj2 (proj2 (proj2 (iav_layout version)))) Hl) as (-> & -> & ->)
  end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  eexists; eassumption.
Qed.

Theorem iav_first_graphical_store_preserves_other_blocks :
  forall version e le m t le' m' out pool ofs,
  le ! (ias_o1 version) = Some (Vptr pool ofs) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ias_flag_frontier version) t le' m' out ->
  forall chunk b offset, b <> pool -> Mem.load chunk m' b offset = Mem.load chunk m b offset.
Proof.
  intros version e le m t le' m' out pool ofs Hobject Hrun chunk b offset Hdistinct.
  destruct (iav_first_graphical_store_exact _ _ _ _ _ _ _ _ _ _ Hobject Hrun)
    as [value Hstore].
  eapply Mem.load_store_other; [exact Hstore|left; congruence].
Qed.

(** The write case is attached to the exact endpoint constructed above,
    rather than to a second independently chosen Mario snapshot. *)
Definition InkActionStartFirstWrite : Prop :=
  forall version memory world previous current k,
  DefaultArea1StartBoundary version (selected_clight_target version)
    memory world previous current ->
  let addresses := default_area1_entry_addresses world in
  let object := object_slot_pointer addresses (area1_mario_slot addresses) in
  exists (run : ImportedClightRun) ready,
    run_program run = selected_clight_target version /\
    run_start run = Callstate (Internal (iap_body version)) [object] k memory /\
    run_trace run = E0 /\
    run_final run = State (iap_body version) (ias_flag_frontier version)
      (Kseq (ias_after_visibility version) (Kseq (ias_return version) k))
      empty_env ready memory /\
    forall t le' m' out,
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env ready memory
      (ias_flag_frontier version) t le' m' out ->
    iap_depth m' (area1_state_storage_block addresses) = Some (Vsingle positive_f32_zero).

Theorem iav_constructed_start_excludes_first_flag_store_seed : InkActionStartFirstWrite.
Proof.
  unfold InkActionStartFirstWrite.
  intros version memory world previous current k Hstart. cbn zeta.
  destruct (ias_boundary_constructs_action_call_start version memory world previous current k Hstart)
    as (run & ready & function_block & Hsymbol & Hfunction & Hprogram & Hstartpoint &
      Htrace & Hfinal & Hobject & Hobject2 & Hzero).
  exists run, ready.
  split; [exact Hprogram|]. split; [exact Hstartpoint|].
  split; [exact Htrace|]. split; [exact Hfinal|].
  intros t le' m' out Hwrite.
  pose proof (default_area1_world_entry_symbols _ _ _
    (default_area1_start_symbol_bindings _ _ _ _ _ _ Hstart)) as Hsymbols.
  assert (area1_state_storage_block (default_area1_entry_addresses world) <>
    area1_object_pool_block (default_area1_entry_addresses world)) as Hseparate.
  { destruct version.
    - exact (proj1 (proj2 (us_area1_entry_storage_blocks_pairwise_distinct _ _ Hsymbols))).
    - exact (proj1 (proj2 (jp_area1_entry_storage_blocks_pairwise_distinct _ _ Hsymbols))). }
  unfold iap_depth.
  rewrite (iav_first_graphical_store_preserves_other_blocks version empty_env ready memory
    t le' m' out (area1_object_pool_block (default_area1_entry_addresses world))
    (Ptrofs.repr (object_slot_offset (area1_mario_slot (default_area1_entry_addresses world))))
    Hobject Hwrite Mfloat32 (area1_state_storage_block (default_area1_entry_addresses world))
    mario_state_quicksand_depth_offset Hseparate).
  exact Hzero.
Qed.
