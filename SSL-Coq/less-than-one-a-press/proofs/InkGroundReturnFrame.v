(** Complete the real post-refresh angle setter and ground return.  Its
    local allocation, three short stores and free cannot touch the movement,
    cached-floor, display or collision cells.  The quarter loop and terrain
    sound call precede this reached cut and are not framed here. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_math_util jp_math_util.
From LessThanOneAPress.Proofs Require Import GameTypes Area2GroundVectorSetSource Area2Rank12BContact
  InkGroundBackwardSource InkGroundCallBackward InkGroundDisplayBackward InkPostDialogGroundReset
  InkCopyEntry InkCopyCaller InkCopyCompletion InkRawCopyStores InkBackwardSource InkBackwardExecution
  InkFloorResetSource InkFloorResetExecution ObjectContactNecessity
  ContactConsumerExecution SecretContactExecution OrdinaryArea1EntryMemory
  EyerokRank15LiveMovement SelectedClightTarget UpperElevatorQueryResolution
  ContactConsumerSource CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IGR := us_math_util.

Definition igr_set_body version := match version with
| VersionUS => us_math_util.f_vec3s_set
| VersionJP => jp_math_util.f_vec3s_set end.
Lemma igr_set_us_source :
  nth_error IGR.global_definitions
    (ueqr_definition_index IGR._vec3s_set IGR.global_definitions) =
  Some (IGR._vec3s_set, Gfun (Internal (igr_set_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma igr_set_us_member :
  In (IGR._vec3s_set, Gfun (Internal (igr_set_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 30 us_units).
  - exact (us_nlist_at_nIn _ 30 us_units).
  - eapply nth_error_In. exact igr_set_us_source.
Qed.

Lemma igr_set_us_selection :
  us_normalized_global_definition_map ! IGR._vec3s_set =
    Some (Gfun (Internal (igr_set_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact igr_set_us_member.
Qed.
Lemma igr_set_us_no_repair :
  us_selected_definition_needs_viewport_repair
    (IGR._vec3s_set, Gfun (Internal (igr_set_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma igr_set_us_selected :
  In (IGR._vec3s_set, Gfun (Internal (igr_set_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite igr_set_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact igr_set_us_selection.
Qed.
Lemma igr_set_jp_source :
  (prog_defmap (nlist_at 30 jp_cleaned_units)) ! IGR._vec3s_set =
    Some (Gfun (Internal (igr_set_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem igr_selected_set_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IGR._vec3s_set = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (igr_set_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact igr_set_us_selected.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 30 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 30 jp_cleaned_units).
    + exact igr_set_jp_source.
Qed.

Definition igr_init := Sassign (Evar IGR._dest (tptr tshort))
  (Etempvar IGR._dest (tptr tshort)).
Definition igr_index id n := Ederef (Ebinop Oadd (Etempvar id (tptr tshort))
  (Econst_int (Int.repr n) tint) (tptr tshort)) tshort.
Definition igr_stage version n := ibk_head
  (rank12b_drop_sequences (S n) (fn_body (igr_set_body version))).
Definition igr_return version := rank12b_drop_sequences 4 (fn_body (igr_set_body version)).
Definition igr_temp n := match n with O => IGR._t'3 | S O => IGR._t'2 | _ => IGR._t'1 end.
Definition igr_value n := match n with O => IGR._x | S O => IGR._y | _ => IGR._z end.

Lemma igr_generated_body : forall version,
  fn_vars (igr_set_body version) = [(IGR._dest,tptr tshort)] /\
  fn_params (igr_set_body version) =
    [(IGR._dest,tptr tshort);(IGR._x,tshort);(IGR._y,tshort);(IGR._z,tshort)] /\
  fn_body (igr_set_body version) = Ssequence igr_init
    (Ssequence (igr_stage version 0) (Ssequence (igr_stage version 1)
      (Ssequence (igr_stage version 2) (igr_return version)))) /\
  igr_return version = Sreturn (Some (Eaddrof
    (Evar IGR._dest (tptr tshort)) (tptr (tptr tshort)))).
Proof. intros []; repeat split; reflexivity. Qed.
Lemma igr_generated_stage : forall version n, (n < 3)%nat ->
  igr_stage version n = Ssequence
    (Sset (igr_temp n) (Evar IGR._dest (tptr tshort)))
    (Sassign (igr_index (igr_temp n) (Z.of_nat n)) (Etempvar (igr_value n) tshort)) /\
  ibk_normal (igr_stage version n) = true.
Proof. intros [] [|[|[|n]]] Hn; try lia; split; reflexivity. Qed.

Lemma igr_actual_entry : forall version ge destination x y z m e le entry,
  function_entry2 ge (igr_set_body version) [destination;x;y;z] m e le entry ->
  exists local, Mem.alloc m 0 (sizeof ge (tptr tshort)) = (entry,local) /\
    e = PTree.set IGR._dest (local,tptr tshort) empty_env /\
    le ! IGR._dest = Some destination.
Proof.
  intros version ge destination x y z m e le entry Hentry.
  destruct (igr_generated_body version) as (Hvars & Hparams & _).
  inversion Hentry; subst; clear Hentry.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ [] _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    rewrite Hparams in Hb; cbn in Hb; inversion Hb; subst temps end.
  eexists. repeat split; eauto.
  repeat rewrite PTree.gso by discriminate. apply PTree.gss.
Qed.

Lemma igr_init_store : forall ge e le m local db dp t le' after out,
  e ! IGR._dest = Some (local,tptr tshort) ->
  le ! IGR._dest = Some (Vptr db dp) ->
  ocn_exec ge e le m igr_init t le' after out ->
  Mem.store Mint32 m local 0 (Vptr db dp) = Some after.
Proof.
  intros ge e le m local db dp t le' after out Hlocal Htemp Hrun.
  unfold igr_init in Hrun. inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ Hlocal Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vptr db dp) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast (Vptr db dp) _ _ _ = Some ?v |- _ =>
    change (Some (Vptr db dp) = Some v) in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  assumption.
Qed.

Lemma igr_pointer_local_read : forall ge e le m local db dp value,
  e ! IGR._dest = Some (local,tptr tshort) ->
  Mem.load Mint32 m local 0 = Some (Vptr db dp) ->
  eval_expr ge e le m (Evar IGR._dest (tptr tshort)) value -> value = Vptr db dp.
Proof.
  intros ge e le m local db dp value Hlocal Hload Hr. inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ Hlocal Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hread : Mem.loadv _ _ _ = Some value |- _ =>
    change (Mem.load Mint32 m local 0 = Some value) in Hread; congruence end.
Qed.

Lemma igr_index_location : forall ge e le m id n db dp b offset bf,
  le ! id = Some (Vptr db dp) ->
  eval_lvalue ge e le m (igr_index id n) b offset bf ->
  b = db /\ offset = Ptrofs.add dp
    (Ptrofs.mul (Ptrofs.repr 2) (ptrofs_of_int Signed (Int.repr n))) /\ bf = Full.
Proof.
  intros ge e le m id n db dp b offset bf Htemp Hl.
  unfold igr_index in Hl. inversion Hl; subst.
  match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion Hr; subst; clear Hr end.
  - match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vptr db dp) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hr; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn in Hsem; inversion Hsem; subst end.
    repeat split; reflexivity.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Lemma igr_stage_store : forall version n ge e le m local db dp t le' after out,
  (n < 3)%nat -> e ! IGR._dest = Some (local,tptr tshort) ->
  Mem.load Mint32 m local 0 = Some (Vptr db dp) ->
  ocn_exec ge e le m (igr_stage version n) t le' after out ->
  exists written, Mem.store Mint16signed m db
    (Ptrofs.unsigned (Ptrofs.add dp (Ptrofs.mul (Ptrofs.repr 2)
      (ptrofs_of_int Signed (Int.repr (Z.of_nat n)))))) written = Some after.
Proof.
  intros version n ge e le m local db dp t le' after out Hn Hlocal Hload Hrun.
  rewrite (proj1 (igr_generated_stage version n Hn)) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ (Evar IGR._dest _) ?v |- _ =>
    assert (v = Vptr db dp) by (eapply igr_pointer_local_read; eauto); subst v end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ ?temps ?memory (igr_index (igr_temp n) _) _ _ _ |- _ =>
    destruct (igr_index_location ge e temps memory (igr_temp n) (Z.of_nat n) db dp _ _ _
      (PTree.gss _ _ _) Hl) as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  eexists; eassumption.
Qed.

Definition igr_outside_angles (ob : block) slot chunk (b : block) offset :=
  b <> ob \/ offset + size_chunk chunk <= object_slot_offset slot + 26 \/
    object_slot_offset slot + 32 <= offset.
Lemma igr_object_offset : forall slot n,
  (slot < object_pool_capacity)%nat -> (n < 3)%nat ->
  Ptrofs.unsigned (Ptrofs.add
    (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 26))
    (Ptrofs.mul (Ptrofs.repr 2) (ptrofs_of_int Signed (Int.repr (Z.of_nat n))))) =
    object_slot_offset slot + 26 + 2*Z.of_nat n.
Proof.
  intros slot n Hslot Hn.
  replace (Ptrofs.mul (Ptrofs.repr 2) (ptrofs_of_int Signed (Int.repr (Z.of_nat n))))
    with (Ptrofs.repr (2*Z.of_nat n)) by (destruct n as [|[|[|n]]]; try lia; reflexivity).
  rewrite Ptrofs.add_assoc.
  replace (Ptrofs.add (Ptrofs.repr 26) (Ptrofs.repr (2*Z.of_nat n)))
    with (Ptrofs.repr (26+2*Z.of_nat n)) by (destruct n as [|[|[|n]]]; try lia; reflexivity).
  rewrite irc_slot_address; [lia|exact Hslot|lia].
Qed.

Theorem igr_complete_short_setter_frames_positions :
  forall version m ob slot x y z t after result,
  (slot < object_pool_capacity)%nat -> Mem.valid_block m ob ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (igr_set_body version))
    [Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 26));x;y;z]
    t after result ->
  forall chunk b offset, Mem.valid_block m b -> igr_outside_angles ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk m b offset.
Proof.
  intros version m ob slot x y z t after result Hslot Hobject Hcall.
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (igr_actual_entry _ _ _ _ _ _ _ _ _ _ He)
      as (local & Halloc & -> & Hdest) end.
  assert (local <> ob) as Hseparate by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
  destruct (igr_generated_body version) as (_ & _ & Hbody & HreturnShape).
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_sequence _ _ _ _ igr_init _ _ _ _ _ eq_refl Hr)
      as (init_le & init_m & init_t & rest_t & Htrace & Hinit & Hrest) end.
  pose proof (igr_init_store _ _ _ _ local ob _ _ _ _ _
    (PTree.gss _ _ _) Hdest Hinit) as HinitStore.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (igr_generated_stage version 0 ltac:(lia))) Hrest)
    as (x_le & x_m & x_t & yz_t & Hxt & Hx & Hyz).
  destruct (igr_stage_store version 0 _ _ _ _ local ob _ _ _ _ _ ltac:(lia)
    (PTree.gss _ _ _) (Mem.load_store_same _ _ _ _ _ _ HinitStore) Hx) as [xvalue Hxs].
  rewrite igr_object_offset in Hxs by auto; cbn [Z.of_nat] in Hxs.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (igr_generated_stage version 1 ltac:(lia))) Hyz)
    as (y_le & y_m & y_t & zr_t & Hyt & Hy & Hzr).
  assert (Mem.load Mint32 x_m local 0 = Some
    (Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 26)))) as HlocalX.
  { erewrite Mem.load_store_other;
      [exact (Mem.load_store_same _ _ _ _ _ _ HinitStore)|exact Hxs|left; congruence]. }
  destruct (igr_stage_store version 1 _ _ _ _ local ob _ _ _ _ _ ltac:(lia)
    (PTree.gss _ _ _) HlocalX Hy) as [yvalue Hys].
  rewrite igr_object_offset in Hys by auto; cbn [Z.of_nat] in Hys.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (igr_generated_stage version 2 ltac:(lia))) Hzr)
    as (z_le & z_m & z_t & return_t & Hzt & Hz & Hreturn).
  assert (Mem.load Mint32 y_m local 0 = Some
    (Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 26)))) as HlocalY.
  { erewrite Mem.load_store_other; [exact HlocalX|exact Hys|left; congruence]. }
  destruct (igr_stage_store version 2 _ _ _ _ local ob _ _ _ _ _ ltac:(lia)
    (PTree.gss _ _ _) HlocalY Hz) as [zvalue Hzs].
  rewrite igr_object_offset in Hzs by auto; cbn [Z.of_nat] in Hzs.
  rewrite HreturnShape in Hreturn. inversion Hreturn; subst.
  lazymatch goal with Hfree : Mem.free_list ?before (blocks_of_env _ _) = Some ?answer |- _ =>
    change (Mem.free_list before [(local,0,4)] = Some answer) in Hfree;
    cbn [Mem.free_list] in Hfree;
    destruct (Mem.free before local 0 4) as [freed|] eqn:HfreeOne; try discriminate;
    inversion Hfree; subst end.
  intros chunk b offset Hvalid Houtside.
  assert (b <> local) as Hfresh by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
  erewrite Mem.load_free; [|exact HfreeOne|left; congruence].
  erewrite Mem.load_store_other; [|exact Hzs|unfold igr_outside_angles in Houtside; cbn [size_chunk]; lia].
  erewrite Mem.load_store_other; [|exact Hys|unfold igr_outside_angles in Houtside; cbn [size_chunk]; lia].
  erewrite Mem.load_store_other; [|exact Hxs|unfold igr_outside_angles in Houtside; cbn [size_chunk]; lia].
  erewrite Mem.load_store_other; [|exact HinitStore|left; congruence].
  eapply Mem.load_alloc_unchanged; eauto.
Qed.

Definition igr_ground_angle version := ibk_head (igb_tail version).
Definition igr_after_angle version := rank12b_drop_sequences 4 (fn_body (igb_body version)).
Definition igr_ground_object := Ederef
  (Etempvar IFR._t'4 (tptr (Tstruct IFR._Object noattr))) (Tstruct IFR._Object noattr).
Definition igr_ground_header := Efield igr_ground_object IFR._header (Tstruct IFR._ObjectNode noattr).
Definition igr_ground_graphics := Efield igr_ground_header IFR._gfx (Tstruct IFR._GraphNodeObject noattr).
Definition igr_ground_angles := Efield igr_ground_graphics IFR._angle (tarray tshort 3).
Definition igr_ground_angle_call := Scall None
  (Evar IFR._vec3s_set (Tfunction [tptr tshort;tshort;tshort;tshort] (tptr tvoid) cc_default))
  [igr_ground_angles;Econst_int Int.zero tint;Etempvar IFR._t'5 tshort;Econst_int Int.zero tint].

Lemma igr_ground_tail_source : forall version,
  igb_tail version = Ssequence (igr_ground_angle version) (igr_after_angle version) /\
  igr_ground_angle version = Ssequence (Sset IFR._t'4 ibk_object_read)
    (Ssequence
      (Sset IFR._t'5 (Ederef (Ebinop Oadd
        (Efield ibcc_state IFR._faceAngle (tarray tshort 3))
        (Econst_int (Int.repr 1) tint) (tptr tshort)) tshort)) igr_ground_angle_call) /\
  ibk_normal (igr_ground_angle version) = true /\
  cce_readonly_keep IFR._m (igr_after_angle version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma igr_selected_angle_field : forall version,
  ibcc_field_ok (genv_cenv (Clight.globalenv (selected_clight_target version)))
    IFR._GraphNodeObject IFR._angle 26 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IFR._GraphNodeObject IFR._angle 26 = true).
  rewrite <- rank15_selected_header_environment_exact. destruct version; vm_compute; reflexivity.
Qed.

Lemma igr_ground_angle_address : forall version e le m ob oo answer,
  le ! IFR._t'4 = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    igr_ground_angles answer -> answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 26)).
Proof.
  intros version e le m ob oo answer Hobject Hr.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & _).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m igr_ground_object v -> v = Vptr ob oo) as Hobj
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m igr_ground_header v -> v = Vptr ob oo) as Hhead.
  { intros v Hread. pose proof (ibcc_aggregate_field _ _ _ _ igr_ground_object
      IFR._Object IFR._header (Tstruct IFR._ObjectNode noattr) ob oo 0 v
      eq_refl Hobj Hheader (or_intror eq_refl) Hread) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m igr_ground_graphics v -> v = Vptr ob oo) as Hgraph.
  { intros v Hread. pose proof (ibcc_aggregate_field _ _ _ _ igr_ground_header
      IFR._ObjectNode IFR._gfx (Tstruct IFR._GraphNodeObject noattr) ob oo 0 v
      eq_refl Hhead Hgfx (or_intror eq_refl) Hread) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  exact (ibcc_aggregate_field _ _ _ _ igr_ground_graphics
    IFR._GraphNodeObject IFR._angle (tarray tshort 3) ob oo 26 answer
    eq_refl Hgraph (igr_selected_angle_field version) (or_introl eq_refl) Hr).
Qed.

Lemma igr_actual_ground_angle_frames : forall version e le m mb ob slot t le' after out,
  (slot < object_pool_capacity)%nat -> Mem.valid_block m ob ->
  e ! IFR._vec3s_set = None -> le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (igr_ground_angle version) t le' after out ->
  forall chunk b offset, Mem.valid_block m b -> igr_outside_angles ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk m b offset.
Proof.
  intros version e le m mb ob slot t le' after out Hslot Hobject Hlocal Hm Hobj Hrun.
  rewrite (proj1 (proj2 (igr_ground_tail_source version))) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?v |- _ =>
    assert (v = Vptr ob (Ptrofs.repr (object_slot_offset slot))) by
      (eapply ibcc_actual_object_read; eauto); subst v end.
  all: try contradiction.
  destruct (igr_selected_set_resolves version) as (fb & Hsymbol & Hfun).
  match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _ igr_ground_angle_call _ _ _ _ |- _ =>
    unfold igr_ground_angle_call in Hcall; inversion Hcall; subst; clear Hcall end.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  pose proof (igr_ground_angle_address version e
    (PTree.set IFR._t'5 v (PTree.set IFR._t'4
      (Vptr ob (Ptrofs.repr (object_slot_offset slot))) le)) m2 ob
    (Ptrofs.repr (object_slot_offset slot)) v1
    ltac:(rewrite PTree.gso by discriminate; apply PTree.gss) H6) as Haddress.
  subst v1.
  match goal with Hcast : sem_cast (Vptr ob _) _ _ _ = Some ?v |- _ =>
    change (Some (Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 26))) = Some v)
      in Hcast; inversion Hcast; subst end.
  eapply igr_complete_short_setter_frames_positions; [exact Hslot|exact Hobject|eassumption].
Qed.

Theorem igr_post_refresh_tail_frames_positions : forall version e le m mb ob slot t le' after out,
  (slot < object_pool_capacity)%nat -> Mem.valid_block m ob ->
  e ! IFR._vec3s_set = None -> le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (igb_tail version) t le' after out ->
  forall chunk b offset, Mem.valid_block m b -> igr_outside_angles ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk m b offset.
Proof.
  intros version e le m mb ob slot t le' after out Hslot Hobject Hlocal Hm Hobj Hrun.
  destruct (igr_ground_tail_source version) as (Hbody & _ & Hnormal & Hreadonly).
  rewrite Hbody in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suffix & Htrace & Hangle & Hrest).
  pose proof (proj1 (proj2 (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrest Hreadonly))) as Hsame.
  subst after. eapply igr_actual_ground_angle_frames; eauto.
Qed.

Lemma igr_ground_entry_has_fresh_local : forall version ge m mb e le entry,
  function_entry2 ge (igb_body version) [Vptr mb Ptrofs.zero] m e le entry ->
  exists local, Mem.alloc m 0 (sizeof ge (tarray tfloat 3)) = (entry,local) /\
    e = PTree.set IFR._intendedPos (local,tarray tfloat 3) empty_env.
Proof.
  intros version ge m mb e le entry He.
  destruct (igb_source_cuts version) as (Hvars & _).
  inversion He; subst; clear He.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ [] _ _ |- _ => inversion Ha; subst; clear Ha end.
  eexists. split; eauto.
Qed.

Definition InkGroundReturnedPositionFrame : Prop :=
  forall version start mb e entry_le entry_m refreshed_le refreshed ob slot
      t last_le last_m out after,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat -> Mem.valid_block start ob ->
  function_entry2 ge (igb_body version) [Vptr mb Ptrofs.zero]
    start e entry_le entry_m ->
  Mem.valid_block refreshed ob ->
  refreshed_le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 refreshed mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec ge e refreshed_le refreshed (igb_tail version) t last_le last_m out ->
  Mem.free_list last_m (blocks_of_env ge e) = Some after ->
  forall chunk b offset, Mem.valid_block start b -> Mem.valid_block refreshed b ->
    igr_outside_angles ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk refreshed b offset.

Theorem igr_actual_ground_return_keeps_refreshed_positions : InkGroundReturnedPositionFrame.
Proof.
  unfold InkGroundReturnedPositionFrame. cbn zeta.
  intros version start mb e entry_le entry_m refreshed_le refreshed ob slot
    t last_le last_m out after Hslot Hstart Hentry Hvalid Hm Hobject Htail Hfree.
  destruct (igr_ground_entry_has_fresh_local _ _ _ _ _ _ _ Hentry) as (local & Halloc & ->).
  assert ((PTree.set IFR._intendedPos (local,tarray tfloat 3) empty_env) ! IFR._vec3s_set = None)
    as Hname by (rewrite PTree.gso by discriminate; apply PTree.gempty).
  pose proof (igr_post_refresh_tail_frames_positions version _ refreshed_le refreshed mb ob slot
    t last_le last_m out Hslot Hvalid Hname Hm Hobject Htail) as Hframe.
  change (Mem.free_list last_m [(local,0,12)] = Some after) in Hfree.
  cbn [Mem.free_list] in Hfree.
  destruct (Mem.free last_m local 0 12) as [freed|] eqn:HfreeOne; try discriminate.
  inversion Hfree; subst after.
  intros chunk b offset Hbefore Hnow Houtside.
  assert (b <> local) as Hfresh by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
  erewrite Mem.load_free; [apply Hframe; assumption|exact HfreeOne|left; congruence].
Qed.

Theorem igr_ground_return_position_checked : InkGroundReturnedPositionFrame.
Proof. exact igr_actual_ground_return_keeps_refreshed_positions. Qed.

(** Compose the completed real display copy with the reached real return
    tail.  The cut height is after quarter steps; the cached floor may be
    different.  No condition says those two heights agree. *)
Theorem igr_refresh_and_return_keep_the_cut_heights :
  forall version start mb ob slot height floor e entry_le entry_m
    cut_le cut_m copy_t copy_le copy_m tail_t last_le last_m out returned,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat -> mb <> ob ->
  Mem.valid_block start mb -> Mem.valid_block start ob -> Mem.valid_block cut_m ob ->
  function_entry2 ge (igb_body version) [Vptr mb Ptrofs.zero]
    start e entry_le entry_m ->
  cut_le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 cut_m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 cut_m mb 64 = Some (Vsingle height) ->
  Mem.load Mfloat32 cut_m mb 112 = Some (Vsingle floor) ->
  ocn_exec ge e cut_le cut_m (igb_refresh version) copy_t copy_le copy_m Out_normal ->
  ocn_exec ge e copy_le copy_m (igb_tail version) tail_t last_le last_m out ->
  Mem.free_list last_m (blocks_of_env ge e) = Some returned ->
  Mem.load Mfloat32 returned mb 64 = Some (Vsingle height) /\
  Mem.load Mfloat32 returned mb 112 = Some (Vsingle floor) /\
  Mem.load Mfloat32 returned ob (object_slot_offset slot + 36) = Some (Vsingle height).
Proof.
  cbn zeta.
  intros version start mb ob slot height floor e entry_le entry_m
    cut_le cut_m copy_t copy_le copy_m tail_t last_le last_m out returned
    Hslot Hsep HstartM HstartO HcutO Hentry Hm Hobject Hheight Hfloor Hcopy Htail Hfree.
  destruct (igb_entry_keeps_argument _ _ _ _ _ _ _ Hentry) as [_ Hname].
  destruct (ipg_ground_refresh_completes_without_old_display version e cut_le cut_m
    mb ob slot height copy_t copy_le copy_m Out_normal Hslot Hsep HcutO Hname
    Hm Hobject Hheight Hcopy) as [Hdisplay HcopyFrame].
  assert (Mem.load Mfloat32 copy_m mb 64 = Some (Vsingle height)) as HcopiedM.
  { rewrite HcopyFrame; [exact Hheight|eapply ibcc_loaded_block_valid; eauto|
      unfold icp_outside_display; left; exact Hsep]. }
  assert (Mem.load Mfloat32 copy_m mb 112 = Some (Vsingle floor)) as HcopiedFloor.
  { rewrite HcopyFrame; [exact Hfloor|eapply ibcc_loaded_block_valid; eauto|
      unfold icp_outside_display; left; exact Hsep]. }
  assert (Mem.load Mint32 copy_m mb 136 = Some
    (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HcopiedObject.
  { rewrite HcopyFrame; [exact Hobject|eapply ibcc_loaded_block_valid; eauto|
      unfold icp_outside_display; left; exact Hsep]. }
  assert (copy_le ! IFR._m = Some (Vptr mb Ptrofs.zero)) as HcopyM.
  { rewrite (cce_argument_temporary_is_preserved _ _ _ _ _ _ _ _ _ IFR._m Hcopy
      ltac:(destruct version; reflexivity)). exact Hm. }
  assert (Mem.valid_block copy_m ob) as HcopyO by (eapply ibcc_loaded_block_valid; eauto).
  assert (Mem.valid_block copy_m mb) as HcopyState by (eapply ibcc_loaded_block_valid; eauto).
  pose proof (igr_actual_ground_return_keeps_refreshed_positions version start mb e
    entry_le entry_m copy_le copy_m ob slot tail_t last_le last_m out returned
    Hslot HstartO Hentry HcopyO HcopyM HcopiedObject Htail Hfree) as HreturnFrame.
  repeat split.
  - rewrite HreturnFrame; [exact HcopiedM|exact HstartM|exact HcopyState|
      unfold igr_outside_angles; left; exact Hsep].
  - rewrite HreturnFrame; [exact HcopiedFloor|exact HstartM|exact HcopyState|
      unfold igr_outside_angles; left; exact Hsep].
  - rewrite HreturnFrame; [exact Hdisplay|exact HstartO|exact HcopyO|
      unfold igr_outside_angles; right; right; cbn; lia].
Qed.
