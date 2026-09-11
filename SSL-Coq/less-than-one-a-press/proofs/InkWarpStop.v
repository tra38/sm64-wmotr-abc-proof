(** Work backward through the warp's stopping helper. Its real speed setter
    cannot move Mario; the floor snap is followed by a completed display copy.
    The remaining angle call is retained after the checkpoint. Earlier
    animation and later warp/sinking effects are not framed by this result. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank10AGroundPound
  InkBackwardSource InkBackwardExecution InkCopyCaller InkCopyCompletion
  InkFloorResetSource InkFloorResetExecution InkFloorResetCopy InkBodyResetFrame
  InkControllerEdge InkFloorListEffects ObjectContactNecessity
  ContactConsumerExecution SecretContactExecution OrdinaryArea1EntryMemory
  SelectedClightTarget EyerokRank15LiveMovement.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Inductive iws_velocity_cell := IWSForward | IWSSlideX | IWSSlideZ
  | IWSVelX | IWSVelY | IWSVelZ.
Definition iws_velocity_base := Efield ibcc_state IFR._vel (tarray tfloat 3).
Definition iws_velocity_index n := Ederef (Ebinop Oadd iws_velocity_base
  (Econst_int (Int.repr n) tint) (tptr tfloat)) tfloat.
Definition iws_cell_lhs c := match c with
| IWSForward => ibr_field IFR._m IFR._MarioState IFR._forwardVel tfloat
| IWSSlideX => ibr_field IFR._m IFR._MarioState IFR._slideVelX tfloat
| IWSSlideZ => ibr_field IFR._m IFR._MarioState IFR._slideVelZ tfloat
| IWSVelX => iws_velocity_index 0 | IWSVelY => iws_velocity_index 1
| IWSVelZ => iws_velocity_index 2 end.
Definition iws_cell_offset c := match c with
| IWSForward => 84 | IWSSlideX => 88 | IWSSlideZ => 92
| IWSVelX => 72 | IWSVelY => 76 | IWSVelZ => 80 end.

(** This small grammar is checked against the actual setter below. It admits
    only its six named velocity cells and no calls or position writes. *)
Inductive iws_velocity_only : statement -> Prop :=
| iws_vo_assign : forall c rhs, iws_velocity_only (Sassign (iws_cell_lhs c) rhs)
| iws_vo_set : forall id rhs, id <> IFR._m -> iws_velocity_only (Sset id rhs)
| iws_vo_seq : forall a b, iws_velocity_only a -> iws_velocity_only b ->
    iws_velocity_only (Ssequence a b).

Lemma iws_selected_fields : forall version,
  let ce := genv_cenv (Clight.globalenv (selected_clight_target version)) in
  ibcc_field_ok ce IFR._MarioState IFR._forwardVel 84 = true /\
  ibcc_field_ok ce IFR._MarioState IFR._slideVelX 88 = true /\
  ibcc_field_ok ce IFR._MarioState IFR._slideVelZ 92 = true /\
  ibcc_field_ok ce IFR._MarioState IFR._vel 72 = true.
Proof.
  intro version. cbn zeta.
  change (ibcc_field_ok (prog_comp_env (selected_clight_target version)) IFR._MarioState IFR._forwardVel 84 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version)) IFR._MarioState IFR._slideVelX 88 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version)) IFR._MarioState IFR._slideVelZ 92 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version)) IFR._MarioState IFR._vel 72 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Definition iws_stop_speed := Scall None
  (Evar IFR._mario_set_forward_vel (Tfunction
    [tptr (Tstruct IFR._MarioState noattr); tfloat] tvoid cc_default))
  [Etempvar IFR._m (tptr (Tstruct IFR._MarioState noattr));
   Econst_single (Float32.of_bits (Int.repr 0)) tfloat].
Definition iws_stop_vertical := Sassign (iws_cell_lhs IWSVelY)
  (Econst_single (Float32.of_bits (Int.repr 0)) tfloat).

Lemma iws_stop_prefix_source : forall version,
  ifr_prefix version IFRStop = [iws_stop_speed; iws_stop_vertical].
Proof. intros []; reflexivity. Qed.

Lemma iws_velocity_location : forall version e le m mb n b ofs bf,
  le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (iws_velocity_index n) b ofs bf ->
  b = mb /\ ofs = Ptrofs.add (Ptrofs.repr 72)
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr n))) /\ bf = Full.
Proof.
  intros version e le m mb n b ofs bf Hm Hl.
  eapply ifr_array_index_location with (base := iws_velocity_base) (n := n);
    [reflexivity| |exact Hl].
  intros v Hr.
  pose proof (ibcc_aggregate_field
    (Clight.globalenv (selected_clight_target version)) e le m ibcc_state
    IFR._MarioState IFR._vel (tarray tfloat 3) mb Ptrofs.zero 72 v eq_refl
    ltac:(intros; eapply ibcc_deref_struct; eauto)
    (proj2 (proj2 (proj2 (iws_selected_fields version))))
    (or_introl eq_refl) Hr) as H.
  exact H.
Qed.

Lemma iws_velocity_store : forall version c e le m mb rhs t le' m' out,
  le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign (iws_cell_lhs c) rhs) t le' m' out ->
  t = E0 /\ le' = le /\ out = Out_normal /\
  exists v, Mem.store Mfloat32 m mb (iws_cell_offset c) v = Some m'.
Proof.
  intros version c e le m mb rhs t le' m' out Hm Hrun.
  destruct (iws_selected_fields version) as (Hf & Hx & Hz & Hv).
  destruct c.
  1: exact (ibr_field_assignment_store _ _ _ _ _ _ _ tfloat 84 Mfloat32 _ _ _ _ _ _
      Ptrofs.zero Hm Hf eq_refl Hrun).
  1: exact (ibr_field_assignment_store _ _ _ _ _ _ _ tfloat 88 Mfloat32 _ _ _ _ _ _
      Ptrofs.zero Hm Hx eq_refl Hrun).
  1: exact (ibr_field_assignment_store _ _ _ _ _ _ _ tfloat 92 Mfloat32 _ _ _ _ _ _
      Ptrofs.zero Hm Hz eq_refl Hrun).
  all: inversion Hrun; subst; clear Hrun.
  all: match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    first [destruct (iws_velocity_location _ _ _ _ _ 0 _ _ _ Hm Hl) as (-> & -> & ->) |
      destruct (iws_velocity_location _ _ _ _ _ 1 _ _ _ Hm Hl) as (-> & -> & ->) |
      destruct (iws_velocity_location _ _ _ _ _ 2 _ _ _ Hm Hl) as (-> & -> & ->)]
  end.
  all: match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    cbn [typeof iws_cell_lhs iws_velocity_index] in Ha;
    inversion Ha; subst; try discriminate end.
  all: match goal with Hmode : access_mode tfloat = By_value _ |- _ =>
    inversion Hmode; subst end.
  all: repeat split; try reflexivity; eexists; eassumption.
Qed.

Definition iws_outside_velocity (mb : block) chunk b ofs :=
  b <> mb \/ ofs + size_chunk chunk <= 72 \/ 96 <= ofs.

Lemma iws_velocity_only_normal : forall s, iws_velocity_only s -> ibk_normal s = true.
Proof. intros s H; induction H; cbn; auto. now rewrite IHiws_velocity_only1, IHiws_velocity_only2. Qed.

Lemma iws_velocity_only_frame : forall version s, iws_velocity_only s ->
  forall e le m mb t le' m' out,
  le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m s t le' m' out ->
  le' ! IFR._m = Some (Vptr mb Ptrofs.zero) /\ Mem.nextblock m' = Mem.nextblock m /\
  forall chunk b ofs, iws_outside_velocity mb chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version s Hshape. induction Hshape; intros e le m mb t le' m' out Hm Hrun.
  - destruct (iws_velocity_store _ _ _ _ _ _ _ _ _ _ _ Hm Hrun)
      as (_ & -> & _ & v & Hstore). split; [exact Hm|].
    split; [eapply Mem.nextblock_store; exact Hstore|].
    intros chunk b ofs Houtside. eapply Mem.load_store_other; [exact Hstore|].
    unfold iws_outside_velocity in Houtside. destruct c; cbn [iws_cell_offset size_chunk];
      (destruct Houtside as [H|[H|H]]; [left|right; left|right; right]; lia).
  - inversion Hrun; subst. split; [rewrite PTree.gso by congruence; exact Hm|auto].
  - destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
      (iws_velocity_only_normal _ Hshape1) Hrun)
      as (middle & memory & pre & rest & Htrace & Hfirst & Hrest).
    destruct (IHHshape1 _ _ _ _ _ _ _ _ Hm Hfirst) as (Hmiddle & Hnext1 & Hframe1).
    destruct (IHHshape2 _ _ _ _ _ _ _ _ Hmiddle Hrest) as (Hlast & Hnext2 & Hframe2).
    split; [exact Hlast|]. split; [congruence|]. intros. rewrite Hframe2, Hframe1; auto.
Qed.

Lemma iws_speed_source : forall version,
  fn_vars (rank10a_body version GPSetSpeed) = [] /\
  fn_params (rank10a_body version GPSetSpeed) =
    [(IFR._m, tptr (Tstruct IFR._MarioState noattr)); (IFR._forwardVel, tfloat)] /\
  iws_velocity_only (fn_body (rank10a_body version GPSetSpeed)).
Proof.
  intros []; repeat apply conj; try reflexivity;
    cbn [rank10a_body fn_body]; repeat apply iws_vo_seq;
    try (apply iws_vo_set; discriminate).
  all: first [exact (iws_vo_assign IWSForward _) | exact (iws_vo_assign IWSSlideX _) |
    exact (iws_vo_assign IWSSlideZ _) | exact (iws_vo_assign IWSVelX _) |
    exact (iws_vo_assign IWSVelZ _)].
Qed.

Theorem iws_speed_setter_preserves_position : forall version m mb speed t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (rank10a_body version GPSetSpeed)) [Vptr mb Ptrofs.zero; speed] t m' result ->
  Mem.nextblock m' = Mem.nextblock m /\
  forall chunk b ofs, iws_outside_velocity mb chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version m mb speed t m' result Hcall.
  destruct (iws_speed_source version) as (Hvars & Hparams & Hshape).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IFR._m = Some (Vptr mb Ptrofs.zero)) as Hm by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb;
       rewrite PTree.gso by discriminate; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    exact (proj2 (iws_velocity_only_frame _ _ Hshape _ _ _ _ _ _ _ _ Hm Hr)) end.
Qed.

Lemma iws_stop_speed_frame : forall version e le m mb t le' m' out,
  e ! IFR._mario_set_forward_vel = None ->
  le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    iws_stop_speed t le' m' out ->
  le' = le /\ Mem.nextblock m' = Mem.nextblock m /\
  forall chunk b ofs, iws_outside_velocity mb chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version e le m mb t le' m' out Hlocal Hm Hrun.
  destruct (rank10a_selected_bodies_resolve version GPSetSpeed) as (fb & Hsymbol & Hfun).
  unfold iws_stop_speed in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IFR._m _) ?v |- _ =>
    assert (v = Vptr mb Ptrofs.zero) by (eapply ocn_temp_value; eauto); subst v end.
  repeat match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  split; [reflexivity|]. eapply iws_speed_setter_preserves_position; eauto.
Qed.

Lemma iws_stop_prefix_frame : forall version e le m mb t le' m' out,
  e ! IFR._mario_set_forward_vel = None ->
  le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ocn_prepend (ifr_prefix version IFRStop) Sskip) t le' m' out ->
  Mem.nextblock m' = Mem.nextblock m /\
  forall chunk b ofs, iws_outside_velocity mb chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version e le m mb t le' m' out Hlocal Hm Hrun.
  rewrite iws_stop_prefix_source in Hrun. cbn [ocn_prepend] in Hrun.
  destruct (ibk_split_sequence _ _ _ _ iws_stop_speed _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & rest & Htrace & Hspeed & Hrest).
  destruct (iws_stop_speed_frame _ _ _ _ _ _ _ _ _ Hlocal Hm Hspeed)
    as (-> & Hnext & Hframe).
  destruct (ibk_split_sequence _ _ _ _ iws_stop_vertical _ _ _ _ _ eq_refl Hrest)
    as (last & after & a & b & Hab & Hvertical & Hskip).
  inversion Hskip; subst.
  destruct (iws_velocity_store version IWSVelY _ _ _ _ _ _ _ _ _ Hm Hvertical)
    as (_ & _ & _ & v & Hstore).
  split; [rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore); exact Hnext|].
  intros chunk target ofs Houtside. rewrite <- Hframe by exact Houtside.
  eapply Mem.load_store_other; [exact Hstore|].
  unfold iws_outside_velocity in Houtside. cbn [iws_cell_offset size_chunk].
  destruct Houtside as [H|[H|H]]; [left|right; left|right; right]; lia.
Qed.

(** This is an actual completed-call checkpoint: both the horizontal
    position and cached floor come from entry to the stopping helper. The
    remaining angle-setting call is retained verbatim after the checkpoint. *)
Definition iws_before_copy version := ocn_prepend
  (ocn_prefix_items 4 (fn_body (ifr_body version IFRStop))) Sskip.

Lemma iws_before_copy_source : forall version,
  iws_before_copy version = Ssequence (Sset IFR._marioObj ibk_object_read)
    (ocn_prepend (ifr_prefix version IFRStop)
      (Ssequence (ifr_snap version IFRStop) Sskip)).
Proof. intros []; reflexivity. Qed.

Lemma iws_join_prefix : forall ge e items le m pre middle memory rest suffix le' m' out,
  forallb ibk_normal items = true ->
  ocn_exec ge e le m (ocn_prepend items Sskip) pre middle memory Out_normal ->
  ocn_exec ge e middle memory rest suffix le' m' out ->
  ocn_exec ge e le m (ocn_prepend items rest) (pre ++ suffix) le' m' out.
Proof.
  intros ge e items. induction items as [|head tail IH];
    intros le m pre middle memory rest suffix le' m' out Hnormal Hprefix Hrest.
  - inversion Hprefix; subst. exact Hrest.
  - cbn in Hnormal. apply andb_true_iff in Hnormal as [Hhead Htail].
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hhead Hprefix)
      as (first_le & first_m & first_t & rest_t & Htrace & Hfirst & Hfollowing).
    rewrite Htrace, <- app_assoc. cbn [ocn_prepend].
    eapply exec_Sseq_1; [exact Hfirst|]. eapply IH; eauto.
Qed.

Definition InkWarpStopCopyCheckpoint : Prop :=
  forall version m mb ob slot height t m' result,
  (slot < object_pool_capacity)%nat -> mb <> ob -> Mem.valid_block m ob ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle height) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifr_body version IFRStop)) [Vptr mb Ptrofs.zero] t m' result ->
  exists entry_le snap_le snap_m copied copy_le last_le pre copy_t suffix out,
    Mem.load Mfloat32 copied mb 60 = Mem.load Mfloat32 m mb 60 /\
    Mem.load Mfloat32 copied mb 68 = Mem.load Mfloat32 m mb 68 /\
    Mem.load Mfloat32 copied mb 64 = Some (Vsingle height) /\
    Mem.load Mfloat32 copied ob (object_slot_offset slot + 36) = Some (Vsingle height) /\
    function_entry2 (Clight.globalenv (selected_clight_target version))
      (ifr_body version IFRStop) [Vptr mb Ptrofs.zero] m empty_env entry_le m /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
      entry_le m (iws_before_copy version) pre snap_le snap_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
      snap_le snap_m (ifr_copy_call version IFRStop) copy_t copy_le copied Out_normal /\
    t = pre ++ (copy_t ++ suffix) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
      copy_le copied (ifr_after_copy version IFRStop) suffix last_le m' out.

Theorem iws_stop_copies_floor_without_horizontal_departure : InkWarpStopCopyCheckpoint.
Proof.
  unfold InkWarpStopCopyCheckpoint.
  intros version m mb ob slot height t m' result Hslot Hseparate Hvalid Hobj Hheight Hcall.
  destruct (ifr_source_cuts version IFRStop) as (Hvars & Hbody & Htail & _).
  destruct (ifr_prefix_properties version IFRStop) as (Hnormal & HkeepM & HkeepO & Hsnap & Hcopy & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    pose proof He as Hentry_saved; inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IFR._m = Some (Vptr mb Ptrofs.zero)) as Hm by
      (destruct version; cbn in Hb; inversion Hb; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_sequence _ _ _ _ (Sset IFR._marioObj ibk_object_read)
      _ _ _ _ _ eq_refl Hr)
      as (cache_le & cache_m & cache_t & rest_t & Htrace & Hcache & Hrest) end.
  pose proof Hcache as Hcache_saved. inversion Hcache; subst; clear Hcache.
  rename cache_m into m.
  match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?v |- _ =>
    assert (v = Vptr ob (Ptrofs.repr (object_slot_offset slot))) by
      (eapply ibcc_actual_object_read; eauto); subst v end.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (cut_le & cut_m & pre & rest & Hresttrace & Hprefix & Hreset).
  match type of Hprefix with ocn_exec _ _ ?temps ?memory _ _ _ _ _ =>
    destruct (iws_stop_prefix_frame version empty_env temps memory mb _ _ _ _ eq_refl
      ltac:(rewrite PTree.gso by discriminate; exact Hm) Hprefix) as [Hnext Hframe] end.
  assert (cut_le ! IFR._m = Some (Vptr mb Ptrofs.zero)) as HcutM.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepM).
    rewrite PTree.gso by discriminate. exact Hm. }
  assert (cut_le ! IFR._marioObj = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HcutO.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepO). apply PTree.gss. }
  assert (Mem.load Mfloat32 cut_m mb 112 = Some (Vsingle height)) as HcutHeight.
  { rewrite Hframe; [exact Hheight|right; right; lia]. }
  change (ifr_after_prefix version IFRStop) with (ifr_reset_tail version IFRStop) in Hreset.
  rewrite Htail in Hreset.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hsnap Hreset)
    as (snap_le & snap_m & snap_t & after_t & Hsnaptrace & Hsnaprun & Hafter).
  destruct (ifr_snap_writes_floor_height _ _ _ _ _ _ _ _ _ _ _ _ HcutM HcutHeight Hsnaprun)
    as (Hstore & HsnapTemps & _ & _).
  change (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr 64))) with 64 in Hstore.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hcopy Hafter)
    as (copy_le & copied & copy_t & suffix & Hcopytrace & Hcopyrun & Hsuffix).
  destruct (ifrc_copy_calls_real_body version IFRStop empty_env snap_le snap_m
    copy_t copy_le copied Out_normal eq_refl Hcopyrun)
    as (args & answer & Hargs & HrealCopy & _).
  assert (args = [Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 32));
    Vptr mb (Ptrofs.repr 60)]) as Hargvalues.
  { eapply (ifrc_copy_arguments version empty_env snap_le snap_m mb Ptrofs.zero
      ob (Ptrofs.repr (object_slot_offset slot)));
      [rewrite HsnapTemps, PTree.gso by discriminate; exact HcutM|
      rewrite HsnapTemps, PTree.gso by discriminate; exact HcutO|exact Hargs]. }
  subst args.
  assert (Mem.valid_block snap_m ob) as HsnapValid.
  { eapply Mem.store_valid_block_1; [exact Hstore|].
    unfold Mem.valid_block in *. rewrite Hnext. exact Hvalid. }
  destruct (icp_completed_copy_forgets_old_display version snap_m mb ob slot height _ _ _
    Hslot Hseparate HsnapValid (Mem.load_store_same _ _ _ _ _ _ Hstore) HrealCopy)
    as [Hdisplay HcopyFrame].
  match type of Hentry_saved with function_entry2 _ _ _ _ _ ?initial _ =>
    assert (ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
      initial m (iws_before_copy version) (pre ++ snap_t) snap_le snap_m Out_normal) as Hbefore
  end.
  { rewrite iws_before_copy_source.
    replace (pre ++ snap_t) with (E0 ++ (pre ++ (snap_t ++ E0)))
      by (rewrite app_nil_r; reflexivity).
    eapply exec_Sseq_1; [exact Hcache_saved|].
    eapply iws_join_prefix; [exact Hnormal|exact Hprefix|].
    eapply exec_Sseq_1; [exact Hsnaprun|apply exec_Sskip]. }
  match type of Hentry_saved with function_entry2 _ _ _ _ _ ?initial _ =>
    match type of Hsuffix with ocn_exec _ _ _ _ _ _ ?last _ ?o =>
      exists initial, snap_le, snap_m, copied, copy_le, last,
        (pre ++ snap_t), copy_t, suffix, o end end.
  assert (forall ofs, ofs = 60 \/ ofs = 68 ->
    Mem.load Mfloat32 copied mb ofs = Mem.load Mfloat32 m mb ofs) as Hxz.
  { intros ofs [-> | ->]; rewrite HcopyFrame;
      try (eapply ibcc_loaded_block_valid; eapply Mem.load_store_same; exact Hstore);
      try (left; exact Hseparate);
      rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore) by (right; cbn; lia);
      apply Hframe; right; left; cbn; lia. }
  repeat apply conj; try (apply Hxz; auto); try exact Hdisplay; try exact Hsuffix;
    try exact Hentry_saved; try exact Hbefore; try exact Hcopyrun.
  - rewrite HcopyFrame; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|
      eapply ibcc_loaded_block_valid; eapply Mem.load_store_same; exact Hstore|left; exact Hseparate].
  - subst. repeat rewrite app_assoc. reflexivity.
Qed.
