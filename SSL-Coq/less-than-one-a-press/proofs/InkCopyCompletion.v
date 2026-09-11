(** Complete the ordinary movement-to-display copy, not just its Y store.
    These are cuts of the generated US/JP vec3f_copy.  The local allocation,
    all three component stores, return, and local free are accounted for.
    No incoming display height or speed bound is needed. *)
From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyEntry InkCopyCaller InkRawCopyStores
  OrdinaryArea1EntryMemory ObjectContactNecessity ContactConsumerExecution
  Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Inductive icp_axis := ICPX | ICPY | ICPZ.
Definition icp_number axis : Z := match axis with ICPX => 0 | ICPY => 1 | ICPZ => 2 end.
Definition icp_dest_temp axis := match axis with
  ICPX => IBV._t'5 | ICPY => IBV._t'3 | ICPZ => IBV._t'1 end.
Definition icp_value_temp axis := match axis with
  ICPX => IBV._t'6 | ICPY => IBV._t'4 | ICPZ => IBV._t'2 end.
Definition icp_stage version axis := ibk_head
  (rank12b_drop_sequences (match axis with ICPX => 1 | ICPY => 2 | ICPZ => 3 end)
    (fn_body (ibk_copy_body version))).
Definition icp_return version := rank12b_drop_sequences 4 (fn_body (ibk_copy_body version)).
Definition icp_offset base axis := Ptrofs.unsigned (Ptrofs.add base
  (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr (icp_number axis))))).

Lemma icp_generated_body : forall version,
  fn_body (ibk_copy_body version) = Ssequence ibc_local_init
    (Ssequence (icp_stage version ICPX)
      (Ssequence (icp_stage version ICPY)
        (Ssequence (icp_stage version ICPZ) (icp_return version)))).
Proof. intros []; reflexivity. Qed.

Lemma icp_generated_stage : forall version axis,
  icp_stage version axis = Ssequence
    (Sset (icp_dest_temp axis) (Evar IBV._dest (tptr tfloat)))
    (Ssequence (Sset (icp_value_temp axis) (ibc_index IBV._src (icp_number axis)))
      (Sassign (ibc_index (icp_dest_temp axis) (icp_number axis))
        (Etempvar (icp_value_temp axis) tfloat))) /\
  ibk_normal (icp_stage version axis) = true.
Proof. intros [] []; split; reflexivity. Qed.

Lemma icp_stage_exact_store : forall version axis ge e le m local db dp sb sp t le' m' out,
  e ! IBV._dest = Some (local, tptr tfloat) ->
  Mem.load Mint32 m local 0 = Some (Vptr db dp) ->
  le ! IBV._src = Some (Vptr sb sp) ->
  ocn_exec ge e le m (icp_stage version axis) t le' m' out ->
  exists read written,
    Mem.load Mfloat32 m sb (icp_offset sp axis) = Some read /\
    sem_cast read tfloat tfloat m = Some written /\
    Mem.store Mfloat32 m db (icp_offset dp axis) written = Some m' /\
    le' ! IBV._src = Some (Vptr sb sp) /\ t = E0 /\ out = Out_normal.
Proof.
  intros version axis ge e le m local db dp sb sp t le' m' out Hlocal Hdest Hsrc Hrun.
  rewrite (proj1 (icp_generated_stage version axis)) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ (Evar IBV._dest _) ?v |- _ =>
    assert (v = Vptr db dp) by (eapply ibc_pointer_local_read; eauto); subst v end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ ?temps _ (ibc_index (icp_dest_temp axis) _) _ _ _ |- _ =>
    assert (temps ! (icp_dest_temp axis) = Some (Vptr db dp)) as Hp by
      (rewrite PTree.gso by (destruct axis; discriminate); apply PTree.gss);
    destruct (ibc_index_location _ _ _ _ _ _ _ _ _ _ _ Hp Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ ?temps _ (ibc_index IBV._src _) ?v |- _ =>
    assert (temps ! IBV._src = Some (Vptr sb sp)) as Hs by
      (rewrite PTree.gso by (destruct axis; discriminate); exact Hsrc);
    pose proof (ibc_float_read _ _ _ _ _ _ _ _ _ Hs Hr) as Hread end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar (icp_value_temp axis) _) ?v |- _ =>
    assert (v = _) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst v end.
  match goal with Hstore : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Hstore; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  do 2 eexists. repeat split; try eassumption; try reflexivity.
  repeat rewrite PTree.gso by (destruct axis; discriminate). exact Hsrc.
Qed.

Lemma icp_object_offset : forall slot axis,
  (slot < object_pool_capacity)%nat ->
  icp_offset (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 32)) axis =
    object_slot_offset slot + 32 + 4 * icp_number axis.
Proof.
  intros slot axis Hslot. unfold icp_offset.
  replace (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr (icp_number axis))))
    with (Ptrofs.repr (4 * icp_number axis)) by (destruct axis; reflexivity).
  rewrite Ptrofs.add_assoc.
  replace (Ptrofs.add (Ptrofs.repr 32) (Ptrofs.repr (4 * icp_number axis)))
    with (Ptrofs.repr (32 + 4 * icp_number axis)) by (destruct axis; reflexivity).
  rewrite irc_slot_address; [lia|exact Hslot|destruct axis; cbn [icp_number]; lia].
Qed.

Definition icp_outside_display (ob : block) slot chunk (b : block) ofs :=
  b <> ob \/ ofs + size_chunk chunk <= object_slot_offset slot + 32 \/
    object_slot_offset slot + 44 <= ofs.

Definition InkCopyCompletedEffect : Prop :=
  forall version m mb ob slot height t m' result,
  (slot < object_pool_capacity)%nat -> mb <> ob -> Mem.valid_block m ob ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Internal (ibk_copy_body version))
    [Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 32));
     Vptr mb (Ptrofs.repr 60)] t m' result ->
  Mem.load Mfloat32 m' ob (object_slot_offset slot + 36) = Some (Vsingle height) /\
  (forall chunk b ofs, Mem.valid_block m b -> icp_outside_display ob slot chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs).

Theorem icp_completed_copy_forgets_old_display : InkCopyCompletedEffect.
Proof.
  unfold InkCopyCompletedEffect.
  intros version m mb ob slot height t m' result Hslot Hseparate Hov Hheight Hcall.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ Hheight) as Hmv.
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_actual_entry _ _ _ _ _ _ _ _ He)
      as (local & Halloc & -> & Hdest & Hsrc) end.
  assert (local <> ob) as Hlo by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
  assert (local <> mb) as Hlm by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite icp_generated_body in Hr;
    destruct (ibk_split_sequence _ _ _ _ ibc_local_init _ _ _ _ _ eq_refl Hr)
      as (init_le & init_m & init_t & rest_t & Htrace & Hinit & Hrest) end.
  destruct (ibc_local_init_store _ _ _ _ _ _ _ _ _ _ (PTree.gss _ _ _) Hdest
    ltac:(do 2 eexists; reflexivity) Hinit) as (HinitStore & -> & -> & _).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (icp_generated_stage version ICPX)) Hrest)
    as (x_le & x_m & x_t & yz_t & Hxt & Hx & Hyz).
  destruct (icp_stage_exact_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) (Mem.load_store_same _ _ _ _ _ _ HinitStore) Hsrc Hx)
    as (xread & xvalue & Hxread & Hxcast & Hxstore & Hxsrc & _).
  rewrite icp_object_offset in Hxstore by exact Hslot.
  cbn [icp_number] in Hxstore.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (icp_generated_stage version ICPY)) Hyz)
    as (y_le & y_m & y_t & zr_t & Hyt & Hy & Hzr).
  assert (Mem.load Mint32 x_m local 0 =
    Some (Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 32)))) as HlocalX.
  { erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ HinitStore)|
      exact Hxstore|left; congruence]. }
  destruct (icp_stage_exact_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) HlocalX Hxsrc Hy)
    as (yread & yvalue & Hyread & Hycast & Hystore & Hysrc & _).
  change (Mem.load Mfloat32 x_m mb 64 = Some yread) in Hyread.
  assert (Mem.load Mfloat32 x_m mb 64 = Some (Vsingle height)) as HsourceY.
  { erewrite Mem.load_store_other; [|exact Hxstore|left; congruence].
    erewrite Mem.load_store_other; [|exact HinitStore|left; congruence].
    erewrite Mem.load_alloc_unchanged; eauto. }
  assert (yread = Vsingle height) by congruence. subst yread.
  cbn in Hycast. inversion Hycast; subst yvalue.
  rewrite icp_object_offset in Hystore by exact Hslot.
  replace (object_slot_offset slot + 32 + 4 * icp_number ICPY)
    with (object_slot_offset slot + 36) in Hystore by (cbn [icp_number]; lia).
  change (Mem.store Mfloat32 x_m ob (object_slot_offset slot + 36)
    (Vsingle height) = Some y_m) in Hystore.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (icp_generated_stage version ICPZ)) Hzr)
    as (z_le & z_m & z_t & return_t & Hzt & Hz & Hreturn).
  assert (Mem.load Mint32 y_m local 0 =
    Some (Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 32)))) as HlocalY.
  { erewrite Mem.load_store_other; [exact HlocalX|exact Hystore|left; congruence]. }
  destruct (icp_stage_exact_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) HlocalY Hysrc Hz)
    as (zread & zvalue & Hzread & Hzcast & Hzstore & _).
  rewrite icp_object_offset in Hzstore by exact Hslot.
  replace (object_slot_offset slot + 32 + 4 * icp_number ICPZ)
    with (object_slot_offset slot + 40) in Hzstore by (cbn [icp_number]; lia).
  change (Mem.store Mfloat32 y_m ob (object_slot_offset slot + 40) zvalue = Some z_m) in Hzstore.
  assert (icp_return version = Sreturn (Some (Eaddrof
    (Evar IBV._dest (tptr tfloat)) (tptr (tptr tfloat))))) as HreturnShape
    by (destruct version; reflexivity).
  rewrite HreturnShape in Hreturn. inversion Hreturn; subst.
  lazymatch goal with Hfree : Mem.free_list ?last_memory (blocks_of_env _ _) = Some ?answer |- _ =>
    change (Mem.free_list last_memory [(local, 0, 4)] = Some answer) in Hfree;
    cbn [Mem.free_list] in Hfree;
    destruct (Mem.free last_memory local 0 4) as [freed|] eqn:HfreeOne; try discriminate;
    inversion Hfree; subst end.
  split.
  - erewrite Mem.load_free; [|exact HfreeOne|left; congruence].
    erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ Hystore)|
      exact Hzstore|right; left; cbn [size_chunk]; lia].
  - intros chunk b ofs Hvalid Houtside.
    assert (b <> local) as Hbl by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
    erewrite Mem.load_free; [|exact HfreeOne|left; congruence].
    erewrite Mem.load_store_other; [|exact Hzstore|unfold icp_outside_display in Houtside;
      cbn [size_chunk]; lia].
    erewrite Mem.load_store_other; [|exact Hystore|unfold icp_outside_display in Houtside;
      cbn [size_chunk]; lia].
    erewrite Mem.load_store_other; [|exact Hxstore|unfold icp_outside_display in Houtside;
      cbn [size_chunk]; lia].
    erewrite Mem.load_store_other; [|exact HinitStore|left; congruence].
    eapply Mem.load_alloc_unchanged; eauto.
Qed.
