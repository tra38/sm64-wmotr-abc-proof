(** Complete the pre-action retry's display-to-movement copy in one actual
    generated US/JP execution.  All three stores, local allocation and free
    are included; the second query starts in the resulting memory.
    The live identity and incoming display are explicit entry conditions,
    not claims that a controller history has produced them. *)
From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyEntry InkCopyCaller InkCopyCompletion InkRawCopyStores
  OrdinaryArea1EntryMemory ObjectContactNecessity Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma irc_plain_offset : forall base axis,
  0 <= base -> base + 8 <= Ptrofs.max_unsigned ->
  icp_offset (Ptrofs.repr base) axis = base + 4 * icp_number axis.
Proof.
  intros base axis Hlo Hhi. unfold icp_offset.
  replace (Ptrofs.mul (Ptrofs.repr 4)
    (ptrofs_of_int Signed (Int.repr (icp_number axis))))
    with (Ptrofs.repr (4 * icp_number axis)) by (destruct axis; reflexivity).
  rewrite Ptrofs.add_unsigned.
  rewrite (Ptrofs.unsigned_repr base) by lia.
  rewrite (Ptrofs.unsigned_repr (4 * icp_number axis)) by
    (destruct axis; cbn [icp_number]; lia).
  apply Ptrofs.unsigned_repr. destruct axis; cbn [icp_number]; lia.
Qed.

Definition irc_outside_vector (db : block) d chunk (b : block) ofs :=
  b <> db \/ ofs + size_chunk chunk <= d \/ d + 12 <= ofs.

(** A reusable complete-copy lemma, including X and Z, for separate ordinary
    storage.  No bound on speed or on the values being copied is used. *)
Theorem irc_completed_vector_copy :
  forall version ge m db d sb s values t m' result,
  db <> sb -> Mem.valid_block m db ->
  0 <= d -> d + 8 <= Ptrofs.max_unsigned ->
  0 <= s -> s + 8 <= Ptrofs.max_unsigned ->
  (forall axis, Mem.load Mfloat32 m sb (s + 4 * icp_number axis) =
    Some (Vsingle (values axis))) ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (ibk_copy_body version))
    [Vptr db (Ptrofs.repr d); Vptr sb (Ptrofs.repr s)] t m' result ->
  (forall axis, Mem.load Mfloat32 m' db (d + 4 * icp_number axis) =
    Some (Vsingle (values axis))) /\
  (forall chunk b ofs, Mem.valid_block m b -> irc_outside_vector db d chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs).
Proof.
  intros version ge m db d sb s values t m' result Hsep Hdvalid
    Hdlo Hdhi Hslo Hshi Hvalues Hcall.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ (Hvalues ICPX)) as Hsvalid.
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_actual_entry _ _ _ _ _ _ _ _ He)
      as (local & Halloc & -> & Hdest & Hsrc) end.
  assert (local <> db) as Hld by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
  assert (local <> sb) as Hls by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
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
  rewrite irc_plain_offset in Hxread, Hxstore by assumption.
  assert (Mem.load Mfloat32 init_m sb (s + 4 * icp_number ICPX) =
    Some (Vsingle (values ICPX))) as HsourceX.
  { erewrite Mem.load_store_other; [|exact HinitStore|left; congruence].
    erewrite Mem.load_alloc_unchanged; eauto. }
  assert (xread = Vsingle (values ICPX)) by congruence. subst xread.
  cbn in Hxcast. inversion Hxcast; subst xvalue.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (icp_generated_stage version ICPY)) Hyz)
    as (y_le & y_m & y_t & zr_t & Hyt & Hy & Hzr).
  assert (Mem.load Mint32 x_m local 0 = Some (Vptr db (Ptrofs.repr d))) as HlocalX.
  { erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ HinitStore)|
      exact Hxstore|left; congruence]. }
  destruct (icp_stage_exact_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) HlocalX Hxsrc Hy)
    as (yread & yvalue & Hyread & Hycast & Hystore & Hysrc & _).
  rewrite irc_plain_offset in Hyread, Hystore by assumption.
  assert (Mem.load Mfloat32 x_m sb (s + 4 * icp_number ICPY) =
    Some (Vsingle (values ICPY))) as HsourceY.
  { erewrite Mem.load_store_other; [|exact Hxstore|left; congruence].
    erewrite Mem.load_store_other; [|exact HinitStore|left; congruence].
    erewrite Mem.load_alloc_unchanged; eauto. }
  assert (yread = Vsingle (values ICPY)) by congruence. subst yread.
  cbn in Hycast. inversion Hycast; subst yvalue.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (icp_generated_stage version ICPZ)) Hzr)
    as (z_le & z_m & z_t & return_t & Hzt & Hz & Hreturn).
  assert (Mem.load Mint32 y_m local 0 = Some (Vptr db (Ptrofs.repr d))) as HlocalY.
  { erewrite Mem.load_store_other; [exact HlocalX|exact Hystore|left; congruence]. }
  destruct (icp_stage_exact_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) HlocalY Hysrc Hz)
    as (zread & zvalue & Hzread & Hzcast & Hzstore & _).
  rewrite irc_plain_offset in Hzread, Hzstore by assumption.
  assert (Mem.load Mfloat32 y_m sb (s + 4 * icp_number ICPZ) =
    Some (Vsingle (values ICPZ))) as HsourceZ.
  { erewrite Mem.load_store_other; [|exact Hystore|left; congruence].
    erewrite Mem.load_store_other; [|exact Hxstore|left; congruence].
    erewrite Mem.load_store_other; [|exact HinitStore|left; congruence].
    erewrite Mem.load_alloc_unchanged; eauto. }
  assert (zread = Vsingle (values ICPZ)) by congruence. subst zread.
  cbn in Hzcast. inversion Hzcast; subst zvalue.
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
  - intros axis. erewrite Mem.load_free; [|exact HfreeOne|left; congruence].
    destruct axis.
    + erewrite Mem.load_store_other; [|exact Hzstore|right; left; cbn [size_chunk icp_number]; lia].
      erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ Hxstore)|
        exact Hystore|right; left; cbn [size_chunk icp_number]; lia].
    + erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ Hystore)|
        exact Hzstore|right; left; cbn [size_chunk icp_number]; lia].
    + exact (Mem.load_store_same _ _ _ _ _ _ Hzstore).
  - intros chunk b ofs Hvalid Houtside.
    assert (b <> local) as Hbl by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
    erewrite Mem.load_free; [|exact HfreeOne|left; congruence].
    erewrite Mem.load_store_other; [|exact Hzstore|unfold irc_outside_vector in Houtside;
      cbn [size_chunk icp_number]; lia].
    erewrite Mem.load_store_other; [|exact Hystore|unfold irc_outside_vector in Houtside;
      cbn [size_chunk icp_number]; lia].
    erewrite Mem.load_store_other; [|exact Hxstore|unfold irc_outside_vector in Houtside;
      cbn [size_chunk icp_number]; lia].
    erewrite Mem.load_store_other; [|exact HinitStore|left; congruence].
    eapply Mem.load_alloc_unchanged; eauto.
Qed.

Definition InkRetryCompletedPosition : Prop :=
  forall version e le m mb ob slot values t le' m' out,
  e ! IBM._vec3f_copy = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  (slot < object_pool_capacity)%nat ->
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  (forall axis, Mem.load Mfloat32 m ob
    (object_slot_offset slot + 32 + 4 * icp_number axis) = Some (Vsingle (values axis))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' m' out ->
  exists copied copy_trace query_trace result,
    t = copy_trace ++ query_trace /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ibk_copy_body version))
      [Vptr mb (Ptrofs.repr 60); Vptr ob (Ptrofs.repr (object_slot_offset slot + 32))]
      copy_trace copied result /\
    (forall axis, Mem.load Mfloat32 copied mb (60 + 4 * icp_number axis) =
      Some (Vsingle (values axis))) /\
    (forall chunk b ofs, Mem.valid_block m b -> irc_outside_vector mb 60 chunk b ofs ->
      Mem.load chunk copied b ofs = Mem.load chunk m b ofs) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBM._t'45 (Vptr ob (Ptrofs.repr (object_slot_offset slot))) le)
      copied (ibk_second_query version) query_trace le' m' out.

Theorem irc_taken_retry_completes_before_second_query : InkRetryCompletedPosition.
Proof.
  unfold InkRetryCompletedPosition.
  intros version e le m mb ob slot values t le' m' out
    Hlocal Hmsym Hosym Hslot Hm Hobj Hvalues Hretry.
  destruct (ibk_taken_retry_has_real_copy_predecessor _ _ _ _ _ _ _ _ Hlocal Hretry)
    as (object & args & result & copied & copy_trace & query_trace &
      Htrace & Hobject & Hargs & Hcall & Hquery).
  assert (object = Vptr ob (Ptrofs.repr (object_slot_offset slot))) by
    (eapply ibcc_actual_object_read; [exact Hm|exact Hobj|exact Hobject]). subst object.
  assert ((PTree.set IBM._t'45 (Vptr ob (Ptrofs.repr (object_slot_offset slot))) le)
    ! IBM._m = Some (Vptr mb Ptrofs.zero)) as HmNow
    by (rewrite PTree.gso by discriminate; exact Hm).
  pose proof (ibcc_actual_argument_pointers _ _ _ _ _ _ _ _ _
    HmNow (PTree.gss _ _ _) Hargs) as HargValues. subst args.
  change (Ptrofs.add Ptrofs.zero (Ptrofs.repr 60)) with (Ptrofs.repr 60) in Hcall.
  replace (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 32))
    with (Ptrofs.repr (object_slot_offset slot + 32)) in Hcall by
    (pose proof (f_equal Ptrofs.repr (irc_slot_address slot 32 Hslot ltac:(lia))) as Hptr;
      rewrite Ptrofs.repr_unsigned in Hptr; congruence).
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hmsym Hosym) as Hsep.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ Hobj) as Hvalid.
  destruct (irc_completed_vector_copy version _ m mb 60 ob
    (object_slot_offset slot + 32) values copy_trace copied result Hsep Hvalid
    ltac:(lia) ltac:(change (68 <= 4294967295); lia)
    ltac:(unfold object_slot_offset, object_size; lia)
    ltac:(change (608 * Z.of_nat slot + 32 + 8 <= 4294967295);
      change (slot < 240)%nat in Hslot; lia) Hvalues Hcall) as (Hcopied & Hframe).
  exists copied, copy_trace, query_trace, result.
  repeat split; assumption.
Qed.
