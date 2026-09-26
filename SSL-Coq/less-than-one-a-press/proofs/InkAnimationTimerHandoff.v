(** Follow a completed animation call to its actual loader invocation.
    This removes the universal transfer-effect premise for an invocation
    whose real loader returns zero.  A nonzero result is not evidence that
    DMA changed Mario, and no lifetime cache invariant is assumed here. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkControllerEdge InkLateHelperSource
  InkLateCallExecution InkLateWriteFrame InkAnimationDestination InkAnimationLoaderFrame
  InkAnimationTimerFrame InkAnimationNoTransfer InkLandingHistoryGate
  InkLandingLateClosure InkLandingContinuationSource InkFloorResetExecution ObjectContactNecessity
  ContactConsumerExecution EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Opaque selected_clight_target.

Definition InkAnimationLoaderHandoff : Prop :=
  forall version m mb mo ob oo lb lo ab ao args t m' result,
  InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version ILAnimation)) (Vptr mb mo :: args) t m' result ->
  exists loader_args loader_t loader_m loader_result,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ill_body version ILLoad)) (Vptr lb lo :: loader_args)
      loader_t loader_m loader_result /\
    ilh_timer_load m' mb mo = ilh_timer_load loader_m mb mo /\
    (loader_result = Vint Int.zero ->
      loader_t = E0 /\ loader_m = m /\
      ilh_timer_load m' mb mo = ilh_timer_load m mb mo).

Theorem iath_completed_animation_exposes_its_real_loader : InkAnimationLoaderHandoff.
Proof.
  intros version m mb mo ob oo lb lo ab ao args t m' result Hdest Hcall.
  destruct (ilh_actual_helper_entry version ILAnimation m mb mo args t m' result Hcall)
    as (entry_le & final_le & out & Hm & Hbody).
  destruct (iaf_source_cuts version) as (Hsource & Htail & Hstores & Hrn & Hln).
  rewrite Hsource in Hbody.
  destruct (ibk_split_prefix _ _ iaf_prefix _ _ _ _ _ _ _ eq_refl Hbody)
    as (cache_le & cache_m & cache_t & rest_t & Htrace & Hcache & Hrest).
  destruct (iaf_actual_prefix_reads version empty_env entry_le m mb mo ob oo lb lo ab ao
    _ _ _ _ Hm Hdest Hcache) as (-> & HcacheM & HcacheO & HcacheA).
  destruct Hdest as (Hobject & Hlist & Hbuffer & Hob & Hlb & Hab).
  rewrite Htail in Hrest.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hln Hrest)
    as (meta_le & meta_m & load_reloc_t & meta_t & HrestTrace & HloadReloc & Hmeta).
  destruct (ibk_split_sequence _ _ _ _ iaf_load_piece _ _ _ _ _ eq_refl HloadReloc)
    as (reloc_le & reloc_m & load_t & reloc_t & HlrTrace & HloadPiece & Hreloc).
  unfold iaf_load_piece in HloadPiece.
  destruct (ibk_split_sequence _ _ _ _ (Sset IBM._t'12 iaf_list_read) _ _ _ _ _ eq_refl HloadPiece)
    as (load_le & load_m & read_t & call_t & HloadTrace & Hread & Hload).
  inversion Hread; subst; clear Hread.
  match goal with Hr : eval_expr _ _ ?temps _ iaf_list_read ?v |- _ =>
    assert (v = Vptr lb lo) by (eapply ice_field_read with (ty := iaf_list_pointer);
      [exact HcacheM|exact (proj1 (iaf_selected_fields version))|reflexivity|exact Hlist|exact Hr]); subst v end.
  assert (reloc_le ! IBM._o = Some (Vptr ob oo) /\
    reloc_le ! IBM._targetAnim = Some (Vptr ab ao)) as [HrelocO HrelocA].
  { pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IBM._o Hload eq_refl) as Ho.
    pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IBM._targetAnim Hload eq_refl) as Ha.
    rewrite PTree.gso in Ho, Ha by discriminate. split; congruence. }
  assert (ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
    reloc_le reloc_m (Ssequence (iaf_relocation version) (iaf_metadata version))
    (reloc_t ++ meta_t) final_le m' out) as Hpost by (econstructor; eauto).
  pose proof (iaf_animation_stores_preserve_timer version empty_env reloc_le reloc_m
    mb mo ob oo ab ao _ _ _ _ HrelocO HrelocA Hob Hab Hpost) as HpostFrame.
  unfold iaf_load_call in Hload.
  destruct (ilh_actual_named_call version ILLoad empty_env _ _ _ _
    [iaf_list_pointer; tint] tint _ _ _ _ eq_refl Hload)
    as (values & answer & Hvalues & Hloader).
  inversion Hvalues; subst.
  lazymatch goal with Hr : eval_expr _ _ _ _ (Etempvar IBM._t'12 _) ?v |- _ =>
    assert (v = Vptr lb lo) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst v end.
  match goal with Hcast : sem_cast (Vptr lb lo) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  do 4 eexists. split; [exact Hloader|]. split; [exact HpostFrame|].
  intros ->.
  destruct (ian_zero_loader_result_has_no_effect _ _ _ _ _ Hloader) as [Ht Hmemory].
  repeat split; congruence.
Qed.

Definition InkLandingAnimationLoaderHandoff : Prop :=
  forall version le m mb mo ob oo lb lo ab ao t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) ->
  InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (ilc_animation version) t le' m' out ->
  exists loader_args loader_t loader_m loader_result,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ill_body version ILLoad)) (Vptr lb lo :: loader_args)
      loader_t loader_m loader_result /\
    ilh_timer_load m' mb mo = ilh_timer_load loader_m mb mo /\
    (loader_result = Vint Int.zero ->
      loader_t = E0 /\ loader_m = m /\
      ilh_timer_load m' mb mo = ilh_timer_load m mb mo).

Theorem iath_landing_call_exposes_its_real_loader : InkLandingAnimationLoaderHandoff.
Proof.
  intros version le m mb mo ob oo lb lo ab ao t le' m' out Hm Hdest Hrun.
  destruct (ilt_actual_call_shapes version) as (aa & sa & Hshape & Hhead & _).
  rewrite Hshape in Hrun.
  destruct (ilh_actual_named_call version ILAnimation empty_env le m None aa
    [ill_mario_pointer; tint] tshort t le' m' out eq_refl Hrun)
    as (values & result & Hargs & Hcall).
  destruct (ilh_mario_head_exact aa Hhead) as [rest ->].
  destruct (ilh_actual_mario_arguments _ _ _ _ _ _ _ mb mo Hm Hargs) as [other ->].
  eapply iath_completed_animation_exposes_its_real_loader; eassumption.
Qed.

(** If this loader invocation changed the timer, its own bookkeeping did
    not do so: the very transfer it executed has that changed timer. *)
Lemma iath_loader_timer_change_is_in_its_actual_transfer :
  forall version m mb mo lb lo ab ao args t m' result,
  lb <> mb -> ab <> mb ->
  Mem.load Mint32 m lb (Ptrofs.unsigned (Ptrofs.add lo (Ptrofs.repr 8))) = Some (Vptr ab ao) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version ILLoad)) (Vptr lb lo :: args) t m' result ->
  ilh_timer_load m' mb mo <> ilh_timer_load m mb mo ->
  exists transfer_le transfer_t after_le after_m,
    transfer_le ! us_memory._t'3 = Some (Vptr ab ao) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env transfer_le m
      ial_transfer_call transfer_t after_le after_m Out_normal /\
    ilh_timer_load m' mb mo = ilh_timer_load after_m mb mo /\
    ilh_timer_load after_m mb mo <> ilh_timer_load m mb mo.
Proof.
  intros version m mb mo lb lo ab ao args t m' result Hother HbufferOther Hbuffer Hcall Hchange.
  destruct (ilh_actual_helper_entry version ILLoad m lb lo args t m' result Hcall)
    as (entry_le & final_le & out & Hlist & Hbody).
  assert (ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    us_memory._DmaHandlerList us_memory._bufTarget 8 = true) as Hfield.
  { change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
      us_memory._DmaHandlerList us_memory._bufTarget 8 = true).
    rewrite <- rank15_selected_header_environment_exact. destruct version; vm_compute; reflexivity. }
  assert (fn_body (ill_body version ILLoad) = fn_body us_memory.f_load_patchable_table) as Hsource
    by (destruct version; reflexivity).
  rewrite Hsource in Hbody.
  cbv [fn_body us_memory.f_load_patchable_table] in Hbody.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hbody.
  cce_unroll_loop_free_exec.
  all: try solve [match goal with
    | Hbad : ?outcome <> Out_normal,
      Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ ?outcome |- _ =>
        inversion Hr; subst; contradiction
    | Hbad : ?outcome <> Out_normal,
      Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ ?outcome |- _ =>
        inversion Hr; subst; contradiction end].
  all: try solve [exfalso; apply Hchange; reflexivity].
  lazymatch goal with Hr : eval_expr _ _ ?temps _ (Efield _ us_memory._bufTarget _) ?value |- _ =>
    assert (temps ! us_memory._list = Some (Vptr lb lo)) as HoriginalList
      by (repeat rewrite PTree.gso by discriminate; exact Hlist);
    assert (value = Vptr ab ao) by (eapply ice_field_read with (ty := tptr tvoid);
      [exact HoriginalList|exact Hfield|reflexivity|exact Hbuffer|exact Hr]); subst value end.
  lazymatch goal with Hr : ClightBigstep.exec_stmt _ _ _ ?temps ?memory (Scall _ _ _) ?tr ?temps' ?memory' ?outcome |- _ =>
    assert (ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env
      temps memory ial_transfer_call tr temps' memory' outcome) as Htransfer by exact Hr;
    assert (temps ! us_memory._t'3 = Some (Vptr ab ao)) as Hdest by apply PTree.gss;
    inversion Hr; subst; clear Hr end.
  lazymatch goal with Hr : ClightBigstep.exec_stmt _ _ _ ?temps ?memory (Sassign ?lhs ?rhs) ?tr ?temps' ?memory' ?outcome |- _ =>
    assert (temps ! us_memory._list = Some (Vptr lb lo)) as HwriteList
      by (cbn [set_opttemp]; repeat rewrite PTree.gso by discriminate; exact Hlist);
    pose proof (iad_other_block_assignment _ _ temps memory lhs rhs us_memory._list lb lo mb mo
      tr temps' memory' outcome eq_refl HwriteList Hother Hr) as HwriteFrame end.
  do 4 eexists. split; [exact Hdest|]. split; [exact Htransfer|]. split; congruence.
Qed.

Definition InkAnimationTimerChangeRequiresTransfer : Prop :=
  forall version m mb mo ob oo lb lo ab ao args t m' result,
  InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version ILAnimation)) (Vptr mb mo :: args) t m' result ->
  ilh_timer_load m' mb mo <> ilh_timer_load m mb mo ->
  exists transfer_le transfer_t after_le after_m,
    transfer_le ! us_memory._t'3 = Some (Vptr ab ao) /\ ab <> mb /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env transfer_le m
      ial_transfer_call transfer_t after_le after_m Out_normal /\
    ilh_timer_load m' mb mo = ilh_timer_load after_m mb mo /\
    ilh_timer_load after_m mb mo <> ilh_timer_load m mb mo.

Theorem iath_changed_timer_requires_the_reached_transfer : InkAnimationTimerChangeRequiresTransfer.
Proof.
  intros version m mb mo ob oo lb lo ab ao args t m' result Hdest Hcall Hchange.
  destruct (iath_completed_animation_exposes_its_real_loader
    version m mb mo ob oo lb lo ab ao args t m' result Hdest Hcall)
    as (loader_args & loader_t & loader_m & loader_result & Hloader & Hframe & _).
  destruct Hdest as (Hobject & Hlist & Hbuffer & Hob & Hlb & Hab).
  destruct (iath_loader_timer_change_is_in_its_actual_transfer
    version m mb mo lb lo ab ao loader_args loader_t loader_m loader_result
    Hlb Hab Hbuffer Hloader ltac:(congruence))
    as (transfer_le & transfer_t & after_le & after_m & Hpointer & Htransfer & Hsame & Hdifferent).
  do 4 eexists. split; [exact Hpointer|]. split; [exact Hab|].
  split; [exact Htransfer|]. split; congruence.
Qed.
