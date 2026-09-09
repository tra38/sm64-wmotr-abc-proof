(** Real animation execution, including its entry pointer reads and loader.
    Ordinary destination separation and the transfer effect remain explicit. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkControllerEdge InkLateHelperSource
  InkLateCallExecution InkLateWriteFrame InkAnimationDestination InkAnimationLoaderFrame
  InkLandingHistoryGate InkFloorResetExecution ObjectContactNecessity
  ContactConsumerExecution EyerokRank15LiveMovement Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition iaf_list_pointer := tptr (Tstruct IBM._DmaHandlerList noattr).
Definition iaf_list_read := Efield ibcc_state IBM._animList iaf_list_pointer.
Definition iaf_buffer_read := Efield
  (Ederef (Etempvar IBM._t'13 iaf_list_pointer) (Tstruct IBM._DmaHandlerList noattr))
  IBM._bufTarget (tptr tvoid).
Definition iaf_prefix := [Sset IBM._o ibk_object_read;
  Ssequence (Sset IBM._t'13 iaf_list_read) (Sset IBM._targetAnim iaf_buffer_read)].
Definition iaf_load_type := Tfunction [iaf_list_pointer; tint] tint cc_default.
Definition iaf_load_call := Scall (Some IBM._t'1)
  (Evar IBM._load_patchable_table iaf_load_type)
  [Etempvar IBM._t'12 iaf_list_pointer; Etempvar IBM._targetAnimID tint].
Definition iaf_load_piece := Ssequence (Sset IBM._t'12 iaf_list_read) iaf_load_call.
Definition iaf_remainder version := rank12b_drop_sequences 2 (fn_body (ill_body version ILAnimation)).
Definition iaf_relocation version := match iaf_remainder version with
| Ssequence (Ssequence _ relocation) _ => relocation | _ => Sskip end.
Definition iaf_metadata version := rank12b_drop_sequences 3 (fn_body (ill_body version ILAnimation)).
Definition iaf_write lhs := match iad_write_root lhs with
| Some id => Pos.eqb id IBM._o || Pos.eqb id IBM._targetAnim | None => false end.

Lemma iaf_source_cuts : forall version,
  fn_body (ill_body version ILAnimation) = ocn_prepend iaf_prefix (iaf_remainder version) /\
  iaf_remainder version = Ssequence
    (Ssequence iaf_load_piece (iaf_relocation version)) (iaf_metadata version) /\
  ilw_shape [IBM._o; IBM._targetAnim] iaf_write (fun _ _ => false)
    (Ssequence (iaf_relocation version) (iaf_metadata version)) = true /\
  ibk_normal (iaf_relocation version) = true /\
  ibk_normal (Ssequence iaf_load_piece (iaf_relocation version)) = true.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Lemma iaf_selected_fields : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) IBM._MarioState IBM._animList 160 = true /\
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) IBM._DmaHandlerList IBM._bufTarget 8 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IBM._animList 160 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version)) IBM._DmaHandlerList IBM._bufTarget 8 = true).
  rewrite <- rank15_selected_header_environment_exact. destruct version; vm_compute; split; reflexivity.
Qed.

Definition InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao : Prop :=
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) = Some (Vptr ob oo) /\
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 160))) = Some (Vptr lb lo) /\
  Mem.load Mint32 m lb (Ptrofs.unsigned (Ptrofs.add lo (Ptrofs.repr 8))) = Some (Vptr ab ao) /\
  ob <> mb /\ lb <> mb /\ ab <> mb.

Lemma iaf_actual_prefix_reads : forall version e le m mb mo ob oo lb lo ab ao t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) ->
  InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ocn_prepend iaf_prefix Sskip) t le' m' out ->
  m' = m /\ le' ! IBM._m = Some (Vptr mb mo) /\
  le' ! IBM._o = Some (Vptr ob oo) /\ le' ! IBM._targetAnim = Some (Vptr ab ao).
Proof.
  intros version e le m mb mo ob oo lb lo ab ao t le' m' out Hm Hdest Hrun.
  destruct Hdest as (Hobject & Hlist & Hbuffer & _).
  destruct (iaf_selected_fields version) as [HlistField HbufferField].
  unfold iaf_prefix, ocn_prepend, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply ibcc_actual_object_read; eauto); subst v end.
  match goal with Hr : eval_expr _ _ ?temps _ iaf_list_read ?v |- _ =>
    assert (temps ! IBM._m = Some (Vptr mb mo)) as Hnow
      by (repeat rewrite PTree.gso by discriminate; exact Hm);
    assert (v = Vptr lb lo) by (eapply ice_field_read with (ty := iaf_list_pointer);
      [exact Hnow|exact HlistField|reflexivity|exact Hlist|exact Hr]); subst v end.
  lazymatch goal with Hr : eval_expr _ _ ?temps _ iaf_buffer_read ?v |- _ =>
    assert (temps ! IBM._t'13 = Some (Vptr lb lo)) as HbufferTemp
      by (repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate]; reflexivity);
    assert (v = Vptr ab ao) by (eapply ice_field_read with (ty := tptr tvoid);
      [exact HbufferTemp|exact HbufferField|reflexivity|exact Hbuffer|exact Hr]); subst v end.
  repeat split; repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate]; auto.
Qed.

Lemma iaf_animation_stores_preserve_timer : forall version e le m mb mo ob oo ab ao t le' m' out,
  le ! IBM._o = Some (Vptr ob oo) -> le ! IBM._targetAnim = Some (Vptr ab ao) ->
  ob <> mb -> ab <> mb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Ssequence (iaf_relocation version) (iaf_metadata version)) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version e le m mb mo ob oo ab ao t le' m' out Ho Ha Hob Hab Hrun.
  destruct (iaf_source_cuts version) as (_ & _ & Hshape & _).
  unshelve eapply (proj1 (ilw_checked_body_frame
    (Clight.globalenv (selected_clight_target version)) e [IBM._o; IBM._targetAnim]
    (fun id => if Pos.eq_dec id IBM._o then Some (Vptr ob oo) else Some (Vptr ab ao))
    iaf_write (fun _ _ => false) mb mo _ _ le m _ t le' m' out Hrun Hshape _)).
  - intros le0 mem lhs rhs tr le1 mem1 outcome Hrefs Hallowed Hwrite.
    unfold iaf_write in Hallowed. destruct (iad_write_root lhs) as [id|] eqn:Hroot; try discriminate.
    apply orb_true_iff in Hallowed as [Hid|Hid]; apply Pos.eqb_eq in Hid; subst id.
    + eapply (iad_other_block_assignment _ _ le0 mem lhs rhs IBM._o ob oo mb mo);
        [exact Hroot|exact (Hrefs IBM._o (or_introl eq_refl))|exact Hob|exact Hwrite].
    + eapply (iad_other_block_assignment _ _ le0 mem lhs rhs IBM._targetAnim ab ao mb mo);
        [exact Hroot|exact (Hrefs IBM._targetAnim (or_intror (or_introl eq_refl)))|exact Hab|exact Hwrite].
  - intros; discriminate.
  - intros id [Heq|[Heq|Hbad]]; subst; try contradiction; [exact Ho|exact Ha].
Qed.

Definition InkAnimationCheckedFrame : Prop := forall version mb mo,
  InkAnimationTransferTimerEffect version mb mo ->
  forall m ob oo lb lo ab ao args t m' result,
  InkAnimationEntryDestinations m mb mo ob oo lb lo ab ao ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version ILAnimation)) (Vptr mb mo :: args) t m' result ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.

Theorem iaf_actual_animation_preserves_timer : InkAnimationCheckedFrame.
Proof.
  intros version mb mo Htransfer m ob oo lb lo ab ao args t m' result Hdest Hcall.
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
  lazymatch type of Hlist with Mem.load _ ?initial_memory _ _ = _ =>
    assert (ilh_timer_load reloc_m mb mo = ilh_timer_load initial_memory mb mo) as HloadFrame end.
  { unfold iaf_load_call in Hload.
    destruct (ilh_actual_named_call version ILLoad empty_env _ _ _ _
      [iaf_list_pointer; tint] tint _ _ _ _ eq_refl Hload)
      as (values & answer & Hvalues & Hloader).
    inversion Hvalues; subst.
    lazymatch goal with Hr : eval_expr _ _ _ _ (Etempvar IBM._t'12 _) ?v |- _ =>
      assert (v = Vptr lb lo) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst v end.
    match goal with Hcast : sem_cast (Vptr lb lo) _ _ _ = Some _ |- _ =>
      cbn in Hcast; inversion Hcast; subst end.
    eapply ial_actual_loader_preserves_timer;
      [exact Htransfer|exact Hlb|exact Hab|exact Hbuffer|exact Hloader]. }
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
  congruence.
Qed.
