(** Actual initialization writes for the animation descriptor. These establish
    what the setup code installs, not persistence through an entire game run. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_memory jp_memory us_mario jp_mario us_level_update.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkAnimationTimerFrame InkControllerEdge InkControllerSource InkCopyCaller
  InkLateHelperSource
  InkFloorResetExecution ObjectContactNecessity ContactConsumerExecution
  EyerokRank15LiveMovement Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition ias_setup_body version := match version with
| VersionUS => us_memory.f_setup_dma_table_list
| VersionJP => jp_memory.f_setup_dma_table_list end.
Definition ias_setup_prefix version := ocn_prefix_items 2 (fn_body (ias_setup_body version)).
Definition ias_buffer_store := Sassign
  (ics_field us_memory._list us_memory._DmaHandlerList us_memory._bufTarget (tptr tvoid))
  (Etempvar us_memory._buffer (tptr tvoid)).

Lemma ias_setup_source : forall version,
  fn_vars (ias_setup_body version) = [] /\
  fn_params (ias_setup_body version) =
    [(us_memory._list, iaf_list_pointer); (us_memory._srcAddr, tptr tvoid);
     (us_memory._buffer, tptr tvoid)] /\
  fn_body (ias_setup_body version) =
    ocn_prepend (ias_setup_prefix version) ias_buffer_store /\
  forallb ibk_normal (ias_setup_prefix version) = true /\
  ifr_keeps_temp us_memory._list (ocn_prepend (ias_setup_prefix version) Sskip) = true /\
  ifr_keeps_temp us_memory._buffer (ocn_prepend (ias_setup_prefix version) Sskip) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ias_actual_buffer_store : forall version e le m lb lo ab ao t le' m' out,
  le ! us_memory._list = Some (Vptr lb lo) ->
  le ! us_memory._buffer = Some (Vptr ab ao) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ias_buffer_store t le' m' out ->
  Mem.load Mint32 m' lb (Ptrofs.unsigned (Ptrofs.add lo (Ptrofs.repr 8))) =
    Some (Vptr ab ao).
Proof.
  intros version e le m lb lo ab ao t le' m' out Hlist Hbuffer Hrun.
  unfold ias_buffer_store in Hrun. inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue ?ge ?env ?temps ?memory _ _ _ _ |- _ =>
    destruct (ice_field_location ge env temps memory us_memory._list
      us_memory._DmaHandlerList us_memory._bufTarget (tptr tvoid) lb lo 8 _ _ _
      Hlist (proj2 (iaf_selected_fields version)) Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar us_memory._buffer _) ?v |- _ =>
    assert (v = Vptr ab ao) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  erewrite Mem.load_store_same by eassumption. reflexivity.
Qed.

Definition InkAnimationSetupInstallsBuffer : Prop :=
  forall version m lb lo source ab ao t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ias_setup_body version)) [Vptr lb lo; source; Vptr ab ao] t m' result ->
  Mem.load Mint32 m' lb (Ptrofs.unsigned (Ptrofs.add lo (Ptrofs.repr 8))) =
    Some (Vptr ab ao).

Theorem ias_completed_setup_installs_original_buffer : InkAnimationSetupInstallsBuffer.
Proof.
  intros version m lb lo source ab ao t m' result Hcall.
  destruct (ias_setup_source version) as (Hvars & Hparams & Hsource & Hnormal & Hkl & Hkb).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  lazymatch goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! us_memory._list = Some (Vptr lb lo) /\
      temps ! us_memory._buffer = Some (Vptr ab ao)) as [Hlist Hbuffer]
      by (rewrite Hparams in Hb; cbn in Hb; inversion Hb; split;
        repeat rewrite PTree.gso by discriminate; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hsource in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (store_le & store_m & pre & suf & Htrace & Hprefix & Hstore) end.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix Hkl) as Hl.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix Hkb) as Hb.
  eapply (ias_actual_buffer_store version empty_env store_le store_m lb lo ab ao);
    [rewrite Hl; exact Hlist|rewrite Hb; exact Hbuffer|exact Hstore].
Qed.

(** The descriptor pointer is a fixed global address, not a return value from
    a callback. Its actual initialization write is checked in both versions. *)
Definition ias_init_body version := match version with
| VersionUS => us_mario.f_init_mario_from_save_file
| VersionJP => jp_mario.f_init_mario_from_save_file end.
Definition ias_list_stage version := ibk_head
  (rank12b_drop_sequences 7 (fn_body (ias_init_body version))).
Definition ias_list_store := Sassign
  (ics_field IBM._t'12 IBM._MarioState IBM._animList iaf_list_pointer)
  (Eaddrof (Evar IBM._gMarioAnimsBuf (Tstruct IBM._DmaHandlerList noattr)) iaf_list_pointer).

Lemma ias_list_source : forall version,
  ias_list_stage version = Ssequence
    (Sset IBM._t'12 (Evar IBM._gMarioState ill_mario_pointer)) ias_list_store.
Proof. intros []; reflexivity. Qed.

Lemma ias_global_address : forall (ge : genv) e le m id ty b v,
  e ! id = None -> Genv.find_symbol ge id = Some b ->
  eval_expr ge e le m (Eaddrof (Evar id ty) (tptr ty)) v ->
  v = Vptr b Ptrofs.zero.
Proof.
  intros ge e le m id ty b v Hlocal Hsymbol Hr. inversion Hr; subst.
  - match goal with Hl : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ =>
      inversion Hl; subst; congruence end.
  - match goal with Hl : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma ias_mario_state_read : forall (ge : genv) le m pb value answer,
  Genv.find_symbol ge IBM._gMarioState = Some pb ->
  Mem.load Mint32 m pb 0 = Some value ->
  eval_expr ge empty_env le m (Evar IBM._gMarioState ill_mario_pointer) answer ->
  answer = value.
Proof.
  intros ge le m pb value answer Hsymbol Hload Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl; subst end;
    try discriminate.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  match goal with Hread : Mem.loadv _ _ (Vptr ?loc _) = Some _ |- _ =>
    assert (loc = pb) by congruence; subst loc;
    change (Mem.load Mint32 m pb 0 = Some answer) in Hread; congruence end.
Qed.

Lemma ias_actual_list_store : forall version e le m mb mo lb t le' m' out,
  le ! IBM._t'12 = Some (Vptr mb mo) -> e ! IBM._gMarioAnimsBuf = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IBM._gMarioAnimsBuf = Some lb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ias_list_store t le' m' out ->
  Mem.load Mint32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 160))) =
    Some (Vptr lb Ptrofs.zero).
Proof.
  intros version e le m mb mo lb t le' m' out Hm Hlocal Hsymbol Hrun.
  unfold ias_list_store in Hrun. inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue ?ge ?env ?temps ?memory _ _ _ _ |- _ =>
    destruct (ice_field_location ge env temps memory IBM._t'12 IBM._MarioState
      IBM._animList iaf_list_pointer mb mo 160 _ _ _ Hm
      (proj1 (iaf_selected_fields version)) Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Eaddrof _ _) ?v |- _ =>
    assert (v = Vptr lb Ptrofs.zero) by (eapply ias_global_address; eauto); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  erewrite Mem.load_store_same by eassumption. reflexivity.
Qed.

Theorem ias_descriptor_global_is_separate : forall (ge : genv) mb lb,
  Genv.find_symbol ge us_level_update._gMarioStates = Some mb ->
  Genv.find_symbol ge IBM._gMarioAnimsBuf = Some lb -> lb <> mb.
Proof.
  intros ge mb lb Hm Hl. eapply (Genv.global_addresses_distinct ge
    (id1 := IBM._gMarioAnimsBuf) (id2 := us_level_update._gMarioStates));
    [discriminate|exact Hl|exact Hm].
Qed.

Definition InkAnimationListInitialization : Prop :=
  forall version le m mb mo pb lb t le' m' out,
  let ge := Clight.globalenv (selected_clight_target version) in
  Genv.find_symbol ge us_level_update._gMarioStates = Some mb ->
  Genv.find_symbol ge IBM._gMarioState = Some pb ->
  Genv.find_symbol ge IBM._gMarioAnimsBuf = Some lb ->
  Mem.load Mint32 m pb 0 = Some (Vptr mb mo) ->
  ocn_exec ge empty_env le m (ias_list_stage version) t le' m' out ->
  Mem.load Mint32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 160))) =
    Some (Vptr lb Ptrofs.zero) /\ lb <> mb.

Theorem ias_initialization_installs_separate_descriptor : InkAnimationListInitialization.
Proof.
  intros version le m mb mo pb lb t le' m' out ge Hstate Hpointer Hdescriptor Hload Hrun.
  split; [|eapply ias_descriptor_global_is_separate; eauto].
  rewrite ias_list_source in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sset IBM._t'12 (Evar IBM._gMarioState ill_mario_pointer)) _ _ _ _ _ eq_refl Hrun)
    as (store_le & store_m & pre & suf & Htrace & Hread & Hstore).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ (Evar IBM._gMarioState _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ias_mario_state_read; eauto); subst v end.
  eapply (ias_actual_list_store version empty_env
    (PTree.set IBM._t'12 (Vptr mb mo) le) store_m mb mo lb);
    [apply PTree.gss|reflexivity|exact Hdescriptor|exact Hstore].
Qed.
