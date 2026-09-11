(** Backward predecessor of a pre-action platform departure. An ownerless
    floor clears both platform references; a null reference makes the next
    complete displacement dispatcher preserve all memory. The actual floor
    selection and intervening scheduler writes are separate obligations. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_platform_displacement jp_platform_displacement.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkBackwardSource InkBackwardExecution InkBodyResetFrame InkBodyResetConstruction
  InkCopyCaller InkFloorListEffects ObjectContactNecessity ContactConsumerExecution
  SecretContactExecution SelectedClightTarget EyerokRank15LiveMovement
  Area2Rank12BContact UpperElevatorQueryResolution
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
From LessThanOneAPress.Proofs Require Import InkPlatformSource.

Lemma ipd_global_value : forall (ge : genv) e le m id b v answer,
  e ! id = None -> Genv.find_symbol ge id = Some b ->
  Mem.load Mptr m b 0 = Some v ->
  eval_expr ge e le m (Evar id ipd_object) answer -> answer = v.
Proof.
  intros ge e le m id b v answer Hlocal Hsymbol Hload Hread.
  inversion Hread; subst.
  match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H; subst end; try congruence.
  match goal with H : deref_loc _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : Mem.loadv _ _ (Vptr ?loc _) = Some _ |- _ =>
    assert (loc = b) by congruence; subst loc;
    change (Mem.load Mptr m b 0 = Some answer) in H; congruence end.
Qed.

Lemma ipd_null_nonnull_is_zero : forall ge e le m id ty v,
  le ! id = Some (Vint Int.zero) ->
  eval_expr ge e le m (Ecast (ipd_nonnull id ty) tbool) v ->
  (ty = ipd_object) -> v = Vint Int.zero.
Proof.
  intros ge e le m id ty v Htemp Hrun ->.
  unfold ipd_nonnull, ipd_null in Hrun.
  inversion Hrun; subst; try solve [match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H end].
  match goal with H : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion H; subst; clear H end.
  - match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Ecast _ _) _ |- _ => inversion H; subst; clear H end.
    + match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
      match goal with H : sem_cast (Vint Int.zero) _ _ _ = Some _ |- _ => cbn in H; inversion H; subst; clear H end.
      match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
        cbn in H; inversion H; subst; clear H end.
      match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H end. reflexivity.
    + match goal with H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

(** This covers the full dispatcher for every defined flag/Mario-pointer
    reading, not a particular time-stop value or a source-only census. *)
Lemma ipd_null_apply_body : forall version e le m pb t le' m' out,
  e ! IPD._gMarioPlatform = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Mem.load Mptr m pb 0 = Some (Vint Int.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ipd_body version IPDApply)) t le' m' out -> t = E0 /\ m' = m.
Proof.
  intros version e le m pb t le' m' out Hlocal Hsymbol Hnull Hrun.
  destruct (ipd_source version) as (_ & _ & _ & _ & _ & Hbody & Hprefix & Hpure & Hnormal).
  rewrite Hbody in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sset IPD._platform (Evar IPD._gMarioPlatform ipd_object)) _ _ _ _ _ eq_refl Hrun)
    as (loaded & m0 & t0 & t1 & -> & Hload & Hrest).
  inversion Hload; subst; clear Hload.
  match type of Hnull with Mem.load _ ?memory _ _ = _ => rename memory into m end.
  match goal with H : eval_expr _ _ _ _ (Evar _ _) ?v |- _ =>
    assert (v = Vint Int.zero) by
      (eapply ipd_global_value; eauto); subst v end.
  destruct (ibk_split_sequence _ _ _ _ (ipd_apply_prefix version) _ _ _ _ _
    ltac:(destruct version; reflexivity) Hrest)
    as (checked & m1 & t2 & t3 & Htrace & Hcheck & Hcall).
  rewrite Hprefix in Hcheck.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hcheck)
    as (tested & m2 & t4 & t5 & Htrace' & Htest & Hchoose).
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Htest Hpure) as (-> & -> & Hkeep).
  rewrite PTree.gss in Hkeep.
  assert (t5 = E0 /\ m1 = m /\ checked ! IPD._t'2 = Some (Vint Int.zero)) as Hzero.
  { inversion Hchoose; subst. destruct b.
    - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion H; subst; clear H end.
      match goal with H : eval_expr _ _ _ _ (Ecast _ _) ?v |- _ =>
        assert (v = Vint Int.zero) by (eapply ipd_null_nonnull_is_zero; eauto); subst v end.
      repeat split; try reflexivity; apply PTree.gss.
    - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion H; subst; clear H end.
      match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
      repeat split; try reflexivity; apply PTree.gss. }
  destruct Hzero as (-> & -> & Hzero).
  assert (exists yes, ipd_apply_call version = Sifthenelse (Etempvar IPD._t'2 tint) yes Sskip)
    as [yes Hlast] by (destruct version; eexists; reflexivity).
  rewrite Hlast in Hcall. inversion Hcall; subst.
  match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : bool_val (Vint Int.zero) _ _ = Some ?take |- _ => change (Some false = Some take) in H; inversion H; subst end.
  cbn beta iota in *.
  match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H; subst end.
  subst. split; reflexivity.
Qed.

Definition InkNullPlatformCannotDepart : Prop := forall version m pb t m' result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Mem.load Mptr m pb 0 = Some (Vint Int.zero) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Internal (ipd_body version IPDApply)) [] t m' result -> t = E0 /\ m' = m.

Theorem ipd_null_platform_call_cannot_depart : InkNullPlatformCannotDepart.
Proof.
  intros version m pb t m' result Hsymbol Hnull Hcall.
  assert (fn_vars (ipd_body version IPDApply) = []) as Hvars by (destruct version; reflexivity).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ => inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ => rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (ipd_null_apply_body version empty_env _ _ pb _ _ _ _ eq_refl Hsymbol Hnull Hrun) as (-> & ->) end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  split; reflexivity.
Qed.

Lemma ipd_fields : forall version,
  let ce := prog_comp_env (selected_clight_target version) in
  ibcc_field_ok ce IPD._Surface IPD._object 44 = true /\
  ibcc_field_ok ce IPD._Object IPD._platform 532 = true.
Proof.
  intro version. cbn zeta. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; split; reflexivity.
Qed.

Lemma ipd_local_floor_value : forall (ge : genv) e le m fb sb so answer,
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vptr sb so) ->
  eval_expr ge e le m (Evar IPD._floor ipd_surface) answer -> answer = Vptr sb so.
Proof.
  intros ge e le m fb sb so answer Hlocal Hload Hread.
  inversion Hread; subst.
  match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H; subst end; try congruence.
  match goal with H : deref_loc _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : Mem.loadv _ _ (Vptr ?loc _) = Some _ |- _ =>
    assert (loc = fb) by congruence; subst loc;
    change (Mem.load Mptr m fb 0 = Some answer) in H; congruence end.
Qed.

(** The real short-circuit owner test, including its two floor-pointer reads.
    No premise says that the test is false; it follows from Surface.object. *)
Lemma ipd_ownerless_guard : forall version e le m fb sb so t le' m' out,
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vptr sb so) ->
  Mem.load Mptr m sb (Ptrofs.unsigned (Ptrofs.add so (Ptrofs.repr 44))) = Some (Vint Int.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipd_owner_guard version) t le' m' out ->
  t = E0 /\ m' = m /\ le' ! IPD._t'3 = Some (Vint Int.zero).
Proof.
  intros version e le m fb sb so t le' m' out Hlocal Hfloor Howner Hrun.
  destruct (ipd_source version) as (_ & _ & Hguard & _). rewrite Hguard in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: repeat match goal with H : eval_expr _ _ _ _ (Evar IPD._floor _) ?v |- _ =>
    assert (v = Vptr sb so) by (eapply ipd_local_floor_value; eauto); subst v; clear H end.
  all: lazymatch goal with H : eval_expr _ _ ?temps ?memory
      (ibr_field IPD._t'11 IPD._Surface IPD._object ipd_object) ?v |- _ =>
    assert (temps ! IPD._t'11 = Some (Vptr sb so)) as Htemp by apply PTree.gss;
    pose proof (ibr_field_read_value (Clight.globalenv (selected_clight_target version))
      e temps memory IPD._t'11 IPD._Surface IPD._object ipd_object 44 Mptr sb so
      (Vint Int.zero) v Htemp (proj1 (ipd_fields version)) eq_refl Howner H) as Hvalue;
    subst v; clear H Htemp
    | _ => idtac end.
  all: try match goal with H : eval_expr _ _ ?temps _ (Ecast (ipd_nonnull IPD._t'12 _) tbool) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ipd_null_nonnull_is_zero;
      [apply PTree.gss|exact H|reflexivity]); subst v end.
  all: repeat match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in H; subst end.
  all: repeat split; try reflexivity; apply PTree.gss.
Qed.

Lemma ipd_null_value : forall ge e le m v,
  eval_expr ge e le m ipd_null v -> v = Vint Int.zero.
Proof.
  intros ge e le m v H. unfold ipd_null in H. inversion H; subst.
  - match goal with Hc : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hc; subst end.
    match goal with Hc : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hc; inversion Hc; reflexivity end.
  - match goal with Hl : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma ipd_null_store : forall ge e le m lhs b ofs t le' m' out,
  typeof lhs = ipd_object ->
  (forall loc off bf, eval_lvalue ge e le m lhs loc off bf -> loc = b /\ off = ofs /\ bf = Full) ->
  ocn_exec ge e le m (Sassign lhs ipd_null) t le' m' out ->
  t = E0 /\ le' = le /\ out = Out_normal /\
  Mem.store Mptr m b (Ptrofs.unsigned ofs) (Vint Int.zero) = Some m'.
Proof.
  intros ge e le m lhs b ofs t le' m' out Htype Hloc Hrun.
  inversion Hrun; subst; clear Hrun.
  match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (Hloc _ _ _ H) as (-> & -> & ->) end.
  match goal with H : eval_expr _ _ _ _ ipd_null _ |- _ => apply ipd_null_value in H; subst end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    rewrite Htype in H; cbn in H; inversion H; subst end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    rewrite Htype in H; inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
  repeat split; assumption.
Qed.

(** All effects of the clearing branch: both stores, including the second
    global Mario-pointer read. Ordinary separate global/object storage is
    sufficient; no preservation property is assumed for this branch. *)
Lemma ipd_clear_both : forall version e le m pb gb ob oo t le' m' out,
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipd_clear version) t le' m' out ->
  t = E0 /\ Mem.load Mptr m' pb 0 = Some (Vint Int.zero) /\
  Mem.load Mptr m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) = Some (Vint Int.zero) /\
  forall chunk b ofs,
    ifl_disjoint pb 0 4 chunk b ofs ->
    ifl_disjoint ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) 4 chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version e le m pb gb ob oo t le' m' out Hpl Hml Hps Hms Hpo Hm Hrun.
  assert (pb <> gb) as Hpg.
  { eapply Genv.global_addresses_distinct; [|exact Hps|exact Hms]. discriminate. }
  destruct (ipd_source version) as (_ & _ & _ & Hclear & _). rewrite Hclear in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sassign (Evar IPD._gMarioPlatform ipd_object) ipd_null) _ _ _ _ _ eq_refl Hrun)
    as (middle & m1 & pre & suf & -> & Hfirst & Hrest).
  destruct (ipd_null_store (Clight.globalenv (selected_clight_target version)) e le m
    (Evar IPD._gMarioPlatform ipd_object) pb Ptrofs.zero _ _ _ _ eq_refl
    ltac:(intros loc off bf Hl; inversion Hl; subst; try congruence;
      assert (loc = pb) by congruence; subst; auto) Hfirst) as (-> & -> & _ & Hstore).
  assert (Mem.load Mptr m1 gb 0 = Some (Vptr ob oo)) as Hm1.
  { rewrite <- Hm. eapply Mem.load_store_other; [exact Hstore|left; congruence]. }
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrest. cce_unroll_loop_free_exec.
  match goal with H : eval_expr _ _ _ _ (Evar IPD._gMarioObject _) ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply ipd_global_value; eauto); subst v end.
  lazymatch goal with H : ClightBigstep.exec_stmt _ _ _ ?temps ?memory (Sassign _ _) _ _ _ _ |- _ =>
    destruct (ipd_null_store (Clight.globalenv (selected_clight_target version)) e temps memory
      (ibr_field IPD._t'4 IPD._Object IPD._platform ipd_object)
      ob (Ptrofs.add oo (Ptrofs.repr 532)) _ _ _ _ eq_refl
      ltac:(intros loc off bf Hl;
        eapply (ibcc_field_location (Clight.globalenv (selected_clight_target version))
          e temps memory (ibr_base IPD._t'4 IPD._Object) IPD._Object IPD._platform
          ipd_object ob oo 532 loc off bf);
        [reflexivity| |exact (proj2 (ipd_fields version))|exact Hl];
        intros; eapply ibcc_deref_struct; [|eassumption]; apply PTree.gss) H)
      as (-> & -> & _ & Hstore2) end.
  split; [reflexivity|]. split.
  - rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore2 Mptr pb 0) by (left; congruence).
    exact (Mem.load_store_same _ _ _ _ _ _ Hstore).
  - split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore2)|].
    intros chunk b ofs Houtside1 Houtside2.
    match type of Hstore with Mem.store _ _ _ _ _ = Some ?middleMemory =>
      transitivity (Mem.load chunk middleMemory b ofs) end;
      eapply Mem.load_store_other; [exact Hstore2|exact Houtside2|exact Hstore|exact Houtside1].
Qed.

Definition InkOwnerlessPlatformClearing : Prop := forall version e le m fb sb so pb gb ob oo t le' m' out,
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vptr sb so) ->
  Mem.load Mptr m sb (Ptrofs.unsigned (Ptrofs.add so (Ptrofs.repr 44))) = Some (Vint Int.zero) ->
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipd_owner_branch version) t le' m' out ->
  t = E0 /\ Mem.load Mptr m' pb 0 = Some (Vint Int.zero) /\
  Mem.load Mptr m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) = Some (Vint Int.zero) /\
  forall chunk b ofs, ifl_disjoint pb 0 4 chunk b ofs ->
    ifl_disjoint ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) 4 chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs.

Theorem ipd_ownerless_floor_clears_both_platforms : InkOwnerlessPlatformClearing.
Proof.
  intros version e le m fb sb so pb gb ob oo t le' m' out
    Hlocal Hfloor Howner Hpl Hml Hps Hms Hpo Hm Hrun.
  destruct (ipd_source version) as (_ & Hbranch & _). rewrite Hbranch in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (ipd_owner_guard version) _ _ _ _ _
    ltac:(destruct version; reflexivity) Hrun)
    as (guarded & middle & pre & suf & -> & Hguard & Hchoice).
  destruct (ipd_ownerless_guard _ _ _ _ _ _ _ _ _ _ _ Hlocal Hfloor Howner Hguard)
    as (-> & -> & Hzero).
  assert (exists yes, ipd_owner_choice version =
    Sifthenelse (Etempvar IPD._t'3 tint) yes (ipd_clear version)) as [yes HchoiceShape]
    by (destruct version; eexists; reflexivity).
  rewrite HchoiceShape in Hchoice. inversion Hchoice; subst.
  match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : bool_val (Vint Int.zero) _ _ = Some ?take |- _ => change (Some false = Some take) in H; inversion H; subst end.
  cbn beta iota in *.
  eapply ipd_clear_both; eauto.
Qed.

(** No frame is granted between these two checkpoints. A changed actual
    position implies changed memory, hence a replacement of the cleared
    global pointer is necessary before the displacement call can help. *)
Definition InkPlatformDepartureNeedsReplacement : Prop :=
  forall version e le m fb sb so pb gb ob oo t le' cleared out next tnext after result,
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vptr sb so) ->
  Mem.load Mptr m sb (Ptrofs.unsigned (Ptrofs.add so (Ptrofs.repr 44))) = Some (Vint Int.zero) ->
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipd_owner_branch version) t le' cleared out ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) next
    (Internal (ipd_body version IPDApply)) [] tnext after result ->
  after <> next -> Mem.load Mptr next pb 0 <> Mem.load Mptr cleared pb 0.

Theorem ipd_departure_requires_replacing_the_cleared_pointer : InkPlatformDepartureNeedsReplacement.
Proof.
  intros version e le m fb sb so pb gb ob oo t le' cleared out next tnext after result
    Hlocal Hfloor Howner Hpl Hml Hps Hms Hpo Hm Hclear Happly Hchanged Hsame.
  destruct (ipd_ownerless_floor_clears_both_platforms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hlocal Hfloor Howner Hpl Hml Hps Hms Hpo Hm Hclear) as (_ & Hnull & _).
  rewrite Hnull in Hsame.
  destruct (ipd_null_platform_call_cannot_depart _ _ _ _ _ _ Hps Hsame Happly) as [_ Hunchanged].
  contradiction.
Qed.

Definition InkPlatformDepartureBoundary : Prop :=
  (forall version kind, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ipd_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b = Some (Internal (ipd_body version kind))) /\
  InkOwnerlessPlatformClearing /\ InkNullPlatformCannotDepart /\ InkPlatformDepartureNeedsReplacement.

Theorem ipd_backward_platform_departure_checked : InkPlatformDepartureBoundary.
Proof.
  split; [exact ipd_selected_bodies_resolve|].
  split; [exact ipd_ownerless_floor_clears_both_platforms|].
  split; [exact ipd_null_platform_call_cannot_depart|].
  exact ipd_departure_requires_replacing_the_cleared_pointer.
Qed.
