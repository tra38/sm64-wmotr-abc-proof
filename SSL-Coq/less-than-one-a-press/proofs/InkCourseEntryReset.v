(** A course-entry reset barrier, taken from the real US/JP initialization.
    A completed call must execute this store even if earlier calls have
    arbitrary effects. This is a checkpoint theorem, not a frame for the
    remaining initialization or a no-A reachability theorem. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import
  us_mario jp_mario us_level_update jp_level_update.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkControllerEdge InkControllerSource InkCopyCaller
  InkQuicksandExpressions ObjectContactNecessity SecretContactExecution
  Area2Rank12BContact UpperElevatorQueryResolution ContactConsumerSource
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IER := us_mario.
Module IEL := us_level_update.

Inductive ier_kind := IERInit | IERAfterWarp.
Definition ier_body version kind := match version, kind with
| VersionUS, IERInit => us_mario.f_init_mario
| VersionJP, IERInit => jp_mario.f_init_mario
| VersionUS, IERAfterWarp => us_level_update.f_init_mario_after_warp
| VersionJP, IERAfterWarp => jp_level_update.f_init_mario_after_warp end.
Definition ier_id kind := match kind with
| IERInit => IER._init_mario | IERAfterWarp => IEL._init_mario_after_warp end.
Definition ier_index kind : nat := match kind with IERInit => 1 | IERAfterWarp => 28 end.
Definition ier_us_defs kind := match kind with
| IERInit => us_mario.global_definitions
| IERAfterWarp => us_level_update.global_definitions end.

Lemma ier_us_source : forall kind,
  nth_error (ier_us_defs kind) (ueqr_definition_index (ier_id kind) (ier_us_defs kind)) =
    Some (ier_id kind, Gfun (Internal (ier_body VersionUS kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma ier_us_member : forall kind,
  In (ier_id kind, Gfun (Internal (ier_body VersionUS kind))) (unit_global_definitions us_units).
Proof.
  intro kind. eapply source_unit_definition_enters_source_union
    with (unit := us_nlist_at (ier_index kind) us_units).
  - exact (us_nlist_at_nIn _ (ier_index kind) us_units).
  - destruct kind.
    + eapply nth_error_In. exact (ier_us_source IERInit).
    + eapply nth_error_In. exact (ier_us_source IERAfterWarp).
Qed.
Lemma ier_us_selection : forall kind,
  us_normalized_global_definition_map ! (ier_id kind) =
    Some (Gfun (Internal (ier_body VersionUS kind))).
Proof.
  intro kind. eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact (ier_us_member kind).
Qed.
Lemma ier_us_no_repair : forall kind,
  us_selected_definition_needs_viewport_repair
    (ier_id kind, Gfun (Internal (ier_body VersionUS kind))) = false.
Proof. intros []; vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma ier_us_selected : forall kind,
  In (ier_id kind, Gfun (Internal (ier_body VersionUS kind))) us_viewport_repaired_global_definitions.
Proof.
  intro kind. unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ier_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. apply ier_us_selection.
Qed.
Lemma ier_jp_source : forall kind,
  (prog_defmap (nlist_at (ier_index kind) jp_cleaned_units)) ! (ier_id kind) =
    Some (Gfun (Internal (ier_body VersionJP kind))).
Proof. intros []; vm_compute; reflexivity. Qed.
Theorem ier_selected_resolves : forall version kind, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ier_id kind) = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ier_body version kind)).
Proof.
  intros [] kind.
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact (ier_us_selected kind).
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link
      (nlist_at (ier_index kind) jp_cleaned_units)).
    + exact (nlist_at_nIn _ (ier_index kind) jp_cleaned_units).
    + exact (ier_jp_source kind).
Qed.

Definition ier_state := Evar IER._gMarioState (tptr (Tstruct IER._MarioState noattr)).
Definition ier_depth := ics_field IER._t'91 IER._MarioState IER._quicksandDepth tfloat.
Definition ier_zero := Sassign ier_depth (Econst_single Float32.zero tfloat).
Definition ier_reset := Ssequence (Sset IER._t'91 ier_state) ier_zero.
Definition ier_prefix version := ocn_prefix_items 11 (fn_body (ier_body version IERInit)).
Definition ier_suffix version := rank12b_drop_sequences 12 (fn_body (ier_body version IERInit)).

Lemma ier_init_source : forall version,
  fn_body (ier_body version IERInit) =
    ocn_prepend (ier_prefix version) (Ssequence ier_reset (ier_suffix version)) /\
  forallb ibk_normal (ier_prefix version) = true.
Proof. intros []; split; reflexivity. Qed.

(** Infer the live Mario pointer from the successful typed field access;
    there is no incoming depth, finite-number, or storage-frame premise. *)
Lemma ier_depth_base : forall ge e le m b ofs bf,
  eval_lvalue ge e le m ier_depth b ofs bf ->
  exists mb mo, le ! IER._t'91 = Some (Vptr mb mo).
Proof.
  intros ge e le m b ofs bf H.
  unfold ier_depth, ics_field in H.
  inversion H; subst; clear H.
  all: repeat match goal with
  | H : eval_expr _ _ _ _ (Ederef _ _) _ |- _ => inversion H; subst; clear H
  | H : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ => inversion H; subst; clear H
  | H : deref_loc _ _ _ _ _ _ |- _ => inversion H; subst; clear H
  | H : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => inversion H; subst; clear H
  end.
  all: try solve [match goal with H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end].
  all: eauto.
Qed.

Lemma ier_reset_effect : forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ier_reset t le' m' out ->
  exists mb mo,
    eval_expr (Clight.globalenv (selected_clight_target version)) e le m
      ier_state (Vptr mb mo) /\
    Mem.store Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192)))
      (Vsingle Float32.zero) = Some m' /\
    Mem.load Mfloat32 m' mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) =
      Some (Vsingle Float32.zero) /\
    t = E0 /\ out = Out_normal.
Proof.
  intros version e le m t le' m' out Hrun.
  unfold ier_reset in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IER._t'91 ier_state) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hstore).
  inversion Hread; subst; clear Hread.
  unfold ier_zero in Hstore. inversion Hstore; subst; clear Hstore.
  lazymatch goal with Hl : eval_lvalue _ _ _ _ ier_depth _ _ _ |- _ =>
    destruct (ier_depth_base _ _ _ _ _ _ _ Hl) as (mb & mo & Hptr);
    rewrite PTree.gss in Hptr; inversion Hptr; subst;
    destruct (ice_field_location _ _ _ _ IER._t'91 IER._MarioState
      IER._quicksandDepth tfloat mb mo 192 _ _ _ ltac:(apply PTree.gss)
      (proj1 (iq_selected_fields version)) Hl) as (-> & -> & ->)
  end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ =>
    inversion Hr; subst; clear Hr
  end.
  all: try solve [match goal with Hb : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ =>
    inversion Hb end].
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  do 2 eexists. split; [eassumption|]. split; [eassumption|]. split.
  - erewrite Mem.load_store_same by eassumption. reflexivity.
  - split; reflexivity.
Qed.

(** This witness retains the actual body prefix, reset, and suffix in one
    completed initialization, plus its allocation and final freeing. *)
Definition InkCourseResetCheckpoint version m t m' result : Prop :=
  exists e le entered last_le last out reset_le before after_reset_le after
    pre suf mb mo,
    function_entry2 (Clight.globalenv (selected_clight_target version))
      (ier_body version IERInit) [] m e le entered /\
    t = pre ++ suf /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le entered
      (ocn_prepend (ier_prefix version) Sskip) pre reset_le before Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e reset_le before
      ier_reset E0 after_reset_le after Out_normal /\
    eval_expr (Clight.globalenv (selected_clight_target version)) e reset_le before
      ier_state (Vptr mb mo) /\
    Mem.store Mfloat32 before mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192)))
      (Vsingle Float32.zero) = Some after /\
    Mem.load Mfloat32 after mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) =
      Some (Vsingle Float32.zero) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e after_reset_le after
      (ier_suffix version) suf last_le last out /\
    Mem.free_list last (blocks_of_env (Clight.globalenv (selected_clight_target version)) e) = Some m' /\
    outcome_result_value out (fn_return (ier_body version IERInit)) result last.

Definition InkCompletedCourseEntryReset : Prop := forall version m t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ier_body version IERInit)) [] t m' result ->
  InkCourseResetCheckpoint version m t m' result.

Theorem ier_completed_init_has_zero_depth_checkpoint : InkCompletedCourseEntryReset.
Proof.
  unfold InkCompletedCourseEntryReset.
  intros version m t m' result Hcall.
  inversion Hcall; subst.
  destruct (ier_init_source version) as [Hbody Hnormal].
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hrun;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
      as (reset_le & before & pre & rest & Htrace & Hprefix & Hrest)
  end.
  destruct (ibk_split_sequence _ _ _ _ ier_reset _ _ _ _ _ eq_refl Hrest)
    as (after_le & after & reset_t & suf & Hresttrace & Hreset & Hsuffix).
  destruct (ier_reset_effect _ _ _ _ _ _ _ _ Hreset)
    as (mb & mo & Hstate & Hstore & Hload & -> & _).
  unfold InkCourseResetCheckpoint.
  match goal with
  | He : function_entry2 _ _ _ _ ?env ?initial_le ?initial_m,
    Hs : ocn_exec _ _ _ _ (ier_suffix _) _ ?last_le ?last ?out |- _ =>
    exists env, initial_le, initial_m, last_le, last, out,
      reset_le, before, after_le, after, pre, suf, mb, mo
  end.
  repeat first [eassumption | split].
  subst; reflexivity.
Qed.

Definition ier_call kind := Scall None
  (Evar (ier_id kind) (Tfunction [] tvoid cc_default)) [].
Lemma ier_named_call : forall version kind e le m t le' m' out,
  e ! (ier_id kind) = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ier_call kind) t le' m' out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version))
    m (Internal (ier_body version kind)) [] t m' result.
Proof.
  intros version kind e le m t le' m' out Hlocal Hrun.
  unfold ier_call in Hrun. inversion Hrun; subst; clear Hrun.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (ier_selected_resolves version kind) as (fb & Hfs & Hff).
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory
      (Evar ?id (Tfunction ?args ?result ?cc)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory id args result cc fb vf
        Hlocal Hfs Hr)); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hff in Hfind; inversion Hfind; subst fd end.
  match goal with Ha : eval_exprlist _ _ _ _ [] _ _ |- _ => inversion Ha; subst end.
  eexists; eassumption.
Qed.

Definition ier_warp_prefix version := ocn_prefix_items 2 (fn_body (ier_body version IERAfterWarp)).
Definition ier_warp_choice version := ibk_head (rank12b_drop_sequences 2
  (fn_body (ier_body version IERAfterWarp))).
Definition ier_warp_reads version := ocn_prefix_items 2 (ier_warp_choice version).
Definition ier_warp_check version := rank12b_drop_sequences 2 (ier_warp_choice version).
Definition ier_warp_guard version := match ier_warp_check version with
| Sifthenelse guard _ _ => guard | _ => Econst_int Int.zero tint end.
Definition ier_warp_active version := match ier_warp_check version with
| Sifthenelse _ yes _ => yes | _ => Sskip end.
Definition ier_warp_suffix version := rank12b_drop_sequences 3
  (fn_body (ier_body version IERAfterWarp)).
Definition ier_active_prefix version := ocn_prefix_items 8 (ier_warp_active version).
Definition ier_active_suffix version := rank12b_drop_sequences 9 (ier_warp_active version).

Lemma ier_warp_source : forall version,
  fn_vars (ier_body version IERAfterWarp) = [] /\
  fn_body (ier_body version IERAfterWarp) =
    ocn_prepend (ier_warp_prefix version)
      (Ssequence (ier_warp_choice version) (ier_warp_suffix version)) /\
  ier_warp_choice version = ocn_prepend (ier_warp_reads version) (ier_warp_check version) /\
  ier_warp_check version =
    Sifthenelse (ier_warp_guard version) (ier_warp_active version) Sskip /\
  ier_warp_active version = ocn_prepend (ier_active_prefix version)
    (Ssequence (ier_call IERInit) (ier_active_suffix version)) /\
  forallb ibk_normal (ier_warp_prefix version) = true /\
  ibk_normal (ier_warp_choice version) = true /\
  forallb ibk_normal (ier_warp_reads version) = true /\
  forallb ibk_normal (ier_active_prefix version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Definition InkActiveWarpResetEvidence version e le m t le' m' out : Prop :=
  exists call_le call_m after_le after_m pre mid suf result,
    t = pre ++ (mid ++ suf) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ocn_prepend (ier_active_prefix version) Sskip) pre call_le call_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e call_le call_m
      (ier_call IERInit) mid after_le after_m Out_normal /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      call_m (Internal (ier_body version IERInit)) [] mid after_m result /\
    InkCourseResetCheckpoint version call_m mid after_m result /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e after_le after_m
      (ier_active_suffix version) suf le' m' out.

Theorem ier_active_warp_reaches_real_reset : forall version e le m t le' m' out,
  e ! (ier_id IERInit) = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ier_warp_active version) t le' m' out ->
  InkActiveWarpResetEvidence version e le m t le' m' out.
Proof.
  intros version e le m t le' m' out Hlocal Hrun.
  destruct (ier_warp_source version)
    as (_ & _ & _ & _ & Hbody & _ & _ & _ & Hnormal).
  rewrite Hbody in Hrun.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (call_le & call_m & pre & rest & Htrace & Hprefix & Hrest).
  destruct (ibk_split_sequence _ _ _ _ (ier_call IERInit) _ _ _ _ _ eq_refl Hrest)
    as (after_le & after_m & mid & suf & Hresttrace & Hcall & Hsuffix).
  destruct (ier_named_call version IERInit _ _ _ _ _ _ _ Hlocal Hcall) as [result Hactual].
  pose proof (ier_completed_init_has_zero_depth_checkpoint _ _ _ _ _ Hactual) as Hreset.
  unfold InkActiveWarpResetEvidence.
  exists call_le, call_m, after_le, after_m, pre, mid, suf, result.
  repeat first [eassumption | split]. subst; reflexivity.
Qed.

(** The complete warp initializer either takes its actual inactive-Mario
    guard, or reaches the reset through the resolved internal call.
    Prefix helpers are not assumed to preserve memory or action. *)
Definition InkCompletedWarpResetChoice : Prop := forall version m t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ier_body version IERAfterWarp)) [] t m' result ->
  exists le first_le first_m test_le test_m after_le after_m last_le out t1 t2 t3 t4,
    t = t1 ++ ((t2 ++ t3) ++ t4) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (ocn_prepend (ier_warp_prefix version) Sskip) t1 first_le first_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env first_le first_m
      (ocn_prepend (ier_warp_reads version) Sskip) t2 test_le test_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env test_le test_m
      (ier_warp_check version) t3 after_le after_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env after_le after_m
      (ier_warp_suffix version) t4 last_le m' out /\
    (ocn_test_value (Clight.globalenv (selected_clight_target version)) empty_env
       test_le test_m (ier_warp_guard version) false \/
     (ocn_test_value (Clight.globalenv (selected_clight_target version)) empty_env
       test_le test_m (ier_warp_guard version) true /\
      InkActiveWarpResetEvidence version empty_env test_le test_m t3 after_le after_m Out_normal)).

Theorem ier_completed_warp_resets_or_takes_inactive_guard : InkCompletedWarpResetChoice.
Proof.
  unfold InkCompletedWarpResetChoice.
  intros version m t m' result Hcall.
  destruct (ier_warp_source version)
    as (Hvars & Hbody & Hchoice & Hcheck & _ & HprefixNormal & HchoiceNormal & HreadNormal & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ HprefixNormal Hr)
      as (first_le & first_m & t1 & rest & Htrace & Hprefix & Hrest)
  end.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HchoiceNormal Hrest)
    as (after_le & after_m & branch & t4 & HrestTrace & Hbranch & Hsuffix).
  rewrite Hchoice in Hbranch.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ HreadNormal Hbranch)
    as (test_le & test_m & t2 & t3 & HbranchTrace & Hreads & Htest).
  assert (ocn_test_value (Clight.globalenv (selected_clight_target version)) empty_env
    test_le test_m (ier_warp_guard version) false \/
    (ocn_test_value (Clight.globalenv (selected_clight_target version)) empty_env
      test_le test_m (ier_warp_guard version) true /\
     InkActiveWarpResetEvidence version empty_env test_le test_m t3 after_le after_m Out_normal))
    as Halternative.
  { rewrite Hcheck in Htest. inversion Htest; subst.
    destruct b; cbn beta iota in *.
    - right. split.
      + unfold ocn_test_value; eauto.
      + eapply ier_active_warp_reaches_real_reset; [reflexivity|eassumption].
    - left. unfold ocn_test_value; eauto. }
  match type of Hprefix with ocn_exec _ _ ?start_le _ _ _ _ _ _ =>
  match type of Hsuffix with ocn_exec _ _ _ _ _ _ ?last_le _ ?out =>
    exists start_le, first_le, first_m, test_le, test_m,
      after_le, after_m, last_le, out, t1, t2, t3, t4
  end end.
  repeat first [eassumption | split]. subst; reflexivity.
Qed.

Definition InkCourseEntryResetBoundary : Prop :=
  InkCompletedCourseEntryReset /\ InkCompletedWarpResetChoice.
Theorem ier_course_entry_reset_checked : InkCourseEntryResetBoundary.
Proof.
  split; [exact ier_completed_init_has_zero_depth_checkpoint |
    exact ier_completed_warp_resets_or_takes_inactive_guard].
Qed.
