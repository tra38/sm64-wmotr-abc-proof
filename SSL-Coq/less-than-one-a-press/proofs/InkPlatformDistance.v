(** The actual support-distance check before a later platform departure.
    This starts after the real floor call has supplied its height. It proves
    the absf call and both clearing stores, not the live floor selection or
    an unchanged scheduler interval. Display height is unrestricted. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_helpers jp_object_helpers.
From LessThanOneAPress.Proofs Require Import GameTypes InkPlatformSource
  InkPlatformDeparture InkPlatformMovementSource InkBackwardSource InkBackwardExecution
  InkBodyResetFrame InkBodyResetConstruction InkCopyCaller InkFloorListEffects
  ObjectContactNecessity ContactConsumerExecution SecretContactExecution Area2Rank12BContact
  SelectedClightTarget UpperElevatorQueryResolution CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ipdist_abs_body version := match version with
| VersionUS => us_object_helpers.f_absf | VersionJP => jp_object_helpers.f_absf end.
Definition ipdist_abs_id := us_object_helpers._absf.

Lemma ipdist_abs_us_source :
  nth_error us_object_helpers.global_definitions
    (ueqr_definition_index ipdist_abs_id us_object_helpers.global_definitions) =
    Some (ipdist_abs_id, Gfun (Internal (ipdist_abs_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma ipdist_abs_us_member :
  In (ipdist_abs_id, Gfun (Internal (ipdist_abs_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 19 us_units).
  - exact (us_nlist_at_nIn _ 19 us_units).
  - eapply nth_error_In. exact ipdist_abs_us_source.
Qed.
Lemma ipdist_abs_us_selection :
  us_normalized_global_definition_map ! ipdist_abs_id =
    Some (Gfun (Internal (ipdist_abs_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact ipdist_abs_us_member.
Qed.
Lemma ipdist_abs_no_repair :
  us_selected_definition_needs_viewport_repair
    (ipdist_abs_id, Gfun (Internal (ipdist_abs_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma ipdist_abs_us_selected :
  In (ipdist_abs_id, Gfun (Internal (ipdist_abs_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ipdist_abs_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact ipdist_abs_us_selection.
Qed.
Lemma ipdist_abs_jp_source :
  (prog_defmap (nlist_at 19 jp_cleaned_units)) ! ipdist_abs_id =
    Some (Gfun (Internal (ipdist_abs_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem ipdist_abs_resolves : forall version,
  exists b, Genv.find_symbol (Clight.globalenv (selected_clight_target version)) ipdist_abs_id = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ipdist_abs_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ipdist_abs_us_selected.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 19 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 19 jp_cleaned_units).
    + exact ipdist_abs_jp_source.
Qed.

(** This is the exact C branch, including its signed-zero/NaN behavior,
    rather than an assumption that absf is a mathematical library function. *)
Definition ipdist_abs x :=
  if Float32.cmp Cge x Float32.zero then x else Float32.neg x.
Lemma ipdist_abs_shape : forall version,
  fn_vars (ipdist_abs_body version) = [] /\
  fn_params (ipdist_abs_body version) = [(us_object_helpers._x, tfloat)] /\
  fn_body (ipdist_abs_body version) = Sifthenelse
    (Ebinop Oge (Etempvar us_object_helpers._x tfloat) (Econst_int Int.zero tint) tint)
    (Sreturn (Some (Etempvar us_object_helpers._x tfloat)))
    (Sreturn (Some (Eunop Oneg (Etempvar us_object_helpers._x tfloat) tfloat))).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ipdist_abs_execution : forall version m x t after result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ipdist_abs_body version)) [Vsingle x] t after result ->
  t = E0 /\ after = m /\ result = Vsingle (ipdist_abs x).
Proof.
  intros version m x t after result Hcall.
  destruct (ipdist_abs_shape version) as (Hvars & Hparams & Hbody).
  assert (fn_return (ipdist_abs_body version) = tfloat) as Hreturn by (destruct version; reflexivity).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! us_object_helpers._x = Some (Vsingle x)) as Hx by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr; inversion Hr; subst; clear Hr end.
  match goal with Hr : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hr; subst; clear Hr end.
  2: match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vsingle x) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  match goal with Hs : sem_binary_operation _ _ _ _ _ _ _ = Some ?answer |- _ =>
    change (Some (Val.of_bool (Float32.cmp Cge x Float32.zero)) = Some answer) in Hs;
    inversion Hs; subst; clear Hs end.
  unfold ipdist_abs. destruct (Float32.cmp Cge x Float32.zero) eqn:Hsign.
  all: match goal with Hb : bool_val _ _ _ = Some ?taken |- _ =>
    first [change (Some true = Some taken) in Hb | change (Some false = Some taken) in Hb];
    inversion Hb; subst; clear Hb end.
  all: cbn beta iota in *.
  all: match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn _) _ _ _ _ |- _ =>
    inversion Hr; subst; clear Hr end.
  all: repeat match goal with Hr : eval_expr _ _ _ _ (Eunop _ _ _) _ |- _ =>
    inversion Hr; subst; clear Hr end.
  all: try solve [match goal with Hl : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion Hl end].
  all: repeat match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vsingle x) by (eapply ocn_temp_value; eauto); subst v; clear Hr end.
  all: repeat match goal with Hs : sem_unary_operation _ _ _ _ = Some _ |- _ =>
    cbn in Hs; inversion Hs; subst; clear Hs end.
  all: match goal with Ho : outcome_result_value _ _ _ _ |- _ =>
    rewrite Hreturn in Ho; destruct Ho as [_ Hcast] end.
  all: repeat match goal with Hs : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hs; inversion Hs; subst; clear Hs end.
  all: repeat split; reflexivity.
Qed.

Definition ipdist_tail version := rank12b_drop_sequences 5 (fn_body (ipd_body version IPDUpdate)).
Definition ipdist_guard version := ibk_head (ipdist_tail version).
Definition ipdist_delta := Ebinop Osub (Etempvar IPD._marioY tfloat)
  (Etempvar IPD._floorHeight tfloat) tfloat.
Definition ipdist_abs_call := Scall (Some IPD._t'2)
  (Evar ipdist_abs_id (Tfunction [tfloat] tfloat cc_default)) [ipdist_delta].
Definition ipdist_four := Float32.of_bits (Int.repr 1082130432).
Definition ipdist_near_test := Ebinop Olt (Etempvar IPD._t'2 tfloat)
  (Econst_single ipdist_four tfloat) tint.
Definition ipdist_cases version := match ipd_switch version with
| Sswitch _ cases => cases | _ => LSnil end.
Definition ipdist_clear_object := Ssequence
  (Sset IPD._t'13 (Evar IPD._gMarioObject ipd_object))
  (Sassign (ibr_field IPD._t'13 IPD._Object IPD._platform ipd_object) ipd_null).
Definition ipdist_far := Ssequence
  (Sassign (Evar IPD._gMarioPlatform ipd_object) ipd_null)
  (Ssequence ipdist_clear_object Sbreak).

Lemma ipdist_tail_source : forall version,
  ipdist_tail version = Ssequence (ipdist_guard version) (ipd_switch version) /\
  ipdist_guard version = Ssequence ipdist_abs_call
    (Sifthenelse ipdist_near_test
      (Sset IPD._awayFromFloor (Econst_int Int.zero tint))
      (Sset IPD._awayFromFloor (Econst_int Int.one tint))) /\
  ipd_switch version = Sswitch (Etempvar IPD._awayFromFloor tuint) (ipdist_cases version) /\
  seq_of_labeled_statement (select_switch 1 (ipdist_cases version)) =
    Ssequence ipdist_far (Ssequence (ipd_near version) Sskip) /\
  ibk_normal (ipdist_guard version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ipdist_delta_value : forall ge e le m y floor answer,
  le ! IPD._marioY = Some (Vsingle y) ->
  le ! IPD._floorHeight = Some (Vsingle floor) ->
  eval_expr ge e le m ipdist_delta answer ->
  answer = Vsingle (Float32.sub y floor).
Proof.
  intros ge e le m y floor answer Hy Hfloor Hr. inversion Hr; subst.
  2: match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl end.
  match goal with H : eval_expr _ _ _ _ (Etempvar IPD._marioY _) ?v |- _ =>
    assert (v = Vsingle y) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : eval_expr _ _ _ _ (Etempvar IPD._floorHeight _) ?v |- _ =>
    assert (v = Vsingle floor) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some ?value |- _ =>
    change (Some (Vsingle (Float32.sub y floor)) = Some value) in H; congruence end.
Qed.

Lemma ipdist_distance_call : forall version e le m y floor t le' after out,
  e ! ipdist_abs_id = None ->
  le ! IPD._marioY = Some (Vsingle y) ->
  le ! IPD._floorHeight = Some (Vsingle floor) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ipdist_abs_call t le' after out ->
  t = E0 /\ after = m /\ out = Out_normal /\
  le' = PTree.set IPD._t'2 (Vsingle (ipdist_abs (Float32.sub y floor))) le.
Proof.
  intros version e le m y floor t le' after out Hlocal Hy Hfloor Hrun.
  inversion Hrun; subst.
  match goal with H : classify_fun _ = _ |- _ => cbn in H; inversion H; subst end.
  destruct (ipdist_abs_resolves version) as (fb & Hsymbol & Hfun).
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  match goal with Htype : type_of_fundef (Internal _) = _ |- _ =>
    assert (type_of_fundef (Internal (ipdist_abs_body version)) =
      Tfunction [tfloat] tfloat cc_default) as T by (destruct version; reflexivity);
    rewrite T in Htype; inversion Htype; subst end.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ ipdist_delta ?v |- _ =>
    assert (v = Vsingle (Float32.sub y floor)) by (eapply ipdist_delta_value; eauto); subst v end.
  match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : ClightBigstep.eval_funcall function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (ipdist_abs_execution version _ _ _ _ _ H) as (-> & -> & ->) end.
  repeat split; reflexivity.
Qed.

Lemma ipdist_guard_value : forall version e le m y floor t le' after out,
  e ! ipdist_abs_id = None ->
  le ! IPD._marioY = Some (Vsingle y) ->
  le ! IPD._floorHeight = Some (Vsingle floor) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipdist_guard version) t le' after out ->
  t = E0 /\ after = m /\
  le' ! IPD._awayFromFloor = Some (Vint (if
    Float32.cmp Clt (ipdist_abs (Float32.sub y floor)) ipdist_four
    then Int.zero else Int.one)).
Proof.
  intros version e le m y floor t le' after out Hlocal Hy Hfloor Hrun.
  destruct (ipdist_tail_source version) as (_ & Hguard & _). rewrite Hguard in Hrun.
  destruct (ibk_split_sequence _ _ _ _ ipdist_abs_call _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & -> & Hcall & Hbranch).
  destruct (ipdist_distance_call _ _ _ _ _ _ _ _ _ _ Hlocal Hy Hfloor Hcall)
    as (-> & -> & _ & ->).
  inversion Hbranch; subst.
  match goal with H : eval_expr _ _ _ _ ipdist_near_test _ |- _ => inversion H; subst; clear H end.
  2: match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H end.
  match goal with H : eval_expr _ _ _ _ (Etempvar IPD._t'2 _) ?v |- _ =>
    assert (v = Vsingle (ipdist_abs (Float32.sub y floor))) by
      (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst v end.
  match goal with H : eval_expr _ _ _ _ (Econst_single _ _) _ |- _ =>
    inversion H; subst; clear H end.
  2: match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H end.
  match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some ?value |- _ =>
    change (Some (Val.of_bool (Float32.cmp Clt
      (ipdist_abs (Float32.sub y floor)) ipdist_four)) = Some value) in H;
    inversion H; subst end.
  destruct (Float32.cmp Clt (ipdist_abs (Float32.sub y floor)) ipdist_four).
  all: match goal with H : bool_val _ _ _ = Some ?taken |- _ =>
    first [change (Some true = Some taken) in H | change (Some false = Some taken) in H];
    inversion H; subst end.
  all: cbn beta iota in *.
  all: match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion H; subst end.
  all: match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
  all: repeat split; try reflexivity; apply PTree.gss.
Qed.

Lemma ipdist_far_guard : forall version e le m y floor t le' after out,
  e ! ipdist_abs_id = None ->
  le ! IPD._marioY = Some (Vsingle y) ->
  le ! IPD._floorHeight = Some (Vsingle floor) ->
  Float32.cmp Clt (ipdist_abs (Float32.sub y floor)) ipdist_four = false ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipdist_guard version) t le' after out ->
  t = E0 /\ after = m /\ le' ! IPD._awayFromFloor = Some (Vint Int.one).
Proof.
  intros version e le m y floor t le' after out Ha Hy Hfloor Hfar Hrun.
  pose proof (ipdist_guard_value _ _ _ _ _ _ _ _ _ _ Ha Hy Hfloor Hrun) as H.
  now rewrite Hfar in H.
Qed.

(** Both stores in the distance-failure case. This branch has a different
    generated temporary from the ownerless-floor branch proved earlier. *)
Lemma ipdist_far_stores : forall version e le m pb gb ob oo t le' after out,
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ipdist_far t le' after out ->
  t = E0 /\ out = Out_break /\
  Mem.load Mptr after pb 0 = Some (Vint Int.zero) /\
  Mem.load Mptr after ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) = Some (Vint Int.zero) /\
  forall chunk b ofs,
    ifl_disjoint pb 0 4 chunk b ofs ->
    ifl_disjoint ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) 4 chunk b ofs ->
    Mem.load chunk after b ofs = Mem.load chunk m b ofs.
Proof.
  intros version e le m pb gb ob oo t le' after out Hpl Hml Hps Hms Hpo Hm Hrun.
  assert (pb <> gb) as Hpg.
  { eapply Genv.global_addresses_distinct; [|exact Hps|exact Hms]. discriminate. }
  unfold ipdist_far in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sassign (Evar IPD._gMarioPlatform ipd_object) ipd_null) _ _ _ _ _ eq_refl Hrun)
    as (middle & m1 & pre & suf & -> & Hfirst & Hrest).
  destruct (ipd_null_store (Clight.globalenv (selected_clight_target version)) e le m
    (Evar IPD._gMarioPlatform ipd_object) pb Ptrofs.zero _ _ _ _ eq_refl
    ltac:(intros loc off bf Hl; inversion Hl; subst; try congruence;
      assert (loc = pb) by congruence; subst; auto) Hfirst) as (-> & -> & _ & Hstore).
  assert (Mem.load Mptr m1 gb 0 = Some (Vptr ob oo)) as Hm1.
  { rewrite <- Hm. eapply Mem.load_store_other; [exact Hstore|left; congruence]. }
  destruct (ibk_split_sequence _ _ _ _ ipdist_clear_object _ _ _ _ _ eq_refl Hrest)
    as (last & m2 & t2 & t3 & -> & Hobject & Hbreak).
  inversion Hbreak; subst; clear Hbreak.
  unfold ipdist_clear_object in Hobject.
  destruct (ibk_split_sequence _ _ _ _
    (Sset IPD._t'13 (Evar IPD._gMarioObject ipd_object)) _ _ _ _ _ eq_refl Hobject)
    as (read & m3 & t4 & t5 & -> & Hread & Hwrite).
  inversion Hread; subst; clear Hread.
  match goal with H : eval_expr _ _ _ _ (Evar IPD._gMarioObject _) ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply ipd_global_value; eauto); subst v end.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hwrite.
  lazymatch goal with H : ClightBigstep.exec_stmt _ _ _ ?temps ?memory (Sassign _ _) _ _ _ _ |- _ =>
    destruct (ipd_null_store (Clight.globalenv (selected_clight_target version)) e temps memory
      (ibr_field IPD._t'13 IPD._Object IPD._platform ipd_object)
      ob (Ptrofs.add oo (Ptrofs.repr 532)) _ _ _ _ eq_refl
      ltac:(intros loc off bf Hl;
        eapply (ibcc_field_location (Clight.globalenv (selected_clight_target version))
          e temps memory (ibr_base IPD._t'13 IPD._Object) IPD._Object IPD._platform
          ipd_object ob oo 532 loc off bf);
        [reflexivity| |exact (proj2 (ipd_fields version))|exact Hl];
        intros; eapply ibcc_deref_struct; [|eassumption]; apply PTree.gss) H)
      as (-> & -> & _ & Hstore2) end.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore2 Mptr pb 0) by (left; congruence).
    exact (Mem.load_store_same _ _ _ _ _ _ Hstore).
  - split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore2)|].
    intros chunk b ofs Houtside1 Houtside2.
    match type of Hstore with Mem.store _ _ _ _ _ = Some ?middleMemory =>
      transitivity (Mem.load chunk middleMemory b ofs) end;
      eapply Mem.load_store_other; [exact Hstore2|exact Houtside2|exact Hstore|exact Houtside1].
Qed.

Definition InkPlatformDistanceClearing : Prop := forall version e le m y floor pb gb ob oo t le' after out,
  e ! ipdist_abs_id = None ->
  le ! IPD._marioY = Some (Vsingle y) ->
  le ! IPD._floorHeight = Some (Vsingle floor) ->
  Float32.cmp Clt (ipdist_abs (Float32.sub y floor)) ipdist_four = false ->
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipdist_tail version) t le' after out ->
  t = E0 /\ out = Out_normal /\
  Mem.load Mptr after pb 0 = Some (Vint Int.zero) /\
  Mem.load Mptr after ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) = Some (Vint Int.zero) /\
  forall chunk b ofs, ifl_disjoint pb 0 4 chunk b ofs ->
    ifl_disjoint ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) 4 chunk b ofs ->
    Mem.load chunk after b ofs = Mem.load chunk m b ofs.

Theorem ipdist_failed_distance_clears_support : InkPlatformDistanceClearing.
Proof.
  intros version e le m y floor pb gb ob oo t le' after out
    Hlocal Hy Hfloor Hfar Hpl Hml Hps Hms Hpo Hm Hrun.
  destruct (ipdist_tail_source version) as (Htail & Hguard & Hswitch & Hcase & Hnormal).
  rewrite Htail in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (checked & middle & pre & suf & -> & Htest & Hchoose).
  destruct (ipdist_far_guard _ _ _ _ _ _ _ _ _ _ Hlocal Hy Hfloor Hfar Htest)
    as (-> & -> & Hone).
  rewrite Hswitch in Hchoose. inversion Hchoose; subst; clear Hchoose.
  match goal with H : eval_expr _ _ _ _ (Etempvar IPD._awayFromFloor _) ?v |- _ =>
    assert (v = Vint Int.one) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : sem_switch_arg _ _ = Some ?n |- _ =>
    change (Some 1 = Some n) in H; inversion H; subst end.
  match goal with H : ClightBigstep.exec_stmt _ _ _ _ _
    (seq_of_labeled_statement (select_switch _ _)) _ _ _ _ |- _ =>
    rewrite Hcase in H; inversion H; subst; clear H end.
  all: match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ ipdist_far _ _ _ _ |- _ =>
    destruct (ipdist_far_stores _ _ _ _ _ _ _ _ _ _ _ _
      Hpl Hml Hps Hms Hpo Hm H) as (-> & Hout & Hclear & Hobj & Hframe);
    try discriminate Hout; subst end.
  simpl. repeat split; auto.
Qed.

(** The no-floor sentinel and the two heights used by the vertical candidate.
    This is a finite check of the guard, not a classification of live floors. *)
Inductive ipdist_sample := IPDistMiss | IPDistStatic | IPDistTop.
Definition ipdist_height sample := Float32.of_bits (Int.repr (match sample with
| IPDistMiss => 3324764160 | IPDistStatic => 1151336448 | IPDistTop => 1156733869 end)).
Definition ipdist_low := Float32.of_bits (Int.repr 1145044992).
Lemma ipdist_low_samples_fail : forall sample,
  Float32.cmp Clt (ipdist_abs (Float32.sub ipdist_low (ipdist_height sample))) ipdist_four = false.
Proof. intros []; vm_compute; reflexivity. Qed.

Definition InkLowPlatformCannotDepart : Prop :=
  forall version sample e le m pb gb ob oo t le' cleared out next tnext after result,
  e ! ipdist_abs_id = None ->
  le ! IPD._marioY = Some (Vsingle ipdist_low) ->
  le ! IPD._floorHeight = Some (Vsingle (ipdist_height sample)) ->
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipdist_tail version) t le' cleared out ->
  Mem.load Mptr next pb 0 = Mem.load Mptr cleared pb 0 ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) next
    (Internal (ipd_body version IPDApply)) [] tnext after result ->
  tnext = E0 /\ after = next.

Theorem ipdist_low_samples_cannot_depart : InkLowPlatformCannotDepart.
Proof.
  intros version sample e le m pb gb ob oo t le' cleared out next tnext after result
    Hlocal Hy Hfloor Hpl Hml Hps Hms Hpo Hm Hrun Hsame Happly.
  destruct (ipdist_failed_distance_clears_support _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hlocal Hy Hfloor (ipdist_low_samples_fail sample) Hpl Hml Hps Hms Hpo Hm Hrun)
    as (_ & _ & Hnull & _).
  rewrite Hnull in Hsame.
  exact (ipd_null_platform_call_cannot_depart _ _ _ _ _ _ Hps Hsame Happly).
Qed.


Lemma ipdist_null_floor_read : forall (ge : genv) e le m fb answer,
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vint Int.zero) ->
  eval_expr ge e le m (Evar IPD._floor ipd_surface) answer -> answer = Vint Int.zero.
Proof.
  intros ge e le m fb answer Hlocal Hload Hr. inversion Hr; subst.
  match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H; subst end; try congruence.
  match goal with H : deref_loc _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : Mem.loadv _ _ (Vptr ?loc _) = Some _ |- _ =>
    assert (loc = fb) by congruence; subst loc;
    change (Mem.load Mptr m fb 0 = Some answer) in H; congruence end.
Qed.

Lemma ipdist_null_floor_test : forall ge e le m answer,
  le ! IPD._t'10 = Some (Vint Int.zero) ->
  eval_expr ge e le m (ipd_nonnull IPD._t'10 ipd_surface) answer -> answer = Vint Int.zero.
Proof.
  intros ge e le m answer Htemp Hr. unfold ipd_nonnull in Hr. inversion Hr; subst.
  2: match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H end.
  match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : eval_expr _ _ _ _ ipd_null ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ipd_null_value; eauto); subst v end.
  match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; reflexivity end.
Qed.

Lemma ipdist_null_floor_owner_guard : forall version e le m fb t le' after out,
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vint Int.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipd_owner_guard version) t le' after out ->
  t = E0 /\ after = m /\ le' ! IPD._t'3 = Some (Vint Int.zero).
Proof.
  intros version e le m fb t le' after out Hlocal Hnull Hrun.
  destruct (ipd_source version) as (_ & _ & Hguard & _). rewrite Hguard in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sset IPD._t'10 (Evar IPD._floor ipd_surface)) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & -> & Hread & Hbranch).
  inversion Hread; subst; clear Hread.
  match goal with H : eval_expr _ _ _ _ (Evar IPD._floor _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ipdist_null_floor_read; eauto); subst v end.
  inversion Hbranch; subst; clear Hbranch.
  match goal with H : eval_expr _ _ _ _ (ipd_nonnull IPD._t'10 _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ipdist_null_floor_test; [apply PTree.gss|exact H]); subst v end.
  match goal with H : bool_val _ _ _ = Some ?taken |- _ =>
    change (Some false = Some taken) in H; inversion H; subst end.
  cbn beta iota in *.
  match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion H; subst end.
  match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in H; subst end.
  repeat split; try reflexivity; apply PTree.gss.
Qed.

Lemma ipdist_null_floor_near_branch : forall version e le m fb pb gb ob oo t le' after out,
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vint Int.zero) ->
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipd_owner_branch version) t le' after out ->
  t = E0 /\ Mem.load Mptr after pb 0 = Some (Vint Int.zero) /\
  Mem.load Mptr after ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) = Some (Vint Int.zero) /\
  forall chunk b ofs, ifl_disjoint pb 0 4 chunk b ofs ->
    ifl_disjoint ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) 4 chunk b ofs ->
    Mem.load chunk after b ofs = Mem.load chunk m b ofs.
Proof.
  intros version e le m fb pb gb ob oo t le' after out Hlocal Hnull Hpl Hml Hps Hms Hpo Hm Hrun.
  destruct (ipd_source version) as (_ & Hbranch & _). rewrite Hbranch in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (ipd_owner_guard version) _ _ _ _ _
    ltac:(destruct version; reflexivity) Hrun)
    as (guarded & middle & pre & suf & -> & Hguard & Hchoice).
  destruct (ipdist_null_floor_owner_guard _ _ _ _ _ _ _ _ _ Hlocal Hnull Hguard)
    as (-> & -> & Hzero).
  assert (exists yes, ipd_owner_choice version =
    Sifthenelse (Etempvar IPD._t'3 tint) yes (ipd_clear version)) as [yes HchoiceShape]
    by (destruct version; eexists; reflexivity).
  rewrite HchoiceShape in Hchoice. inversion Hchoice; subst.
  match goal with H : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : bool_val _ _ _ = Some ?taken |- _ =>
    change (Some false = Some taken) in H; inversion H; subst end.
  cbn beta iota in *.
  eapply ipd_clear_both; eauto.
Qed.

(** A missing floor clears support for every binary32 height returned.
    In particular no identification of NULL with the -11000 sentinel is used. *)
Definition InkNullFloorPlatformClearing : Prop :=
  forall version e le m y floor fb pb gb ob oo t le' after out,
  e ! ipdist_abs_id = None ->
  le ! IPD._marioY = Some (Vsingle y) ->
  le ! IPD._floorHeight = Some (Vsingle floor) ->
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vint Int.zero) ->
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipdist_tail version) t le' after out ->
  t = E0 /\ Mem.load Mptr after pb 0 = Some (Vint Int.zero) /\
  Mem.load Mptr after ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) = Some (Vint Int.zero) /\
  forall chunk b ofs, ifl_disjoint pb 0 4 chunk b ofs ->
    ifl_disjoint ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) 4 chunk b ofs ->
    Mem.load chunk after b ofs = Mem.load chunk m b ofs.

Theorem ipdist_missing_floor_clears_support : InkNullFloorPlatformClearing.
Proof.
  intros version e le m y floor fb pb gb ob oo t le' after out
    Habs Hy Hheight Hlocal Hnull Hpl Hml Hps Hms Hpo Hm Hrun.
  destruct (Float32.cmp Clt (ipdist_abs (Float32.sub y floor)) ipdist_four) eqn:Hnear.
  2: destruct (ipdist_failed_distance_clears_support _ _ _ _ _ _ _ _ _ _ _ _ _ _
       Habs Hy Hheight Hnear Hpl Hml Hps Hms Hpo Hm Hrun) as (Ht & _ & Hrest); auto.
  destruct (ipdist_tail_source version) as (Htail & _ & Hswitch & _ & Hnormal).
  rewrite Htail in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (checked & middle & pre & suf & -> & Htest & Hchoose).
  destruct (ipdist_guard_value _ _ _ _ _ _ _ _ _ _ Habs Hy Hheight Htest)
    as (-> & -> & Hzero).
  rewrite Hnear in Hzero.
  rewrite Hswitch in Hchoose. inversion Hchoose; subst; clear Hchoose.
  match goal with H : eval_expr _ _ _ _ (Etempvar IPD._awayFromFloor _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with H : sem_switch_arg _ _ = Some ?n |- _ =>
    change (Some 0 = Some n) in H; inversion H; subst end.
  assert (seq_of_labeled_statement (select_switch 0 (ipdist_cases version)) =
    Ssequence (ipd_near version) Sskip) as Hcase by (destruct version; reflexivity).
  match goal with H : ClightBigstep.exec_stmt _ _ _ _ _
    (seq_of_labeled_statement (select_switch _ _)) _ _ _ _ |- _ =>
    rewrite Hcase, (proj1 (ipd_source version)) in H end.
  cce_unroll_loop_free_exec.
  all: match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (ipd_owner_branch ?ver) _ _ _ _ |- _ =>
    destruct (ipdist_null_floor_near_branch ver _ _ _ _ _ _ _ _ _ _ _ _
      Hlocal Hnull Hpl Hml Hps Hms Hpo Hm H) as (-> & Hclear & Hobj & Hframe) end.
  all: repeat split; auto.
Qed.

(** No scheduler frame is assumed: a later changed-memory displacement
    after this missing-floor check needs a different value in this one cell. *)
Definition InkMissingFloorDepartureNeedsReplacement : Prop :=
  forall version e le m y floor fb pb gb ob oo t le' cleared out next tnext after result,
  e ! ipdist_abs_id = None ->
  le ! IPD._marioY = Some (Vsingle y) ->
  le ! IPD._floorHeight = Some (Vsingle floor) ->
  e ! IPD._floor = Some (fb, ipd_surface) ->
  Mem.load Mptr m fb 0 = Some (Vint Int.zero) ->
  e ! IPD._gMarioPlatform = None -> e ! IPD._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPD._gMarioObject = Some gb ->
  pb <> ob -> Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipdist_tail version) t le' cleared out ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) next
    (Internal (ipd_body version IPDApply)) [] tnext after result ->
  after <> next -> Mem.load Mptr next pb 0 <> Mem.load Mptr cleared pb 0.

Theorem ipdist_missing_floor_departure_needs_replacement :
  InkMissingFloorDepartureNeedsReplacement.
Proof.
  intros version e le m y floor fb pb gb ob oo t le' cleared out next tnext after result
    Ha Hy Hheight Hlocal Hnull Hpl Hml Hps Hms Hpo Hm Hrun Happly Hchanged Hsame.
  destruct (ipdist_missing_floor_clears_support _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Ha Hy Hheight Hlocal Hnull Hpl Hml Hps Hms Hpo Hm Hrun)
    as (_ & Hcleared & _).
  rewrite Hcleared in Hsame.
  destruct (ipd_null_platform_call_cannot_depart _ _ _ _ _ _ Hps Hsame Happly) as [_ E].
  contradiction.
Qed.

Definition InkPlatformDistanceBoundary : Prop :=
  InkPlatformDistanceClearing /\ InkLowPlatformCannotDepart /\
  InkNullFloorPlatformClearing /\ InkMissingFloorDepartureNeedsReplacement.
Theorem ipdist_platform_distance_checked : InkPlatformDistanceBoundary.
Proof.
  split; [exact ipdist_failed_distance_clears_support|].
  split; [exact ipdist_low_samples_cannot_depart|].
  split; [exact ipdist_missing_floor_clears_support|].
  exact ipdist_missing_floor_departure_needs_replacement.
Qed.
