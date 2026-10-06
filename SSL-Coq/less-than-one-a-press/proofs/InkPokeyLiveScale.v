(** The reached Pokey growth branch reads and updates one actual parent cell.

    This does not classify skipped growth, every parent history, or every
    child callback. The bound is on the real argument constructed after this
    particular completed approach call, rather than on an assumed live scale. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From Flocq Require Import BinarySingleNaN Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_obj_behaviors_2 jp_obj_behaviors_2.
From LessThanOneAPress.Proofs Require Import GameTypes InkStockBounceHeight
  InkFlyGuyCycleHeight InkCopyCaller InkControllerSource InkControllerEdge
  InkRawCopyExpressions InkFloorResetExecution InkBackwardExecution
  ObjectContactNecessity ObjectContactReadback ContactConsumerExecution
  InkQuicksandExpressions EyerokRank15LiveMovement SelectedClightTarget
  InkFlyGuyGrowthPrefix Area2Rank9ACoinFlight SecretContactExecution
  Area1PostCopyChildSource UpperElevatorQueryResolution ContactConsumerSource
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module PLS := us_obj_behaviors_2.
Local Instance ipls_precision_positive : Prec_gt_0 24.
Proof. constructor; reflexivity. Qed.
Local Instance ipls_precision_below_exponent : Prec_lt_emax 24 128.
Proof. constructor; reflexivity. Qed.

Lemma ipls_const_single_value : forall ge e le m number answer,
  eval_expr ge e le m (Econst_single number tfloat) answer -> answer = Vsingle number.
Proof.
  intros ge e le m number answer Hread. inversion Hread; subst; try reflexivity.
  match goal with Hl : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma ipls_approach_us_source :
  nth_error PLS.global_definitions
    (ueqr_definition_index PLS._approach_f32_ptr PLS.global_definitions) =
  Some (PLS._approach_f32_ptr, Gfun (Internal (ifch_approach_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma ipls_approach_us_member :
  In (PLS._approach_f32_ptr, Gfun (Internal (ifch_approach_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 24 us_units).
  - exact (us_nlist_at_nIn _ 24 us_units).
  - eapply nth_error_In. exact ipls_approach_us_source.
Qed.

Lemma ipls_approach_us_selection :
  us_normalized_global_definition_map ! PLS._approach_f32_ptr =
    Some (Gfun (Internal (ifch_approach_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact ipls_approach_us_member.
Qed.
Lemma ipls_approach_us_no_repair :
  us_selected_definition_needs_viewport_repair
    (PLS._approach_f32_ptr, Gfun (Internal (ifch_approach_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma ipls_approach_us_selected_member :
  In (PLS._approach_f32_ptr, Gfun (Internal (ifch_approach_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite ipls_approach_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact ipls_approach_us_selection.
Qed.
Lemma ipls_approach_jp_source :
  (prog_defmap (nlist_at 24 jp_cleaned_units)) ! PLS._approach_f32_ptr =
    Some (Gfun (Internal (ifch_approach_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem ipls_actual_approach_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PLS._approach_f32_ptr = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (ifch_approach_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact ipls_approach_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 24 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 24 jp_cleaned_units).
    + exact ipls_approach_jp_source.
Qed.

Definition ipls_body version := match version with
| VersionUS => us_obj_behaviors_2.f_bhv_pokey_body_part_update
| VersionJP => jp_obj_behaviors_2.f_bhv_pokey_body_part_update end.

Definition ipls_first {A : Type} (some_a some_b : option A) := match some_a with
| Some a => Some a | None => some_b end.
Fixpoint ipls_find_growth (s : statement) : option statement := match s with
| Ssequence first rest =>
    match first with
    | Ssequence (Sset id _) _ =>
      if Pos.eqb id PLS._t'83 then Some s
      else ipls_first (ipls_find_growth first) (ipls_find_growth rest)
    | _ => ipls_first (ipls_find_growth first) (ipls_find_growth rest) end
| Sifthenelse _ yes no => ipls_first (ipls_find_growth yes) (ipls_find_growth no)
| _ => None end.
Definition ipls_stage version := match ipls_find_growth (fn_body (ipls_body version)) with
| Some s => s | None => Sskip end.
Definition ipls_guard version := match ipls_stage version with
| Ssequence guard _ => guard | _ => Sskip end.
Definition ipls_growth version := match ipls_stage version with
| Ssequence _ (Sifthenelse _ growth _) => growth | _ => Sskip end.
Definition ipls_guard_tail version := match ipls_guard version with
| Ssequence _ (Ssequence _ (Ssequence _ tail)) => tail | _ => Sskip end.
Definition ipls_approach_stage version := match ipls_growth version with
| Ssequence first _ => first | _ => Sskip end.
Definition ipls_reload_stage version := match ipls_growth version with
| Ssequence _ rest => rest | _ => Sskip end.

Definition ipls_current := Evar PLS._gCurrentObject (tptr (Tstruct PLS._Object noattr)).
Definition ipls_parent temporary := ics_field temporary PLS._Object PLS._parentObj
  (tptr (Tstruct PLS._Object noattr)).
Definition ipls_factor_pointer version temporary := Ebinop Oadd
  (irc_raw_array version temporary) (Econst_int (Int.repr 29) tint) (tptr tfloat).
Definition ipls_factor version temporary := Ederef (ipls_factor_pointer version temporary) tfloat.
Definition ipls_one := Float32.of_bits (Int.repr 1065353216).
Definition ipls_delta := Float32.of_bits (Int.repr 1036831949).
Definition ipls_three := Float32.of_bits (Int.repr 1077936128).
Definition ipls_test := Ebinop Olt (Etempvar PLS._t'85 tfloat)
  (Econst_single ipls_one tfloat) tint.
Definition ipls_reads version current_temp parent_temp factor_temp :=
  ocn_prepend [Sset current_temp ipls_current;
    Sset parent_temp (ipls_parent current_temp);
    Sset factor_temp (ipls_factor version parent_temp)] Sskip.
Definition ipls_approach_call version := Scall None
  (Evar PLS._approach_f32_ptr
    (Tfunction [tptr tfloat;tfloat;tfloat] tint cc_default))
  [ipls_factor_pointer version PLS._t'82;
   Econst_single ipls_one tfloat;Econst_single ipls_delta tfloat].
Definition ipls_scale_argument := Ebinop Omul (Etempvar PLS._t'80 tfloat)
  (Econst_single ipls_three tfloat) tfloat.
Definition ipls_scale_call := Scall None
  (Evar PLS._cur_obj_scale (Tfunction [tfloat] tvoid cc_default)) [ipls_scale_argument].

Theorem ipls_growth_cut_is_generated : forall version,
  ipls_find_growth (fn_body (ipls_body version)) = Some (ipls_stage version) /\
  ipls_guard version = Ssequence (Sset PLS._t'83 ipls_current)
    (Ssequence (Sset PLS._t'84 (ipls_parent PLS._t'83))
      (Ssequence (Sset PLS._t'85 (ipls_factor version PLS._t'84))
        (ipls_guard_tail version))) /\
  (exists integer_guard,
    ipls_guard_tail version = Sifthenelse ipls_test integer_guard
      (Sset PLS._t'1 (Econst_int Int.zero tint))) /\
  cce_readonly_keep PLS._px (ipls_guard version) = true /\
  ipls_growth version = Ssequence (ipls_approach_stage version)
    (ipls_reload_stage version) /\
  ipls_approach_stage version = Ssequence (Sset PLS._t'81 ipls_current)
    (Ssequence (Sset PLS._t'82 (ipls_parent PLS._t'81))
      (ipls_approach_call version)) /\
  ipls_reload_stage version =
    ocn_prepend [Sset PLS._t'78 ipls_current;
      Sset PLS._t'79 (ipls_parent PLS._t'78);
      Sset PLS._t'80 (ipls_factor version PLS._t'79)] ipls_scale_call.
Proof. intros []; repeat split; try reflexivity; eexists; reflexivity. Qed.

Lemma ipls_parent_field_checked : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    PLS._Object PLS._parentObj 104 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    PLS._Object PLS._parentObj 104 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Lemma ipls_factor_pointer_value : forall version e le m temporary pb po answer,
  le ! temporary = Some (Vptr pb po) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_factor_pointer version temporary) answer ->
  answer = Vptr pb (Ptrofs.add po (Ptrofs.repr 252)).
Proof.
  intros version e le m temporary pb po answer Htemp Hread.
  unfold ipls_factor_pointer in Hread. inversion Hread; subst.
  - match goal with Harray : eval_expr _ _ _ _ (irc_raw_array version temporary) ?v |- _ =>
      assert (v = Vptr pb (Ptrofs.add po (Ptrofs.repr 136))) by
        (eapply irc_raw_array_value; eauto); subst v end.
    match goal with Hindex : eval_expr _ _ _ _ (Econst_int _ _) ?v |- _ =>
      assert (v = Vint (Int.repr 29)) by (eapply ocn_const_int_value; eauto); subst v end.
    match goal with Hsem : sem_binary_operation _ Oadd _ _ _ _ _ = Some answer |- _ =>
      cbn [typeof irc_raw_array sem_binary_operation sem_add classify_add sem_add_ptr_int] in Hsem;
      inversion Hsem; subst end.
    rewrite Ptrofs.add_assoc. reflexivity.
  - match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma ipls_approach_arguments : forall version e le m pb po values,
  le ! PLS._t'82 = Some (Vptr pb po) ->
  eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
    [ipls_factor_pointer version PLS._t'82;
     Econst_single ipls_one tfloat;Econst_single ipls_delta tfloat]
    [tptr tfloat;tfloat;tfloat] values ->
  values = [Vptr pb (Ptrofs.add po (Ptrofs.repr 252));Vsingle ipls_one;Vsingle ipls_delta].
Proof.
  intros version e le m pb po values Htemp Hargs.
  inversion Hargs; subst; clear Hargs.
  match goal with Hp : eval_expr _ _ _ _ (ipls_factor_pointer version PLS._t'82) ?v |- _ =>
    assert (v = Vptr pb (Ptrofs.add po (Ptrofs.repr 252))) by
      (eapply ipls_factor_pointer_value; eauto); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn [typeof ipls_factor_pointer sem_cast classify_cast] in Hcast;
    inversion Hcast; subst; clear Hcast end.
  match goal with Hrest : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Hrest; subst; clear Hrest end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_single ipls_one _) ?v |- _ =>
    apply ipls_const_single_value in Hr; subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hrest : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Hrest; subst; clear Hrest end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_single ipls_delta _) ?v |- _ =>
    apply ipls_const_single_value in Hr; subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hnil : eval_exprlist _ _ _ _ [] _ _ |- _ => inversion Hnil; subst end.
  reflexivity.
Qed.

(** The named native call resolves to the real linked internal helper and
    passes the pointer reconstructed from the actual parent receiver. *)
Theorem ipls_reached_call_is_actual_approach : forall version e le m pb po t le' m' out,
  e ! PLS._approach_f32_ptr = None ->
  le ! PLS._t'82 = Some (Vptr pb po) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_approach_call version) t le' m' out ->
  exists result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifch_approach_body version))
    [Vptr pb (Ptrofs.add po (Ptrofs.repr 252));Vsingle ipls_one;Vsingle ipls_delta]
    t m' result /\ le' = le /\ out = Out_normal.
Proof.
  intros version e le m pb po t le' m' out Hlocal Hparent Hrun.
  unfold ipls_approach_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (ipls_actual_approach_resolves version) as (fb & HfnSymbol & Hfunction).
  match goal with Hr : eval_expr _ _ _ _ (Evar PLS._approach_f32_ptr _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hargs : eval_exprlist _ _ _ _ _ _ ?values |- _ =>
    assert (values = [Vptr pb (Ptrofs.add po (Ptrofs.repr 252));Vsingle ipls_one;Vsingle ipls_delta])
      by (eapply ipls_approach_arguments; eauto); subst values end.
  eexists. repeat split; try reflexivity; eassumption.
Qed.

Lemma ipls_parent_read : forall version e le m temporary ob oo pb po answer,
  le ! temporary = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 104))) =
    Some (Vptr pb po) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_parent temporary) answer -> answer = Vptr pb po.
Proof.
  intros version e le m temporary ob oo pb po answer Htemp Hparent Hread.
  unfold ipls_parent in Hread.
  eapply (ice_field_read (Clight.globalenv (selected_clight_target version))
    e le m temporary PLS._Object PLS._parentObj (tptr (Tstruct PLS._Object noattr))
    ob oo 104 Mint32 (Vptr pb po) answer);
    [exact Htemp|apply ipls_parent_field_checked|reflexivity|exact Hparent|exact Hread].
Qed.

Lemma ipls_factor_location : forall version e le m temporary pb po b ofs bf,
  le ! temporary = Some (Vptr pb po) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_factor version temporary) b ofs bf ->
  b = pb /\ ofs = Ptrofs.add po (Ptrofs.repr 252) /\ bf = Full.
Proof.
  intros version e le m temporary pb po b ofs bf Htemp Hl.
  unfold ipls_factor, ipls_factor_pointer in Hl.
  destruct (iq_array_location _ _ _ _ (irc_raw_array version temporary)
    tfloat 80 29 pb (Ptrofs.add po (Ptrofs.repr 136)) b ofs bf
    eq_refl ltac:(intros; eapply irc_raw_array_value; eauto) Hl)
    as (-> & -> & ->).
  rewrite Ptrofs.add_assoc. repeat split; reflexivity.
Qed.

Lemma ipls_factor_read : forall version e le m temporary pb po factor answer,
  le ! temporary = Some (Vptr pb po) ->
  Mem.load Mfloat32 m pb (Ptrofs.unsigned (Ptrofs.add po (Ptrofs.repr 252))) =
    Some (Vsingle factor) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_factor version temporary) answer -> answer = Vsingle factor.
Proof.
  intros version e le m temporary pb po factor answer Htemp Hload Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ipls_factor_location _ _ _ _ _ _ _ _ _ _ Htemp Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  all: try match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn [typeof ipls_factor access_mode] in Hmode; inversion Hmode; subst end.
  match goal with Hread : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m pb
      (Ptrofs.unsigned (Ptrofs.add po (Ptrofs.repr 252))) = Some answer) in Hread;
    congruence end.
Qed.

Lemma ipls_actual_reads : forall version e le m current_temp parent_temp factor_temp
    cb ob oo pb po factor t le' m' out,
  current_temp <> parent_temp -> current_temp <> factor_temp ->
  parent_temp <> factor_temp ->
  e ! PLS._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PLS._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 104))) = Some (Vptr pb po) ->
  Mem.load Mfloat32 m pb (Ptrofs.unsigned (Ptrofs.add po (Ptrofs.repr 252))) = Some (Vsingle factor) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_reads version current_temp parent_temp factor_temp) t le' m' out ->
  m' = m /\ le' ! current_temp = Some (Vptr ob oo) /\
    le' ! parent_temp = Some (Vptr pb po) /\ le' ! factor_temp = Some (Vsingle factor).
Proof.
  intros version e le m current_temp parent_temp factor_temp cb ob oo pb po factor
    t le' m' out Hcp Hcf Hpf Hlocal Hsymbol Hcurrent Hparent Hfactor Hrun.
  unfold ipls_reads, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cbn [ocn_prepend] in Hrun. cce_unroll_loop_free_exec.
  lazymatch goal with Hr : eval_expr _ _ _ _ ipls_current ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply irc_global_pointer_read; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (ipls_parent current_temp) ?v |- _ =>
    assert (v = Vptr pb po) by
      (eapply ipls_parent_read; [apply PTree.gss|exact Hparent|exact Hr]); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (ipls_factor version parent_temp) ?v |- _ =>
    assert (v = Vsingle factor) by
      (eapply ipls_factor_read; [apply PTree.gss|exact Hfactor|exact Hr]); subst v end.
  repeat split; try reflexivity.
  - repeat rewrite PTree.gso by congruence. apply PTree.gss.
  - rewrite PTree.gso by congruence. apply PTree.gss.
  - apply PTree.gss.
Qed.

Lemma ipls_less_test_value : forall ge e le m old answer,
  le ! PLS._t'85 = Some (Vsingle old) ->
  ocn_test_value ge e le m ipls_test answer ->
  Float32.cmp Clt old ipls_one = answer.
Proof.
  intros ge e le m old answer Htemp [value [Hread Hbool]].
  unfold ipls_test in Hread. inversion Hread; subst.
  - match goal with Hr : eval_expr _ _ _ _ (Etempvar PLS._t'85 _) ?v |- _ =>
      assert (v = Vsingle old) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hc : eval_expr _ _ _ _ (Econst_single _ _) ?v |- _ =>
      apply ipls_const_single_value in Hc; subst v end.
    match goal with Hsem : sem_binary_operation _ Olt _ _ _ _ _ = Some value |- _ =>
      change (Some (Val.of_bool (Float32.cmp Clt old ipls_one)) = Some value) in Hsem;
      injection Hsem as Hvalue; rewrite <- Hvalue in Hbool end.
    destruct (Float32.cmp Clt old ipls_one); cbn in Hbool;
      vm_compute in Hbool; congruence.
  - match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
Qed.

(** A taken growth guard derives the factor limit from the actual descriptor
    read. The second integer guard is not assumed to preserve memory: its
    real generated statements are read-only. *)
Theorem ipls_taken_growth_guard_reads_less_than_one :
  forall version e le m cb ob oo pb po old t le' m' out flag,
  e ! PLS._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PLS._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 104))) = Some (Vptr pb po) ->
  Mem.load Mfloat32 m pb (Ptrofs.unsigned (Ptrofs.add po (Ptrofs.repr 252))) = Some (Vsingle old) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_guard version) t le' m' out ->
  le' ! PLS._t'1 = Some (Vint flag) -> flag <> Int.zero ->
  m' = m /\ Float32.cmp Clt old ipls_one = true.
Proof.
  intros version e le m cb ob oo pb po old t le' m' out flag
    Hlocal Hsymbol Hcurrent Hparent Hfactor Hrun Hflag Hnonzero.
  pose proof (proj1 (proj2 (proj2 (proj2 (ipls_growth_cut_is_generated version))))) as Hreadonly.
  pose proof (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun Hreadonly)
    as (_ & Hmemory & _). split; [exact Hmemory|].
  destruct (ipls_growth_cut_is_generated version) as (_ & Hshape & (integer_guard & Htail) & _).
  rewrite Hshape in Hrun.
  change (ocn_exec (Clight.globalenv (selected_clight_target version)) e le m (ocn_prepend
    [Sset PLS._t'83 ipls_current;
     Sset PLS._t'84 (ipls_parent PLS._t'83);
     Sset PLS._t'85 (ipls_factor version PLS._t'84)]
    (ipls_guard_tail version)) t le' m' out) in Hrun.
  destruct (ibk_split_prefix _ _
    [Sset PLS._t'83 ipls_current;
     Sset PLS._t'84 (ipls_parent PLS._t'83);
     Sset PLS._t'85 (ipls_factor version PLS._t'84)]
    (ipls_guard_tail version) _ _ _ _ _ _
    ltac:(reflexivity) Hrun)
    as (reads_le & reads_m & pre & suf & Htrace & Hreads & Hguard).
  change (ocn_exec (Clight.globalenv (selected_clight_target version)) e le m (ipls_reads version PLS._t'83 PLS._t'84 PLS._t'85)
    pre reads_le reads_m Out_normal) in Hreads.
  destruct (ipls_actual_reads version e le m PLS._t'83 PLS._t'84 PLS._t'85
    cb ob oo pb po old _ _ _ _ ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) Hlocal Hsymbol Hcurrent Hparent Hfactor Hreads)
    as (Hmem & _ & _ & HfactorTemp).
  subst reads_m. rewrite Htail in Hguard. inversion Hguard; subst; clear Hguard.
  destruct b.
  - eapply ipls_less_test_value; [exact HfactorTemp|].
    unfold ocn_test_value. eexists. split; eassumption.
  - match goal with Hzero : ClightBigstep.exec_stmt _ _ _ _ _ (Sset PLS._t'1 _) _ _ _ _ |- _ =>
      inversion Hzero; subst end.
    match goal with Hz : eval_expr _ _ _ _ (Econst_int Int.zero tint) ?v |- _ =>
      assert (v = Vint Int.zero) by (eapply ocn_const_int_value; eauto); subst v end.
    rewrite PTree.gss in Hflag. exfalso. apply Hnonzero. congruence.
Qed.



Definition ipls_parent_reads current_temp parent_temp :=
  ocn_prepend [Sset current_temp ipls_current;
    Sset parent_temp (ipls_parent current_temp)] Sskip.
Lemma ipls_actual_parent_reads : forall version e le m current_temp parent_temp
    cb ob oo pb po t le' m' out,
  current_temp <> parent_temp -> e ! PLS._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PLS._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 104))) = Some (Vptr pb po) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_parent_reads current_temp parent_temp) t le' m' out ->
  m' = m /\ le' ! current_temp = Some (Vptr ob oo) /\ le' ! parent_temp = Some (Vptr pb po).
Proof.
  intros version e le m current_temp parent_temp cb ob oo pb po t le' m' out
    Hfresh Hlocal Hsymbol Hcurrent Hparent Hrun.
  unfold ipls_parent_reads, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cbn [ocn_prepend] in Hrun. cce_unroll_loop_free_exec.
  lazymatch goal with Hr : eval_expr _ _ _ _ ipls_current ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply irc_global_pointer_read; eauto); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (ipls_parent current_temp) ?v |- _ =>
    assert (v = Vptr pb po) by
      (eapply ipls_parent_read; [apply PTree.gss|exact Hparent|exact Hr]); subst v end.
  repeat split; try reflexivity.
  - rewrite PTree.gso by congruence. apply PTree.gss.
  - apply PTree.gss.
Qed.


(** Signed ceilings: these do not require a nonnegative parent factor. A
    negative scale stays signed; finite multiplication is stated explicitly. *)
Theorem ipls_finite_factor_gives_scale_upper_bound : forall factor,
  rank9cf_finite factor ->
  rank9cf_finite (Float32.mul factor ipls_three) ->
  (rank9cf_real factor <= rank9cf_real ipls_one)%R ->
  (rank9cf_real (Float32.mul factor ipls_three) <= 3)%R.
Proof.
  intros factor Ffactor Fproduct Hfactor.
  assert (Fone : rank9cf_finite ipls_one) by (vm_compute; reflexivity).
  assert (Fthree : rank9cf_finite ipls_three) by (vm_compute; reflexivity).
  assert (Hone : (rank9cf_real ipls_one = 1)%R) by (vm_compute; nra).
  assert (Hthree : (rank9cf_real ipls_three = 3)%R) by (vm_compute; nra).
  assert (Hpeak : Float32.mul ipls_one ipls_three = ipls_three).
  { rewrite <- (Float32.of_to_bits (Float32.mul ipls_one ipls_three)).
    unfold ipls_three. f_equal; vm_compute; reflexivity. }
  assert (Fpeak : rank9cf_finite (Float32.mul ipls_one ipls_three))
    by (rewrite Hpeak; exact Fthree).
  assert (HpeakReal : (rank9cf_real (Float32.mul ipls_one ipls_three) = 3)%R) by (rewrite Hpeak; exact Hthree).
  rewrite <- HpeakReal. unfold rank9cf_real.
  rewrite (ifch_finite_product_real _ _ Ffactor Fthree Fproduct).
  rewrite (ifch_finite_product_real _ _ Fone Fthree Fpeak).
  apply round_le; [typeclasses eauto|typeclasses eauto|].
  change (rank9cf_real factor * rank9cf_real ipls_three <=
    rank9cf_real ipls_one * rank9cf_real ipls_three)%R.
  rewrite Hthree. nra.
Qed.

Theorem ipls_signed_finite_scale_gives_height_upper_bound : forall scale,
  rank9cf_finite scale ->
  rank9cf_finite (Float32.mul scale (Float32.of_int (Int.repr 20))) ->
  (rank9cf_real scale <= 3)%R ->
  (rank9cf_real (Float32.mul scale (Float32.of_int (Int.repr 20))) <= 60)%R.
Proof.
  intros scale Fscale Fheight Hscale.
  destruct (rank9cf_integer_exact 3 ltac:(lia)) as [H3 F3].
  destruct (rank9cf_integer_exact 20 ltac:(lia)) as [H20 F20].
  destruct (rank9cf_integer_exact 60 ltac:(lia)) as [H60 F60].
  assert (Hpeak : Float32.mul (rank9cf_integer 3) (rank9cf_integer 20) = rank9cf_integer 60).
  { rewrite <- (Float32.of_to_bits (Float32.mul (rank9cf_integer 3) (rank9cf_integer 20))).
    unfold rank9cf_integer. rewrite <- (Float32.of_to_bits (Float32.of_int (Int.repr 60))).
    f_equal; vm_compute; reflexivity. }
  assert (Fpeak : rank9cf_finite (Float32.mul (rank9cf_integer 3) (rank9cf_integer 20)))
    by (rewrite Hpeak; exact F60).
  change (rank9cf_real (Float32.mul scale (rank9cf_integer 20)) <= 60)%R.
  rewrite <- H60, <- Hpeak. unfold rank9cf_real.
  rewrite (ifch_finite_product_real _ _ Fscale F20 Fheight).
  rewrite (ifch_finite_product_real _ _ F3 F20 Fpeak).
  apply round_le; [typeclasses eauto|typeclasses eauto|].
  change (rank9cf_real scale * rank9cf_real (rank9cf_integer 20) <=
    rank9cf_real (rank9cf_integer 3) * rank9cf_real (rank9cf_integer 20))%R.
  rewrite H3, H20. nra.
Qed.



Local Transparent Float32.cmp Float32.compare.
Lemma ipls_taken_float_guard_has_real_bound : forall old,
  rank9cf_finite old -> Float32.cmp Clt old ipls_one = true ->
  (rank9cf_real old < 1)%R.
Proof.
  intros old Fo Hcmp.
  assert (Fone : rank9cf_finite ipls_one) by (vm_compute; reflexivity).
  assert (Hone : (rank9cf_real ipls_one = 1)%R) by (vm_compute; nra).
  unfold Float32.cmp, Float32.compare in Hcmp.
  rewrite (Bcompare_correct 24 128 old ipls_one Fo Fone) in Hcmp.
  unfold rank9cf_real in Hone |- *.
  destruct (Rcompare_spec (B2R 24 128 old) (B2R 24 128 ipls_one));
    simpl in Hcmp; try discriminate; lra.
Qed.

Definition ipls_receiver_separated (ob : block) oo pb po :=
  ob <> pb \/ Ptrofs.unsigned oo + 108 <= Ptrofs.unsigned po + 252 \/
    Ptrofs.unsigned po + 256 <= Ptrofs.unsigned oo + 104.
Definition ipls_receiver_frame cb ob oo before after :=
  Mem.load Mint32 after cb 0 = Mem.load Mint32 before cb 0 /\
  Mem.load Mint32 after ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 104))) =
    Mem.load Mint32 before ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 104))).
Lemma ipls_one_factor_store_frames_receivers : forall m m' cb ob oo pb po value,
  cb <> pb -> isbh_room oo -> isbh_room po -> ipls_receiver_separated ob oo pb po ->
  Mem.store Mfloat32 m pb (Ptrofs.unsigned (Ptrofs.add po (Ptrofs.repr 252))) value = Some m' ->
  ipls_receiver_frame cb ob oo m m'.
Proof.
  intros m m' cb ob oo pb po value HglobalSep HobjectRoom HparentRoom Hsep Hstore.
  split.
  - eapply Mem.load_store_other; [exact Hstore|]. left; exact HglobalSep.
  - eapply Mem.load_store_other; [exact Hstore|].
    unfold ipls_receiver_separated in Hsep.
    rewrite !isbh_address by (auto; lia).
    cbn [size_chunk]. intuition lia.
Qed.
Lemma ipls_receiver_frames_trans : forall cb ob oo a b c,
  ipls_receiver_frame cb ob oo a b -> ipls_receiver_frame cb ob oo b c ->
  ipls_receiver_frame cb ob oo a c.
Proof. intros cb ob oo a b c [Ha Hb] [Hc Hd]. split; congruence. Qed.

Lemma ipls_scale_argument_value : forall ge e le m factor answer,
  le ! PLS._t'80 = Some (Vsingle factor) ->
  eval_expr ge e le m ipls_scale_argument answer ->
  answer = Vsingle (Float32.mul factor ipls_three).
Proof.
  intros ge e le m factor answer Htemp Hread.
  unfold ipls_scale_argument in Hread. inversion Hread; subst.
  - match goal with Hr : eval_expr _ _ _ _ (Etempvar PLS._t'80 _) ?v |- _ =>
      assert (v = Vsingle factor) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hc : eval_expr _ _ _ _ (Econst_single ipls_three _) ?v |- _ =>
      apply ipls_const_single_value in Hc; subst v end.
    match goal with Hsem : sem_binary_operation _ Omul _ _ _ _ _ = Some answer |- _ =>
      change (Some (Vsingle (Float32.mul factor ipls_three)) = Some answer) in Hsem;
      congruence end.
  - match goal with Hl : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma ipls_reached_scale_argument_is_loaded_product : forall version e le m factor t le' m' out,
  le ! PLS._t'80 = Some (Vsingle factor) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ipls_scale_call t le' m' out ->
  eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
    [ipls_scale_argument] [tfloat] [Vsingle (Float32.mul factor ipls_three)].
Proof.
  intros version e le m factor t le' m' out Htemp Hrun.
  unfold ipls_scale_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hargs : eval_exprlist _ _ _ _ [ipls_scale_argument] _ ?args |- _ =>
    assert (args = [Vsingle (Float32.mul factor ipls_three)]) as Hvalue;
    [inversion Hargs; subst|
     rewrite <- Hvalue; exact Hargs] end.
  match goal with Hr : eval_expr _ _ _ _ ipls_scale_argument ?v |- _ =>
    assert (v = Vsingle (Float32.mul factor ipls_three)) by
      (eapply ipls_scale_argument_value; eauto); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hnil : eval_exprlist _ _ _ _ [] _ _ |- _ => inversion Hnil; subst end.
  reflexivity.
Qed.




Definition InkPokeyLiveScaleArgumentBoundary : Prop :=
  forall version e le m cb ob oo pb po old guard_t guard_le guard_m guard_out flag
      growth_t growth_le growth_m growth_out,
  cb <> pb -> isbh_room oo -> isbh_room po -> ipls_receiver_separated ob oo pb po ->
  e ! PLS._gCurrentObject = None -> e ! PLS._approach_f32_ptr = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) PLS._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 104))) = Some (Vptr pb po) ->
  Mem.load Mfloat32 m pb (Ptrofs.unsigned (Ptrofs.add po (Ptrofs.repr 252))) = Some (Vsingle old) ->
  rank9cf_finite old ->
  rank9cf_finite (Float32.mul (ifch_approach_result old ipls_one ipls_delta) ipls_three) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ipls_guard version) guard_t guard_le guard_m guard_out ->
  guard_le ! PLS._t'1 = Some (Vint flag) -> flag <> Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e guard_le guard_m
    (ipls_growth version) growth_t growth_le growth_m growth_out ->
  exists factor call_le call_m call_t,
    factor = ifch_approach_result old ipls_one ipls_delta /\
    Mem.load Mfloat32 call_m pb (Ptrofs.unsigned (Ptrofs.add po (Ptrofs.repr 252))) = Some (Vsingle factor) /\
    rank9cf_finite factor /\ (rank9cf_real factor <= 1)%R /\
    rank9cf_finite (Float32.mul factor ipls_three) /\
    (rank9cf_real (Float32.mul factor ipls_three) <= 3)%R /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e call_le call_m
      ipls_scale_call call_t growth_le growth_m growth_out /\
    eval_exprlist (Clight.globalenv (selected_clight_target version)) e call_le call_m
      [ipls_scale_argument] [tfloat] [Vsingle (Float32.mul factor ipls_three)].

Theorem ipls_reached_growth_constructs_bounded_scale_argument :
  InkPokeyLiveScaleArgumentBoundary.
Proof.
  unfold InkPokeyLiveScaleArgumentBoundary.
  intros version e le m cb ob oo pb po old guard_t guard_le guard_m guard_out flag
    growth_t growth_le growth_m growth_out HglobalSep HobjectRoom HparentRoom HreceiverSep
    Hlocal HapproachLocal Hsymbol Hcurrent Hparent Hfactor Fold Fproduct
    Hguard Hflag Hnonzero Hgrowth.
  destruct (ipls_taken_growth_guard_reads_less_than_one version e le m cb ob oo pb po old
    guard_t guard_le guard_m guard_out flag Hlocal Hsymbol Hcurrent Hparent Hfactor
    Hguard Hflag Hnonzero) as (HguardMemory & Hless).
  subst guard_m.
  destruct (ipls_growth_cut_is_generated version) as (_ & _ & _ & _ & HgrowthShape & HapproachShape & HreloadShape).
  rewrite HgrowthShape in Hgrowth.
  destruct (ibk_split_sequence _ _ _ _ (ipls_approach_stage version) _ _ _ _ _
    ltac:(rewrite HapproachShape; reflexivity) Hgrowth)
    as (approach_le & approach_m & approach_t & reload_t & HgrowthTrace & Happroach & Hreload).
  rewrite HapproachShape in Happroach.
  change (ocn_exec (Clight.globalenv (selected_clight_target version)) e guard_le m (ocn_prepend
    [Sset PLS._t'81 ipls_current;Sset PLS._t'82 (ipls_parent PLS._t'81)]
    (ipls_approach_call version)) approach_t approach_le approach_m Out_normal) in Happroach.
  destruct (ibk_split_prefix _ _
    [Sset PLS._t'81 ipls_current;Sset PLS._t'82 (ipls_parent PLS._t'81)]
    (ipls_approach_call version) _ _ _ _ _ _ ltac:(reflexivity) Happroach)
    as (parent_le & parent_m & parent_t & helper_t & HapproachTrace & HparentReads & HhelperCall).
  change (ocn_exec (Clight.globalenv (selected_clight_target version)) e guard_le m (ipls_parent_reads PLS._t'81 PLS._t'82)
    parent_t parent_le parent_m Out_normal) in HparentReads.
  destruct (ipls_actual_parent_reads version e guard_le m PLS._t'81 PLS._t'82
    cb ob oo pb po parent_t parent_le parent_m Out_normal ltac:(discriminate)
    Hlocal Hsymbol Hcurrent Hparent HparentReads) as (HparentMemory & _ & Hpointer).
  subst parent_m.
  destruct (ipls_reached_call_is_actual_approach version e parent_le m pb po
    helper_t approach_le approach_m Out_normal HapproachLocal Hpointer HhelperCall)
    as (result & HactualHelper & HhelperTemps & _).
  destruct (ifch_completed_approach_exact_effect version m pb
    (Ptrofs.add po (Ptrofs.repr 252)) old ipls_one ipls_delta
    helper_t approach_m result Hfactor HactualHelper)
    as (increment_m & Hincrement & HfinalStore & HfinalFactor).
  pose proof (ipls_one_factor_store_frames_receivers m increment_m cb ob oo pb po
    (Vsingle (ifch_candidate old ipls_one ipls_delta)) HglobalSep HobjectRoom HparentRoom
    HreceiverSep Hincrement) as HfirstFrame.
  assert (HhelperFrame : ipls_receiver_frame cb ob oo m approach_m).
  { destruct HfinalStore as [Hsame|Hclamp].
    - subst approach_m. exact HfirstFrame.
    - eapply ipls_receiver_frames_trans; [exact HfirstFrame|].
      eapply ipls_one_factor_store_frames_receivers; eauto. }
  destruct HhelperFrame as [HglobalFrame HparentFrame].
  assert (HcurrentAfter : Mem.load Mint32 approach_m cb 0 = Some (Vptr ob oo)) by congruence.
  assert (HparentAfter : Mem.load Mint32 approach_m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 104))) = Some (Vptr pb po)) by congruence.
  pose proof (ipls_taken_float_guard_has_real_bound old Fold Hless) as Hold.
  destruct (ifch_pokey_approach_result_bounded old Fold Hold) as [Ffactor HfactorBound].
  change (rank9cf_finite (ifch_approach_result old ipls_one ipls_delta)) in Ffactor.
  change (rank9cf_real (ifch_approach_result old ipls_one ipls_delta) <= 1)%R in HfactorBound.
  rewrite HreloadShape in Hreload.
  destruct (ibk_split_prefix _ _
    [Sset PLS._t'78 ipls_current;Sset PLS._t'79 (ipls_parent PLS._t'78);
     Sset PLS._t'80 (ipls_factor version PLS._t'79)]
    ipls_scale_call _ _ _ _ _ _ ltac:(reflexivity) Hreload)
    as (call_le & call_m & reads_t & call_t & HreloadTrace & Hreads & Hcall).
  change (ocn_exec (Clight.globalenv (selected_clight_target version)) e approach_le approach_m (ipls_reads version PLS._t'78 PLS._t'79 PLS._t'80)
    reads_t call_le call_m Out_normal) in Hreads.
  destruct (ipls_actual_reads version e approach_le approach_m PLS._t'78 PLS._t'79 PLS._t'80
    cb ob oo pb po (ifch_approach_result old ipls_one ipls_delta) reads_t call_le call_m Out_normal
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hlocal Hsymbol
    HcurrentAfter HparentAfter HfinalFactor Hreads)
    as (HcallMemory & _ & _ & HcallFactor).
  subst call_m.
  exists (ifch_approach_result old ipls_one ipls_delta), call_le, approach_m, call_t.
  repeat split; try reflexivity; try assumption.
  - eapply ipls_finite_factor_gives_scale_upper_bound; [exact Ffactor|exact Fproduct|].
    assert (Hone : (rank9cf_real ipls_one = 1)%R) by (vm_compute; nra).
    rewrite Hone. exact HfactorBound.
  - eapply ipls_reached_scale_argument_is_loaded_product; [exact HcallFactor|exact Hcall].
Qed.





