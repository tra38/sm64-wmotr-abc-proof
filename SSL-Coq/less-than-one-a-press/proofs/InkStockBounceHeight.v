(** Native scale-to-height bridges for stock bounce actors.

    These results use the selected generated US/JP helpers. They derive the
    height written by the helper from a real completed scale operation and
    template read. Native action/carry history and preservation between
    separate callbacks are not assumed to be a whole-game invariant. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_helpers jp_object_helpers.
From LessThanOneAPress.Proofs Require Import GameTypes InkFlyGuyGrowthPrefix
  InkCopyCaller InkFloorResetExecution InkRawCopyExpressions InkBackwardExecution
  InkControllerSource InkControllerEdge ObjectContactNecessity
  ContactConsumerExecution EyerokRank15LiveMovement SelectedClightTarget
  InkQuicksandExpressions SecretContactExecution Area1PostCopyChildSource
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module SBH := us_object_helpers.

Definition isbh_fresh id kept := negb (existsb (Pos.eqb id) kept).
Definition isbh_refs kept (refs : ident -> option val) (le : temp_env) :=
  forall id, In id kept -> le ! id = refs id.
Fixpoint isbh_shape kept (write_ok : expr -> bool)
    (call_ok : expr -> list expr -> bool) s := match s with
| Sskip | Sreturn _ => true
| Sset id _ => isbh_fresh id kept
| Sassign lhs _ => write_ok lhs
| Scall opt fn args =>
    (match opt with None => true | Some id => isbh_fresh id kept end) && call_ok fn args
| Ssequence a b | Sifthenelse _ a b =>
    isbh_shape kept write_ok call_ok a && isbh_shape kept write_ok call_ok b
| _ => false end.
Lemma isbh_set_refs : forall kept refs le id v,
  isbh_refs kept refs le -> isbh_fresh id kept = true ->
  isbh_refs kept refs (PTree.set id v le).
Proof.
  intros kept refs le id v Hrefs Hfresh other Hin.
  unfold isbh_fresh in Hfresh. apply negb_true_iff in Hfresh.
  assert (id <> other) as Hneq.
  { intro Heq. subst other.
    assert (existsb (Pos.eqb id) kept = true) as Hyes.
    { apply existsb_exists. exists id. split; [exact Hin|apply Pos.eqb_refl]. }
    congruence. }
  rewrite PTree.gso by congruence. apply Hrefs; exact Hin.
Qed.

Definition isbh_scale_body version := match version with
| VersionUS => us_object_helpers.f_cur_obj_scale
| VersionJP => jp_object_helpers.f_cur_obj_scale end.
Definition isbh_scale_index temporary n := Ederef
  (Ebinop Oadd (ifgp_scales temporary) (Econst_int (Int.repr n) tint)
    (tptr tfloat)) tfloat.
Definition isbh_scale_stage temporary n := Ssequence
  (Sset temporary (Evar SBH._gCurrentObject (tptr (Tstruct SBH._Object noattr))))
  (Sassign (isbh_scale_index temporary n) (Etempvar SBH._scale tfloat)).
Definition isbh_room oo := Ptrofs.unsigned oo + 600 <= Ptrofs.max_unsigned.
Lemma isbh_address : forall oo delta,
  isbh_room oo -> 0 <= delta <= 600 ->
  Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr delta)) = Ptrofs.unsigned oo + delta.
Proof.
  intros oo delta Hroom Hdelta. unfold isbh_room in Hroom.
  pose proof (Ptrofs.unsigned_range oo).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr delta)
    by (change (0 <= delta <= 4294967295); lia).
  apply Ptrofs.unsigned_repr. lia.
Qed.


Definition isbh_tangible_body version := match version with
| VersionUS => us_object_helpers.f_cur_obj_become_tangible
| VersionJP => jp_object_helpers.f_cur_obj_become_tangible end.
Lemma isbh_tangible_us_source :
  nth_error SBH.global_definitions
    (ueqr_definition_index SBH._cur_obj_become_tangible SBH.global_definitions) =
  Some (SBH._cur_obj_become_tangible, Gfun (Internal (isbh_tangible_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma isbh_tangible_us_member :
  In (SBH._cur_obj_become_tangible, Gfun (Internal (isbh_tangible_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 19 us_units).
  - exact (us_nlist_at_nIn _ 19 us_units).
  - eapply nth_error_In. exact isbh_tangible_us_source.
Qed.
Lemma isbh_tangible_us_selection :
  us_normalized_global_definition_map ! SBH._cur_obj_become_tangible =
    Some (Gfun (Internal (isbh_tangible_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact isbh_tangible_us_member.
Qed.
Lemma isbh_tangible_us_no_repair :
  us_selected_definition_needs_viewport_repair
    (SBH._cur_obj_become_tangible, Gfun (Internal (isbh_tangible_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma isbh_tangible_us_selected_member :
  In (SBH._cur_obj_become_tangible, Gfun (Internal (isbh_tangible_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite isbh_tangible_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact isbh_tangible_us_selection.
Qed.
Lemma isbh_tangible_jp_source :
  (prog_defmap (nlist_at 19 jp_cleaned_units)) ! SBH._cur_obj_become_tangible =
    Some (Gfun (Internal (isbh_tangible_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem isbh_actual_tangible_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._cur_obj_become_tangible = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (isbh_tangible_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact isbh_tangible_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 19 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 19 jp_cleaned_units).
    + exact isbh_tangible_jp_source.
Qed.

Definition isbh_raw_array version temporary (unsigned : bool) := Efield
  (irc_raw_union version temporary)
  (if unsigned then SBH._asU32 else SBH._asS32)
  (tarray (if unsigned then tuint else tint) 80).
Definition isbh_raw_cell version temporary (unsigned : bool) n :=
  Ederef (Ebinop Oadd (isbh_raw_array version temporary unsigned)
    (Econst_int (Int.repr n) tint) (tptr (if unsigned then tuint else tint)))
    (if unsigned then tuint else tint).

Definition isbh_raw_member_check environment tag (unsigned : bool) :=
  match environment ! tag with
  | Some raw_type =>
      match union_field_offset environment
        (if unsigned then SBH._asU32 else SBH._asS32) (co_members raw_type) with
      | OK (offset, Full) => Z.eqb offset 0
      | _ => false
      end
  | None => false
  end.
Lemma isbh_raw_member_checked : forall version unsigned,
  isbh_raw_member_check (rank15_selected_header_environment version)
    (rank15_raw_union_tag version) unsigned = true.
Proof. intros [] []; vm_compute; reflexivity. Qed.
Lemma isbh_raw_member_sound : forall environment tag unsigned raw_type,
  environment ! tag = Some raw_type ->
  isbh_raw_member_check environment tag unsigned = true ->
  union_field_offset environment
    (if unsigned then SBH._asU32 else SBH._asS32) (co_members raw_type) =
    OK (0, Full).
Proof.
  intros environment tag unsigned raw_type Hraw Hcheck.
  unfold isbh_raw_member_check in Hcheck. rewrite Hraw in Hcheck.
  destruct (union_field_offset environment
    (if unsigned then SBH._asU32 else SBH._asS32) (co_members raw_type))
    as [[offset bits]|] eqn:Hoffset; try discriminate.
  destruct bits; try discriminate.
  apply Z.eqb_eq in Hcheck. subst offset. reflexivity.
Qed.

Lemma isbh_raw_array_value : forall version e le m temporary unsigned ob oo answer,
  le ! temporary = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (isbh_raw_array version temporary unsigned) answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136)).
Proof.
  intros version e le m temporary unsigned ob oo answer Htemp Hread.
  destruct (rank15_selected_raw_layout version)
    as (object_type & raw_type & Hobject & Hraw & HobjectOffset & HrawOffset).
  assert (ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    SBH._Object SBH._rawData 136 = true) as Hfield.
  { unfold ibcc_field_ok. change ((genv_cenv (Clight.globalenv (selected_clight_target version))) ! SBH._Object =
      Some object_type) in Hobject.
    change (field_offset (Clight.globalenv (selected_clight_target version))
      SBH._rawData (co_members object_type) = OK (136, Full)) in HobjectOffset.
    rewrite Hobject, HobjectOffset. reflexivity. }
  assert (forall value, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m (irc_raw_union version temporary) value ->
    value = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136))) as Hbase.
  { intros. eapply ibcc_aggregate_field with (base := irc_raw_object temporary)
      (tag := SBH._Object) (field := SBH._rawData)
      (ty := Tunion (rank15_raw_union_tag version) noattr) (delta := 136);
      [reflexivity| |exact Hfield|right; reflexivity|eassumption].
    intros. eapply ibcc_deref_struct; eauto. }
  assert (Hmember : union_field_offset (Clight.globalenv (selected_clight_target version))
    (if unsigned then SBH._asU32 else SBH._asS32) (co_members raw_type) = OK (0, Full)).
  { eapply isbh_raw_member_sound; [exact Hraw|].
    pose proof (isbh_raw_member_checked version unsigned) as Hcheck.
    rewrite rank15_selected_header_environment_exact in Hcheck.
    exact Hcheck. }
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl; subst; try discriminate end.
  match goal with Hr : eval_expr _ _ _ _ (irc_raw_union _ _) _ |- _ => apply Hbase in Hr; inversion Hr; subst end.
  match goal with Htype : typeof (irc_raw_union _ _) = _ |- _ =>
    cbn [typeof irc_raw_union] in Htype; inversion Htype; subst end.
  match goal with Hco : (genv_cenv _) ! _ = Some ?co |- _ =>
    assert (co = raw_type) by congruence; subst co end.
  match goal with Hoff : union_field_offset _ _ _ = OK (?offset, ?bf) |- _ =>
    assert (offset = 0 /\ bf = Full) as Hfields by (split; congruence);
    destruct Hfields as [Hdelta Hbits]; subst offset bf end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  all: try solve [match goal with Hmode : access_mode _ = _ |- _ =>
    destruct unsigned; cbn [typeof isbh_raw_array access_mode] in Hmode; discriminate end].
  all: rewrite Ptrofs.add_zero; reflexivity.
Qed.

Lemma isbh_raw_cell_location : forall version e le m temporary unsigned n ob oo b ofs bf,
  le ! temporary = Some (Vptr ob oo) -> In n [1;5;42;62;63;68] ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (isbh_raw_cell version temporary unsigned n) b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr (136+4*n)) /\ bf = Full.
Proof.
  intros version e le m temporary unsigned n ob oo b ofs bf Htemp Hn Hl.
  unfold isbh_raw_cell in Hl.
  destruct (iq_array_location _ _ _ _ (isbh_raw_array version temporary unsigned)
    (if unsigned then tuint else tint) 80 n ob
    (Ptrofs.add oo (Ptrofs.repr 136)) b ofs bf eq_refl
    ltac:(intros; eapply isbh_raw_array_value; eauto) Hl) as (-> & -> & ->).
  rewrite Ptrofs.add_assoc.
  destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    destruct unsigned; repeat split; reflexivity.
Qed.

Lemma isbh_raw_store : forall version e le m temporary unsigned n ob oo rhs t le' m' out,
  le ! temporary = Some (Vptr ob oo) -> In n [1;5;42;62;63;68] ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign (isbh_raw_cell version temporary unsigned n) rhs) t le' m' out ->
  exists written, Mem.store Mint32 m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (136+4*n)))) written = Some m' /\
    le' = le /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m temporary unsigned n ob oo rhs t le' m' out Ho Hn Hrun.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (isbh_raw_cell_location _ _ _ _ _ _ _ _ _ _ _ _ Ho Hn Hl)
      as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  all: match goal with Hmode : access_mode _ = _ |- _ =>
    destruct unsigned; cbn [typeof isbh_raw_cell access_mode] in Hmode;
    inversion Hmode; subst end.
  all: eexists; repeat split; try reflexivity; eassumption.
Qed.

Definition isbh_outside_before (ob : block) oo chunk b offset :=
  b <> ob \/ offset + size_chunk chunk <= Ptrofs.unsigned oo + 136 \/
    Ptrofs.unsigned oo + 508 <= offset.
Definition isbh_before_frame ob oo before after := forall chunk b offset,
  isbh_outside_before ob oo chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk before b offset.
Lemma isbh_before_frame_refl : forall ob oo m, isbh_before_frame ob oo m m.
Proof. intros ob oo m chunk b offset H; reflexivity. Qed.
Lemma isbh_before_frame_trans : forall ob oo a b c,
  isbh_before_frame ob oo a b -> isbh_before_frame ob oo b c -> isbh_before_frame ob oo a c.
Proof. intros ob oo a b c Hab Hbc chunk loc offset Hsep. rewrite Hbc, Hab by exact Hsep. reflexivity. Qed.
Lemma isbh_raw_store_before_frame : forall version e le m temporary unsigned n ob oo rhs t le' m' out,
  le ! temporary = Some (Vptr ob oo) -> In n [1;5;42;62;63;68] -> isbh_room oo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign (isbh_raw_cell version temporary unsigned n) rhs) t le' m' out ->
  isbh_before_frame ob oo m m'.
Proof.
  intros version e le m temporary unsigned n ob oo rhs t le' m' out Ho Hn Hroom Hrun.
  destruct (isbh_raw_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ho Hn Hrun) as (written & Hstore & _).
  assert (1 <= n <= 68) by
    (destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; lia).
  rewrite isbh_address in Hstore by (auto; lia).
  intros chunk b offset Hsep. eapply Mem.load_store_other; [exact Hstore|].
  unfold isbh_outside_before in Hsep.
  cbn [size_chunk]. destruct Hsep as [Hloc|[Hlow|Hhigh]];
    [left; exact Hloc|right; left; lia|right; right; lia].
Qed.

(** First initialization makes the actor tangible. This is the actual tiny
    no-call callee, including its real global read and intangible-timer write. *)
Theorem isbh_completed_tangible_frames_size : forall version m cb ob oo t m' result,
  isbh_room oo ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (isbh_tangible_body version)) [] t m' result ->
  isbh_before_frame ob oo m m'.
Proof.
  intros version m cb ob oo t m' result Hroom Hsymbol Hcurrent Hcall.
  assert (Hvars : fn_vars (isbh_tangible_body version) = []) by (destruct version; reflexivity).
  assert (Hbody : fn_body (isbh_tangible_body version) = Ssequence
    (Sset SBH._t'1 (Evar SBH._gCurrentObject (tptr (Tstruct SBH._Object noattr))))
    (Sassign (isbh_raw_cell version SBH._t'1 false 5) (Econst_int Int.zero tint)))
    by (destruct version; reflexivity).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ => inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hrun end.
  cce_unroll_loop_free_exec.
  match goal with Hr : eval_expr _ _ _ _ (Evar SBH._gCurrentObject _) ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply irc_global_pointer_read; eauto; apply PTree.gempty); subst v end.
  eapply isbh_raw_store_before_frame with
    (version := version) (temporary := SBH._t'1) (unsigned := false) (n := 5);
    [apply PTree.gss|cbn; auto|exact Hroom|eassumption].
Qed.

Definition isbh_tangible_call := Scall None
  (Evar SBH._cur_obj_become_tangible (Tfunction [] tvoid cc_default)) [].
Lemma isbh_tangible_call_frames_size : forall version e le m cb ob oo t le' m' out,
  e ! SBH._cur_obj_become_tangible = None -> isbh_room oo ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    isbh_tangible_call t le' m' out -> isbh_before_frame ob oo m m'.
Proof.
  intros version e le m cb ob oo t le' m' out Hlocal Hroom Hsymbol Hcurrent Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (isbh_actual_tangible_resolves version) as (fb & HfnSymbol & Hfunction).
  match goal with Hr : eval_expr _ _ _ _ (Evar SBH._cur_obj_become_tangible _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hargs : eval_exprlist _ _ _ _ [] _ ?values |- _ => inversion Hargs; subst values end.
  eapply isbh_completed_tangible_frames_size; eauto.
Qed.

Fixpoint isbh_writes s := match s with
| Sassign lhs _ => [lhs]
| Ssequence a b | Sifthenelse _ a b => isbh_writes a ++ isbh_writes b
| _ => [] end.
Fixpoint isbh_calls s := match s with
| Scall opt fn args => [(opt,fn,args)]
| Ssequence a b | Sifthenelse _ a b => isbh_calls a ++ isbh_calls b
| _ => [] end.
Fixpoint isbh_frame_shape kept s := match s with
| Sskip | Sassign _ _ => true
| Sset id _ => isbh_fresh id kept
| Scall opt _ _ => match opt with None => true | Some id => isbh_fresh id kept end
| Ssequence a b | Sifthenelse _ a b => isbh_frame_shape kept a && isbh_frame_shape kept b
| _ => false end.

Definition isbh_write_receipt version e ob oo kept refs lhs :=
  forall le m rhs t le' m' out, isbh_refs kept refs le ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (Sassign lhs rhs) t le' m' out -> isbh_before_frame ob oo m m'.
Definition isbh_call_receipt version e cb ob oo kept refs (item : option ident * expr * list expr) :=
  let '(opt,fn,args) := item in
  forall le m t le' m' out, isbh_refs kept refs le ->
    Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (Scall opt fn args) t le' m' out -> isbh_before_frame ob oo m m'.

(** The finite write/call lists are discharged for the generated prefix
    below; they are not an assumed inventory of all gameplay. *)
Lemma isbh_list_frame : forall version e cb ob oo kept refs le m s t le' m' out,
  cb <> ob ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m s t le' m' out ->
  isbh_frame_shape kept s = true ->
  Forall (isbh_write_receipt version e ob oo kept refs) (isbh_writes s) ->
  Forall (isbh_call_receipt version e cb ob oo kept refs) (isbh_calls s) ->
  isbh_refs kept refs le -> Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  isbh_before_frame ob oo m m' /\ isbh_refs kept refs le'.
Proof.
  intros version e cb ob oo kept refs le m s t le' m' out Hsep Hrun.
  induction Hrun; cbn [isbh_frame_shape isbh_writes isbh_calls];
    intros Hshape Hwrites Hcalls Hrefs Hcurrent; try discriminate.
  - split; [apply isbh_before_frame_refl|exact Hrefs].
  - inversion Hwrites as [|lhs items Hreceipt Hrest]; subst.
    split; [eapply Hreceipt; eauto; econstructor; eauto|exact Hrefs].
  - split; [apply isbh_before_frame_refl|]. eapply isbh_set_refs; eauto.
  - inversion Hcalls as [|item items Hreceipt Hrest]; subst.
    split; [eapply Hreceipt; eauto; econstructor; eauto|].
    destruct optid; cbn; [eapply isbh_set_refs; eauto|exact Hrefs].
  - apply andb_true_iff in Hshape as [Ha Hb].
    apply Forall_app in Hwrites as [Hwa Hwb]. apply Forall_app in Hcalls as [Hca Hcb].
    destruct (IHHrun1 Ha Hwa Hca Hrefs Hcurrent) as [Hab Hmiddle].
    assert (Mem.load Mint32 m1 cb 0 = Some (Vptr ob oo)) as HmidCurrent.
    { rewrite Hab; [exact Hcurrent|left; exact Hsep]. }
    destruct (IHHrun2 Hb Hwb Hcb Hmiddle HmidCurrent) as [Hbc Hfinal].
    split; [eapply isbh_before_frame_trans; eauto|exact Hfinal].
  - apply andb_true_iff in Hshape as [Ha Hb].
    apply Forall_app in Hwrites as [Hwa Hwb]. apply Forall_app in Hcalls as [Hca Hcb].
    eauto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    apply Forall_app in Hwrites as [Hwa Hwb]. apply Forall_app in Hcalls as [Hca Hcb].
    destruct b; eauto.
  Unshelve. all: exact None.
Qed.

Lemma isbh_scale_source : forall version,
  fn_vars (isbh_scale_body version) = [] /\
  fn_params (isbh_scale_body version) = [(SBH._scale, tfloat)] /\
  fn_body (isbh_scale_body version) =
    Ssequence (isbh_scale_stage SBH._t'3 0)
      (Ssequence (isbh_scale_stage SBH._t'2 1)
        (isbh_scale_stage SBH._t'1 2)).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma isbh_scale_index_location : forall version e le m temporary n ob oo b ofs bf,
  le ! temporary = Some (Vptr ob oo) -> In n [0; 1; 2] ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (isbh_scale_index temporary n) b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr (44 + 4*n)) /\ bf = Full.
Proof.
  intros version e le m temporary n ob oo b ofs bf Htemp Hn Hl.
  unfold isbh_scale_index in Hl.
  destruct (ifr_array_index_location _ _ _ _ (ifgp_scales temporary) n ob
    (Ptrofs.add oo (Ptrofs.repr 44)) b ofs bf eq_refl
    ltac:(intros; eapply ifgp_scales_value; eauto) Hl) as (-> & -> & ->).
  rewrite Ptrofs.add_assoc.
  destruct Hn as [<-|[<-|[<-|[]]]]; repeat split; reflexivity.
Qed.

Lemma isbh_scale_index_read : forall version e le m temporary n ob oo value answer,
  le ! temporary = Some (Vptr ob oo) -> In n [0; 1; 2] ->
  Mem.load Mfloat32 m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (44 + 4*n)))) = Some value ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (isbh_scale_index temporary n) answer -> answer = value.
Proof.
  intros version e le m temporary n ob oo value answer Ho Hn Hload Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (isbh_scale_index_location _ _ _ _ _ _ _ _ _ _ _ Ho Hn Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn [typeof isbh_scale_index access_mode] in Hmode; inversion Hmode; subst end.
  match goal with Hread : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m ob
      (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (44+4*n)))) = Some answer) in Hread;
    congruence end.
Qed.

Lemma isbh_scale_stage_actual_store : forall version e le m temporary n cb ob oo
    scale t le' m' out,
  temporary <> SBH._scale -> In n [0;1;2] ->
  e ! SBH._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  le ! SBH._scale = Some (Vsingle scale) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (isbh_scale_stage temporary n) t le' m' out ->
  Mem.store Mfloat32 m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (44+4*n))))
    (Vsingle scale) = Some m' /\
  le' = PTree.set temporary (Vptr ob oo) le /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m temporary n cb ob oo scale t le' m' out
    Hneq Hn Hlocal Hsymbol Hcurrent Hscale Hrun.
  unfold isbh_scale_stage, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  match goal with Hr : eval_expr _ _ _ _ (Evar SBH._gCurrentObject _) ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply irc_global_pointer_read; eauto); subst v end.
  match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (isbh_scale_index_location _ _ _ _ _ _ _ _ _ _ _ (PTree.gss _ _ _) Hn Hl)
      as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar SBH._scale _) ?v |- _ =>
    assert (v = Vsingle scale) by
      (eapply ocn_temp_value; [exact Hr|rewrite PTree.gso by congruence; exact Hscale]);
    subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  repeat split; try reflexivity; assumption.
Qed.

(** All three generated stores are included, so scale Y is still established
    after the helper returns. The global pointer cannot alias the actor. *)
Theorem isbh_completed_scale_sets_y : forall version m cb ob oo scale t m' result,
  cb <> ob -> isbh_room oo ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (isbh_scale_body version)) [Vsingle scale] t m' result ->
  Mem.load Mfloat32 m' ob (Ptrofs.unsigned oo + 48) = Some (Vsingle scale) /\
  Mem.load Mint32 m' cb 0 = Some (Vptr ob oo) /\ t = E0.
Proof.
  intros version m cb ob oo scale t m' result Hsep Hroom Hsymbol Hcurrent Hcall.
  destruct (isbh_scale_source version) as (Hvars & Hparams & Hbody).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! SBH._scale = Some (Vsingle scale)) as Hscale
      by (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; subst;
          apply PTree.gss) end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hrun;
    destruct (ibk_split_sequence _ _ _ _ (isbh_scale_stage SBH._t'3 0)
      _ _ _ _ _ eq_refl Hrun) as (lx & mx & tx & tr & Htrace & Hx & Hrest) end.
  destruct (isbh_scale_stage_actual_store version empty_env _ _ SBH._t'3 0 cb ob oo scale _ _ _ _
    ltac:(discriminate) ltac:(cbn; auto) (PTree.gempty _ _) Hsymbol Hcurrent Hscale Hx)
    as (Hxs & -> & -> & _).
  assert (Mem.load Mint32 mx cb 0 = Some (Vptr ob oo)) as Hcx.
  { erewrite Mem.load_store_other; [exact Hcurrent|exact Hxs|left; congruence]. }
  destruct (ibk_split_sequence _ _ _ _ (isbh_scale_stage SBH._t'2 1)
    _ _ _ _ _ eq_refl Hrest) as (ly & my & ty & tz & Htrace2 & Hy & Hz).
  match type of Hscale with ?entry ! SBH._scale = _ =>
    assert ((PTree.set SBH._t'3 (Vptr ob oo) entry) ! SBH._scale =
      Some (Vsingle scale)) as Hsx
      by (rewrite PTree.gso by discriminate; exact Hscale) end.
  destruct (isbh_scale_stage_actual_store version empty_env _ _ SBH._t'2 1 cb ob oo scale _ _ _ _
    ltac:(discriminate) ltac:(cbn; auto) (PTree.gempty _ _) Hsymbol Hcx Hsx Hy)
    as (Hys & -> & -> & _).
  assert (Mem.load Mint32 my cb 0 = Some (Vptr ob oo)) as Hcy.
  { erewrite Mem.load_store_other; [exact Hcx|exact Hys|left; congruence]. }
  match type of Hsx with ?entry_x ! SBH._scale = _ =>
    assert ((PTree.set SBH._t'2 (Vptr ob oo) entry_x) ! SBH._scale =
      Some (Vsingle scale)) as Hsy
      by (rewrite PTree.gso by discriminate; exact Hsx) end.
  destruct (isbh_scale_stage_actual_store version empty_env _ _ SBH._t'1 2 cb ob oo scale _ _ _ _
    ltac:(discriminate) ltac:(cbn; auto) (PTree.gempty _ _) Hsymbol Hcy Hsy Hz)
    as (Hzs & _ & -> & _).
  rewrite isbh_address in Hys, Hzs by (auto; lia).
  split.
  - erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ Hys)|exact Hzs|].
    right; left; cbn [size_chunk]; lia.
  - split.
    + erewrite Mem.load_store_other; [exact Hcy|exact Hzs|left; congruence].
    + subst. reflexivity.
Qed.

Lemma isbh_template_height_field : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    SBH._ObjectHitbox SBH._height 10 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    SBH._ObjectHitbox SBH._height 10 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Theorem isbh_height_store_general : forall version e le m ob oo scale_y height
    t le' m' out,
  le ! SBH._obj = Some (Vptr ob oo) ->
  le ! SBH._t'7 = Some (Vsingle scale_y) ->
  le ! SBH._t'8 = Some (Vint height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ifgp_height_store t le' m' out ->
  Mem.store Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508)))
    (Vsingle (Float32.mul scale_y (Float32.of_int height))) = Some m' /\
  le' = le /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m ob oo scale_y height t le' m' out Ho Hs Hh Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt, ifgp_height_store in Hrun.
  inversion Hrun; subst; clear Hrun.
  match goal with Hl : eval_lvalue _ _ _ _ (ics_field _ _ _ _) _ _ _ |- _ =>
    destruct (ice_field_location _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ho
      (ifgp_selected_height_field version) Hl) as (-> & -> & ->) end.
  match goal with H : eval_expr _ _ _ _ ifgp_height_expression _ |- _ =>
    unfold ifgp_height_expression in H; inversion H; subst; clear H end.
  - match goal with H : eval_expr _ _ _ _ (Etempvar SBH._t'7 _) ?v |- _ =>
      assert (v = Vsingle scale_y) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : eval_expr _ _ _ _ (Etempvar SBH._t'8 _) ?v |- _ =>
      assert (v = Vint height) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn in H; inversion H; subst; clear H end.
    match goal with H : sem_cast _ _ _ _ = Some _ |- _ => cbn in H; inversion H; subst end.
    match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
    match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
    repeat split; try reflexivity; assumption.
  - match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

(** The scale and template are read by the actual setter, not supplied as
    already-computed hitbox height or guessed expression temporaries. *)
Theorem isbh_height_stage_derives_live_height : forall version e le m ob oo hb ho
    scale_y height t le' m' out,
  le ! SBH._obj = Some (Vptr ob oo) ->
  le ! SBH._hitbox = Some (Vptr hb ho) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 48))) = Some (Vsingle scale_y) ->
  Mem.load Mint16signed m hb (Ptrofs.unsigned (Ptrofs.add ho (Ptrofs.repr 10))) = Some (Vint height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifgp_height_stage version) t le' m' out ->
  Mem.store Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508)))
    (Vsingle (Float32.mul scale_y (Float32.of_int height))) = Some m' /\
  Mem.load Mfloat32 m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle (Float32.mul scale_y (Float32.of_int height))) /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m ob oo hb ho scale_y height t le' m' out Ho Hh Hscale Hheight Hrun.
  assert (Hstage : ifgp_height_stage version = Ssequence
    (Sset SBH._t'7 (isbh_scale_index SBH._obj 1))
    (Ssequence (Sset SBH._t'8 (ics_field SBH._hitbox SBH._ObjectHitbox SBH._height tshort))
      ifgp_height_store)) by (destruct version; reflexivity).
  rewrite Hstage in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  lazymatch goal with Hr : eval_expr _ ?read_e ?read_le ?read_m
      (isbh_scale_index SBH._obj 1) ?v |- _ =>
    assert (v = Vsingle scale_y) by
      (eapply (isbh_scale_index_read version read_e read_le read_m SBH._obj 1 ob oo
        (Vsingle scale_y) v); [exact Ho|cbn; auto|exact Hscale|exact Hr]);
    subst v end.
  lazymatch goal with Hr : eval_expr _ ?read_e ?read_le ?read_m
      (ics_field SBH._hitbox SBH._ObjectHitbox SBH._height tshort) ?v |- _ =>
    assert (v = Vint height) by
      (eapply (ice_field_read (Clight.globalenv (selected_clight_target version))
         read_e read_le read_m SBH._hitbox SBH._ObjectHitbox SBH._height
         tshort hb ho 10 Mint16signed (Vint height) v);
       [rewrite PTree.gso by discriminate; exact Hh|exact (isbh_template_height_field version)|
        reflexivity|exact Hheight|exact Hr]); subst v end.
  lazymatch goal with Hstore : ClightBigstep.exec_stmt _ _ ?store_e ?store_le ?store_m
      ifgp_height_store _ _ _ _ |- _ =>
    destruct (isbh_height_store_general version store_e store_le store_m ob oo scale_y height _ _ _ _
      ltac:(rewrite !PTree.gso by discriminate; exact Ho)
      ltac:(rewrite PTree.gso by discriminate; apply PTree.gss)
      (PTree.gss _ _ _) Hstore) as (Hs & _ & -> & ->) end.
  split; [exact Hs|]. split; [exact (Mem.load_store_same _ _ _ _ _ _ Hs)|].
  split; reflexivity.
Qed.

(** Exact stock products. This certificate does not classify all intervening
    scale histories, especially shrinking, carry-script changes or cloning. *)
Theorem isbh_stock_height_products_checked :
  Float32.to_bits (Float32.mul (Float32.of_bits (Int.repr 1069547520))
    (Float32.of_int (Int.repr 50))) = Int.repr 1117126656 /\
  Float32.to_bits (Float32.mul (Float32.of_int (Int.repr 3))
    (Float32.of_int (Int.repr 20))) = Int.repr 1114636288 /\
  Float32.to_bits (Float32.mul (Float32.of_int (Int.repr 1))
    (Float32.of_int (Int.repr 250))) = Int.repr 1132068864.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** A small checker is used only for the reached helper prefix/tail. Its
    semantic frame comes from the actual destinations; it grants no callee
    frame for unexamined native callbacks. *)
Lemma isbh_checked_load_frame : forall ge e kept refs write_ok call_ok chunk b offset,
  (forall le m lhs rhs t le' m' out,
    isbh_refs kept refs le -> write_ok lhs = true ->
    ocn_exec ge e le m (Sassign lhs rhs) t le' m' out ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset) ->
  (forall le m opt fn args t le' m' out,
    isbh_refs kept refs le -> call_ok fn args = true ->
    ocn_exec ge e le m (Scall opt fn args) t le' m' out ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset) ->
  forall le m s t le' m' out,
    ocn_exec ge e le m s t le' m' out ->
    isbh_shape kept write_ok call_ok s = true -> isbh_refs kept refs le ->
    Mem.load chunk m' b offset = Mem.load chunk m b offset /\ isbh_refs kept refs le'.
Proof.
  intros ge e kept refs write_ok call_ok chunk b offset Hwrite Hcall
    le m s t le' m' out Hrun.
  induction Hrun; cbn [isbh_shape]; intros Hshape Hrefs; try discriminate;
    try (split; [reflexivity|exact Hrefs]).
  - split; [eapply Hwrite; eauto; econstructor; eauto|exact Hrefs].
  - split; [reflexivity|]. eapply isbh_set_refs; eauto.
  - apply andb_true_iff in Hshape as [Hfresh Hallowed].
    split; [eapply Hcall; eauto; econstructor; eauto|].
    destruct optid; cbn; [eapply isbh_set_refs; eauto|exact Hrefs].
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Hwrite Hcall Ha Hrefs) as [Hfirst Hmiddle].
    destruct (IHHrun2 Hwrite Hcall Hb Hmiddle) as [Hsecond Hfinal].
    split; [congruence|exact Hfinal].
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb].
    match goal with Hif : ClightBigstep.exec_stmt _ _ _ _ _
      (if ?branch then _ else _) _ _ _ _ |- _ => destruct branch; auto end.
  Unshelve. all: exact None.
Qed.

Definition isbh_field_delta field :=
  if Pos.eq_dec field SBH._hitboxRadius then Some 504 else
  if Pos.eq_dec field SBH._hitboxHeight then Some 508 else
  if Pos.eq_dec field SBH._hurtboxRadius then Some 512 else
  if Pos.eq_dec field SBH._hurtboxHeight then Some 516 else
  if Pos.eq_dec field SBH._hitboxDownOffset then Some 520 else None.
Lemma isbh_field_delta_sound : forall version field delta,
  isbh_field_delta field = Some delta ->
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    SBH._Object field delta = true /\ 504 <= delta <= 520.
Proof.
  intros version field delta H. unfold isbh_field_delta in H.
  repeat match type of H with context [if ?test then _ else _] =>
    destruct test; try discriminate; subst end.
  all: inversion H; subst; split; try lia.
  all: match goal with |- ibcc_field_ok _ ?tag ?member ?offset = true =>
    change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
      tag member offset = true) end;
    rewrite <- rank15_selected_header_environment_exact;
    destruct version; vm_compute; reflexivity.
Qed.

Lemma isbh_float_field_store : forall version e le m ob oo field delta rhs t le' m' out,
  le ! SBH._obj = Some (Vptr ob oo) -> isbh_field_delta field = Some delta ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign (ics_field SBH._obj SBH._Object field tfloat) rhs) t le' m' out ->
  exists written, Mem.store Mfloat32 m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr delta))) written = Some m' /\
    le' = le /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m ob oo field delta rhs t le' m' out Ho Hfield Hrun.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ice_field_location _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ho
      (proj1 (isbh_field_delta_sound version field delta Hfield)) Hl)
      as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  eexists. repeat split; try reflexivity; eassumption.
Qed.

Definition isbh_tail_write lhs := match lhs with
| Efield (Ederef (Etempvar id pty) sty) field fty =>
    if Pos.eq_dec id SBH._obj then
    if type_eq pty (tptr (Tstruct SBH._Object noattr)) then
    if type_eq sty (Tstruct SBH._Object noattr) then
    if type_eq fty tfloat then
      Pos.eqb field SBH._hurtboxRadius || Pos.eqb field SBH._hurtboxHeight ||
      Pos.eqb field SBH._hitboxDownOffset
    else false else false else false else false
| _ => false end.
Lemma isbh_tail_write_cases : forall lhs, isbh_tail_write lhs = true ->
  exists field delta,
    lhs = ics_field SBH._obj SBH._Object field tfloat /\
    isbh_field_delta field = Some delta /\ 512 <= delta <= 520.
Proof.
  intro lhs. unfold isbh_tail_write.
  destruct lhs; try discriminate. destruct lhs; try discriminate.
  destruct lhs; try discriminate.
  repeat match goal with |- context [if ?test then _ else _] =>
    destruct test; try discriminate; subst end.
  intro H. repeat rewrite orb_true_iff in H.
  destruct H as [[H|H]|H]; apply Pos.eqb_eq in H; subst.
  all: do 2 eexists; repeat split; reflexivity || lia.
Qed.

Theorem isbh_hitbox_tail_preserves_height : forall version e le m ob oo
    t le' m' out,
  le ! SBH._obj = Some (Vptr ob oo) -> isbh_room oo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifgp_after_height version) t le' m' out ->
  Mem.load Mfloat32 m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))).
Proof.
  intros version e le m ob oo t le' m' out Ho Hroom Hrun.
  unshelve eapply (proj1 (isbh_checked_load_frame
    (Clight.globalenv (selected_clight_target version)) e [SBH._obj]
    (fun _ => Some (Vptr ob oo)) isbh_tail_write (fun _ _ => false)
    Mfloat32 ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508)))
    _ _ le m (ifgp_after_height version) t le' m' out Hrun _ _)).
  - intros temps before lhs rhs trace temps' after outcome Hrefs Hshape Hstore.
    destruct (isbh_tail_write_cases lhs Hshape) as (field & delta & -> & Hdelta & Hrange).
    destruct (isbh_float_field_store _ _ _ _ _ _ _ _ _ _ _ _ _
      ltac:(apply Hrefs; cbn; auto) Hdelta Hstore) as (written & Hs & _).
    eapply Mem.load_store_other; [exact Hs|].
    right; left. cbn [size_chunk]. rewrite !isbh_address by (auto; lia). lia.
  - intros. discriminate.
  - destruct version; reflexivity.
  - intros id [<-|[]]. exact Ho.
Qed.

(** The whole suffix from the actual Y read through the remaining three
    stores retains the freshly derived height. *)
Theorem isbh_height_and_tail_derives_retained_height : forall version e le m ob oo hb ho
    scale_y height t le' m' out,
  le ! SBH._obj = Some (Vptr ob oo) -> le ! SBH._hitbox = Some (Vptr hb ho) ->
  isbh_room oo ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 48))) = Some (Vsingle scale_y) ->
  Mem.load Mint16signed m hb (Ptrofs.unsigned (Ptrofs.add ho (Ptrofs.repr 10))) = Some (Vint height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Ssequence (ifgp_height_stage version) (ifgp_after_height version)) t le' m' out ->
  Mem.load Mfloat32 m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle (Float32.mul scale_y (Float32.of_int height))).
Proof.
  intros version e le m ob oo hb ho scale_y height t le' m' out
    Ho Hh Hroom Hscale Hheight Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (proj2 (proj2 (proj2 (proj2 (ifgp_height_cuts_are_generated version)))))) Hrun)
    as (middle_le & middle_m & height_t & tail_t & Htrace & Hstage & Htail).
  destruct (isbh_height_stage_derives_live_height _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Ho Hh Hscale Hheight Hstage) as (_ & Hlive & _).
  erewrite isbh_hitbox_tail_preserves_height; [exact Hlive| |exact Hroom|exact Htail].
  rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ SBH._obj Hstage
    ltac:(destruct version; reflexivity)). exact Ho.
Qed.

Definition isbh_before_height version := ocn_prepend (ifgp_before_height version) Sskip.
Lemma isbh_before_lists_are_generated : forall version,
  isbh_frame_shape [SBH._obj] (isbh_before_height version) = true /\
  isbh_writes (isbh_before_height version) =
    [isbh_raw_cell version SBH._obj true 1;
     isbh_raw_cell version SBH._obj true 42;
     isbh_raw_cell version SBH._obj false 62;
     isbh_raw_cell version SBH._obj false 63;
     isbh_raw_cell version SBH._obj false 68;
     ics_field SBH._obj SBH._Object SBH._hitboxRadius tfloat] /\
  isbh_calls (isbh_before_height version) =
    [(None, Evar SBH._cur_obj_become_tangible (Tfunction [] tvoid cc_default), [])].
Proof. intros []; repeat split; reflexivity. Qed.

Theorem isbh_complete_hitbox_prefix_frames_inputs : forall version e le m cb ob oo
    t le' m' out,
  cb <> ob -> isbh_room oo ->
  le ! SBH._obj = Some (Vptr ob oo) ->
  e ! SBH._cur_obj_become_tangible = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (isbh_before_height version) t le' m' out -> isbh_before_frame ob oo m m'.
Proof.
  intros version e le m cb ob oo t le' m' out Hsep Hroom Ho Hlocal Hsymbol Hcurrent Hrun.
  destruct (isbh_before_lists_are_generated version) as (Hshape & Hwrites & Hcalls).
  unshelve eapply (proj1 (isbh_list_frame version e cb ob oo [SBH._obj]
    (fun _ => Some (Vptr ob oo)) le m _ t le' m' out Hsep Hrun Hshape _ _ _ Hcurrent)).
  - rewrite Hwrites. repeat constructor.
    all: unfold isbh_write_receipt; intros temps before rhs trace temps' after outcome Hrefs Hstore.
    all: lazymatch type of Hstore with
      ocn_exec _ _ _ _ (Sassign (isbh_raw_cell _ _ ?raw_unsigned ?index) _) _ _ _ _ =>
      eapply isbh_raw_store_before_frame with (version := version)
        (temporary := SBH._obj) (unsigned := raw_unsigned) (n := index);
      [apply Hrefs; cbn; auto|cbn; auto 10|exact Hroom|exact Hstore]
    | _ => idtac end.
    destruct (isbh_float_field_store version e temps before ob oo SBH._hitboxRadius 504 rhs
      trace temps' after outcome ltac:(apply Hrefs; cbn; auto) eq_refl Hstore)
      as (written & Hs & _).
    rewrite isbh_address in Hs by (auto; lia).
    intros chunk loc offset Houtside. eapply Mem.load_store_other; [exact Hs|].
    unfold isbh_outside_before in Houtside. cbn [size_chunk].
    destruct Houtside as [Hloc|[Hlow|Hhigh]];
      [left; exact Hloc|right; left; lia|right; right; lia].
  - rewrite Hcalls. constructor; [|constructor].
    unfold isbh_call_receipt. intros temps before trace temps' after outcome Hrefs Hpointer Hcall.
    eapply isbh_tangible_call_frames_size; eauto.
  - intros id [<-|[]]. exact Ho.
Qed.

(** First-init and subsequent-call cases are both included. The five raw
    initialization stores, actual tangible call, radius store, height read
    and store, and three tail stores are covered through function return. *)
Theorem isbh_completed_hitbox_derives_height : forall version m cb ob oo hb ho scale_y height t m' result,
  cb <> ob -> hb <> ob -> isbh_room oo ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 48))) = Some (Vsingle scale_y) ->
  Mem.load Mint16signed m hb (Ptrofs.unsigned (Ptrofs.add ho (Ptrofs.repr 10))) = Some (Vint height) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifgp_hitbox_body version)) [Vptr ob oo; Vptr hb ho] t m' result ->
  Mem.load Mfloat32 m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle (Float32.mul scale_y (Float32.of_int height))).
Proof.
  intros version m cb ob oo hb ho scale_y height t m' result
    HcurrentSep HtemplateSep Hroom Hsymbol Hcurrent Hscale Hheight Hcall.
  destruct (ifgp_height_cuts_are_generated version)
    as (Hvars & Hbody & HbeforeNormal & Hstage & Hreads & Hnormal).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ => inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! SBH._obj = Some (Vptr ob oo) /\
      temps ! SBH._hitbox = Some (Vptr hb ho)) as [Ho Hh]
      by (destruct version; cbn in Hbind; inversion Hbind; split; reflexivity) end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hrun;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ HbeforeNormal Hrun)
      as (middle_le & middle_m & prefix_t & suffix_t & Htrace & Hprefix & Hsuffix) end.
  pose proof (isbh_complete_hitbox_prefix_frames_inputs _ _ _ _ _ _ _ _ _ _ _
    HcurrentSep Hroom Ho (PTree.gempty _ _) Hsymbol Hcurrent Hprefix) as Hframe.
  assert (middle_le ! SBH._obj = Some (Vptr ob oo)) as HmiddleObj.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ SBH._obj Hprefix
      ltac:(destruct version; reflexivity)). exact Ho. }
  assert (middle_le ! SBH._hitbox = Some (Vptr hb ho)) as HmiddleHitbox.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ SBH._hitbox Hprefix
      ltac:(destruct version; reflexivity)). exact Hh. }
  eapply isbh_height_and_tail_derives_retained_height;
    [exact HmiddleObj|exact HmiddleHitbox|exact Hroom| | |exact Hsuffix].
  - rewrite Hframe; [exact Hscale|]. right; left. rewrite isbh_address by (auto; lia).
    cbn [size_chunk]; lia.
  - rewrite Hframe; [exact Hheight|left; exact HtemplateSep].
Qed.

(** This bridge starts with an actual completed scale helper. Only the
    precise Y-cell continuity to the later setter remains at this boundary;
    it does not assume the desired live height. *)
Theorem isbh_actual_scale_to_completed_hitbox : forall version m scale_m hitbox_m m'
    cb ob oo hb ho scale_y height scale_t scale_result hitbox_t hitbox_result,
  cb <> ob -> hb <> ob -> isbh_room oo ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Internal (isbh_scale_body version)) [Vsingle scale_y] scale_t scale_m scale_result ->
  Mem.load Mfloat32 hitbox_m ob (Ptrofs.unsigned oo + 48) =
    Mem.load Mfloat32 scale_m ob (Ptrofs.unsigned oo + 48) ->
  Mem.load Mint32 hitbox_m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint16signed hitbox_m hb (Ptrofs.unsigned (Ptrofs.add ho (Ptrofs.repr 10))) = Some (Vint height) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) hitbox_m
    (Internal (ifgp_hitbox_body version)) [Vptr ob oo; Vptr hb ho] hitbox_t m' hitbox_result ->
  Mem.load Mfloat32 m' ob (Ptrofs.unsigned oo + 508) =
    Some (Vsingle (Float32.mul scale_y (Float32.of_int height))).
Proof.
  intros version m scale_m hitbox_m m' cb ob oo hb ho scale_y height scale_t scale_result
    hitbox_t hitbox_result HcurrentSep HtemplateSep Hroom Hsymbol Hcurrent HscaleCall
    HscaleContinuity HhitCurrent Htemplate HhitCall.
  destruct (isbh_completed_scale_sets_y _ _ _ _ _ _ _ _ _
    HcurrentSep Hroom Hsymbol Hcurrent HscaleCall) as (Hscale & _).
  rewrite Hscale in HscaleContinuity.
  rewrite <- (isbh_address oo 508 Hroom ltac:(lia)).
  eapply isbh_completed_hitbox_derives_height with (cb := cb)
    (hb := hb) (ho := ho) (scale_y := scale_y) (height := height);
    [exact HcurrentSep|exact HtemplateSep|exact Hroom|exact Hsymbol|
      exact HhitCurrent| |exact Htemplate|exact HhitCall].
  rewrite isbh_address by (auto; lia). exact HscaleContinuity.
Qed.

From Coq Require Import Reals Lra.
From LessThanOneAPress.Generated Require Import us_obj_behaviors_2 jp_obj_behaviors_2.
From LessThanOneAPress.Proofs Require Import InkBounceProducerEffect Area2Rank9ACoinFlight.
Module SBB := us_obj_behaviors_2.
Inductive StockBounceHeightKind := SBHGoomba | SBHPokey | SBHKlepto.
Definition isbh_stock_template version kind := match version, kind with
| VersionUS, SBHGoomba => us_obj_behaviors_2.v_sGoombaHitbox
| VersionJP, SBHGoomba => jp_obj_behaviors_2.v_sGoombaHitbox
| VersionUS, SBHPokey => us_obj_behaviors_2.v_sPokeyBodyPartHitbox
| VersionJP, SBHPokey => jp_obj_behaviors_2.v_sPokeyBodyPartHitbox
| VersionUS, SBHKlepto => us_obj_behaviors_2.v_sKleptoHitbox
| VersionJP, SBHKlepto => jp_obj_behaviors_2.v_sKleptoHitbox end.
Definition isbh_stock_template_ident kind := match kind with
| SBHGoomba => SBB._sGoombaHitbox | SBHPokey => SBB._sPokeyBodyPartHitbox
| SBHKlepto => SBB._sKleptoHitbox end.
Definition isbh_stock_template_height kind := match kind with
| SBHGoomba => 50 | SBHPokey => 20 | SBHKlepto => 250 end.
Definition isbh_native_body version kind := match version, kind with
| VersionUS, SBHGoomba => us_obj_behaviors_2.f_bhv_goomba_update
| VersionJP, SBHGoomba => jp_obj_behaviors_2.f_bhv_goomba_update
| VersionUS, SBHPokey => us_obj_behaviors_2.f_bhv_pokey_body_part_update
| VersionJP, SBHPokey => jp_obj_behaviors_2.f_bhv_pokey_body_part_update
| VersionUS, SBHKlepto => us_obj_behaviors_2.f_bhv_klepto_update
| VersionJP, SBHKlepto => jp_obj_behaviors_2.f_bhv_klepto_update end.
Theorem isbh_stock_templates_from_actual_initializers : forall version kind,
  ibp_hitbox_template_height (gvar_init (isbh_stock_template version kind)) =
    Some (isbh_stock_template_height kind).
Proof. intros [] []; reflexivity. Qed.

Fixpoint isbh_f32_initializers data := match data with
| [] => []
| Init_float32 value :: rest => value :: isbh_f32_initializers rest
| _ :: rest => isbh_f32_initializers rest end.
Definition isbh_goomba_scales version := isbh_f32_initializers
  (gvar_init (match version with
    | VersionUS => us_obj_behaviors_2.v_sGoombaProperties
    | VersionJP => jp_obj_behaviors_2.v_sGoombaProperties end)).
Theorem isbh_all_goomba_property_scales_checked : forall version,
  map Float32.to_bits (isbh_goomba_scales version) =
    [Int.repr 1069547520; Int.repr 1080033280; Int.repr 1056964608] /\
  map (fun scale => Float32.to_bits (Float32.mul scale (Float32.of_int (Int.repr 50))))
    (isbh_goomba_scales version) =
    [Int.repr 1117126656; Int.repr 1127153664; Int.repr 1103626240].
Proof. intros []; vm_compute; split; reflexivity. Qed.

Fixpoint isbh_native_has_template template s := match s with
| Scall _ (Evar called _) (Eaddrof (Evar found _) _ :: _) =>
    Pos.eqb called SBB._obj_handle_attacks && Pos.eqb found template
| Ssequence a b | Sifthenelse _ a b =>
    isbh_native_has_template template a || isbh_native_has_template template b
| Sloop a b => isbh_native_has_template template a || isbh_native_has_template template b
| Sswitch _ cases => isbh_cases_have_template template cases
| _ => false end
with isbh_cases_have_template template cases := match cases with
| LSnil => false
| LScons _ s rest => isbh_native_has_template template s || isbh_cases_have_template template rest end.
Theorem isbh_native_stock_template_callers_checked : forall version kind,
  isbh_native_has_template (isbh_stock_template_ident kind)
    (fn_body (isbh_native_body version kind)) = true.
Proof. intros [] []; reflexivity. Qed.

(** These are arithmetic bounds on the size read by the completed helper.
    Applying the scale bounds to every native history is a distinct task. *)
Theorem isbh_pokey_scale_product_at_most_60 : forall scale_y,
  rank9cf_finite scale_y -> (0 <= rank9cf_real scale_y <= 3)%R ->
  rank9cf_finite (Float32.mul scale_y (Float32.of_int (Int.repr 20))) /\
  (0 <= rank9cf_real (Float32.mul scale_y (Float32.of_int (Int.repr 20))) <= 60)%R.
Proof.
  intros scale_y Fs Hscale.
  destruct (rank9cf_integer_exact 20 ltac:(lia)) as [H20 F20].
  exact (rank9cf_mul_range scale_y (rank9cf_integer 20) 0 60
    Fs F20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite H20; cbn; nra)).
Qed.
Theorem isbh_goomba_scale_product_at_most_175 : forall scale_y,
  rank9cf_finite scale_y -> (0 <= rank9cf_real scale_y <= 7/2)%R ->
  rank9cf_finite (Float32.mul scale_y (Float32.of_int (Int.repr 50))) /\
  (0 <= rank9cf_real (Float32.mul scale_y (Float32.of_int (Int.repr 50))) <= 175)%R.
Proof.
  intros scale_y Fs Hscale.
  destruct (rank9cf_integer_exact 50 ltac:(lia)) as [H50 F50].
  exact (rank9cf_mul_range scale_y (rank9cf_integer 50) 0 175
    Fs F50 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite H50; cbn; nra)).
Qed.
Theorem isbh_klepto_scale_product_at_most_250 : forall scale_y,
  rank9cf_finite scale_y -> (0 <= rank9cf_real scale_y <= 1)%R ->
  rank9cf_finite (Float32.mul scale_y (Float32.of_int (Int.repr 250))) /\
  (0 <= rank9cf_real (Float32.mul scale_y (Float32.of_int (Int.repr 250))) <= 250)%R.
Proof.
  intros scale_y Fs Hscale.
  destruct (rank9cf_integer_exact 250 ltac:(lia)) as [H250 F250].
  exact (rank9cf_mul_range scale_y (rank9cf_integer 250) 0 250
    Fs F250 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite H250; cbn; nra)).
Qed.

Theorem isbh_completed_stock_hitbox_uses_source_template : forall version kind m cb ob oo hb scale_y t m' result,
  cb <> ob -> hb <> ob -> isbh_room oo ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SBH._gCurrentObject = Some cb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (isbh_stock_template_ident kind) = Some hb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 48))) = Some (Vsingle scale_y) ->
  Mem.load Mint16signed m hb 10 = Some (Vint (Int.repr (isbh_stock_template_height kind))) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifgp_hitbox_body version)) [Vptr ob oo; Vptr hb Ptrofs.zero] t m' result ->
  Mem.load Mfloat32 m' ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508))) =
    Some (Vsingle (Float32.mul scale_y (Float32.of_int (Int.repr (isbh_stock_template_height kind))))).
Proof.
  intros version kind m cb ob oo hb scale_y t m' result Hsep HtemplateSep Hroom
    Hsymbol HtemplateSymbol Hcurrent Hscale Htemplate Hcall.
  eapply isbh_completed_hitbox_derives_height with (cb := cb)
    (hb := hb) (ho := Ptrofs.zero) (scale_y := scale_y)
    (height := Int.repr (isbh_stock_template_height kind));
    [exact Hsep|exact HtemplateSep|exact Hroom|exact Hsymbol|
      exact Hcurrent|exact Hscale| |exact Hcall].
  change (Mem.load Mint16signed m hb 10 =
    Some (Vint (Int.repr (isbh_stock_template_height kind)))).
  exact Htemplate.
Qed.
