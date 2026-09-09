(** Identify the real retry arguments and its read at the caller boundary.
    This does not assume that the displayed height is reachable without A. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyEntry ObjectContactNecessity
  EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ibcc_state := Ederef
  (Etempvar IBM._m (tptr (Tstruct IBM._MarioState noattr)))
  (Tstruct IBM._MarioState noattr).
Definition ibcc_object := Ederef
  (Etempvar IBM._t'45 (tptr (Tstruct IBM._Object noattr)))
  (Tstruct IBM._Object noattr).
Definition ibcc_header := Efield ibcc_object IBM._header
  (Tstruct IBM._ObjectNode noattr).
Definition ibcc_graphics := Efield ibcc_header IBM._gfx
  (Tstruct IBM._GraphNodeObject noattr).
Definition ibcc_destination := Efield ibcc_state IBM._pos (tarray tfloat 3).
Definition ibcc_source := Efield ibcc_graphics IBM._pos (tarray tfloat 3).

Lemma ibcc_arguments_are_generated : forall version,
  ibk_copy_args version = [ibcc_destination; ibcc_source].
Proof. intros []; reflexivity. Qed.

Definition ibcc_field_ok (ce : composite_env) (tag field : ident) (offset : Z) :=
  match ce ! tag with
  | Some co => match field_offset ce field (co_members co) with
      | OK (actual, Full) => Z.eqb actual offset | _ => false end
  | None => false end.

Lemma ibcc_field_ok_sound : forall ce tag field offset,
  ibcc_field_ok ce tag field offset = true ->
  exists co, ce ! tag = Some co /\
    field_offset ce field (co_members co) = OK (offset, Full).
Proof.
  intros ce tag field offset H. unfold ibcc_field_ok in H.
  destruct (ce ! tag) as [co|] eqn:Hco; try discriminate.
  destruct (field_offset ce field (co_members co)) as [[actual bf]|] eqn:Hfield;
    try discriminate.
  destruct bf; try discriminate. apply Z.eqb_eq in H. subst. eauto.
Qed.

Lemma ibcc_selected_fields : forall version,
  let ce := genv_cenv (Clight.globalenv (selected_clight_target version)) in
  ibcc_field_ok ce IBM._MarioState IBM._pos 60 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._marioObj 136 = true /\
  ibcc_field_ok ce IBM._Object IBM._header 0 = true /\
  ibcc_field_ok ce IBM._ObjectNode IBM._gfx 0 = true /\
  ibcc_field_ok ce IBM._GraphNodeObject IBM._pos 32 = true.
Proof.
  intros version. cbn zeta.
  change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
      IBM._MarioState IBM._pos 60 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
      IBM._MarioState IBM._marioObj 136 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
      IBM._Object IBM._header 0 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
      IBM._ObjectNode IBM._gfx 0 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
      IBM._GraphNodeObject IBM._pos 32 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Lemma ibcc_deref_struct : forall ge e le m id tag b ofs answer,
  le ! id = Some (Vptr b ofs) ->
  eval_expr ge e le m
    (Ederef (Etempvar id (tptr (Tstruct tag noattr))) (Tstruct tag noattr)) answer ->
  answer = Vptr b ofs.
Proof.
  intros ge e le m id tag b ofs answer Htemp Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl; subst end.
  match goal with Ht : eval_expr _ _ _ _ (Etempvar _ _) ?value |- _ =>
    assert (value = Vptr b ofs) by (eapply ocn_temp_value; eauto);
    match goal with H : value = Vptr b ofs |- _ => inversion H; subst end end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; try discriminate end.
  reflexivity.
Qed.

Lemma ibcc_field_location : forall ge e le m base tag field ty b ofs delta loc offset bf,
  typeof base = Tstruct tag noattr ->
  (forall answer, eval_expr ge e le m base answer -> answer = Vptr b ofs) ->
  ibcc_field_ok ge tag field delta = true ->
  eval_lvalue ge e le m (Efield base field ty) loc offset bf ->
  loc = b /\ offset = Ptrofs.add ofs (Ptrofs.repr delta) /\ bf = Full.
Proof.
  intros ge e le m base tag field ty b ofs delta loc offset bf Htype Hbase Hfield Hl.
  destruct (ibcc_field_ok_sound _ _ _ _ Hfield) as (description & Hco & Hoffset).
  inversion Hl; subst; try congruence.
  match goal with Ht : typeof base = Tstruct _ _ |- _ =>
    rewrite Htype in Ht; inversion Ht; subst end.
  match goal with Hr : eval_expr _ _ _ _ base _ |- _ =>
    apply Hbase in Hr; inversion Hr; subst end.
  repeat split; congruence.
Qed.

Lemma ibcc_aggregate_field : forall ge e le m base tag field ty b ofs delta answer,
  typeof base = Tstruct tag noattr ->
  (forall value, eval_expr ge e le m base value -> value = Vptr b ofs) ->
  ibcc_field_ok ge tag field delta = true ->
  (access_mode ty = By_reference \/ access_mode ty = By_copy) ->
  eval_expr ge e le m (Efield base field ty) answer ->
  answer = Vptr b (Ptrofs.add ofs (Ptrofs.repr delta)).
Proof.
  intros ge e le m base tag field ty b ofs delta answer Htype Hbase Hfield Hmode Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibcc_field_location _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Htype Hbase Hfield Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; destruct Hmode; cbn [typeof] in *; congruence end.
Qed.

Lemma ibcc_pointer_field : forall ge e le m base tag field b ofs delta answer value,
  typeof base = Tstruct tag noattr ->
  (forall v, eval_expr ge e le m base v -> v = Vptr b ofs) ->
  ibcc_field_ok ge tag field delta = true ->
  Mem.load Mint32 m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some value ->
  eval_expr ge e le m (Efield base field (tptr (Tstruct IBM._Object noattr))) answer ->
  answer = value.
Proof.
  intros ge e le m base tag field b ofs delta answer value Htype Hbase Hfield Hload Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibcc_field_location _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Htype Hbase Hfield Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn [typeof access_mode] in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mint32 m b
      (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some answer) in Hr;
    congruence end.
Qed.

(** This is the actual caller read, tied to the selected MarioState layout. *)
Theorem ibcc_actual_object_read : forall version e le m mb mo object answer,
  le ! IBM._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) = Some object ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ibk_object_read answer -> answer = object.
Proof.
  intros version e le m mb mo object answer Hm Hload Hread.
  destruct (ibcc_selected_fields version) as (_ & Hfield & _).
  eapply ibcc_pointer_field with (base := ibcc_state) (tag := IBM._MarioState)
    (field := IBM._marioObj) (delta := 136);
    [reflexivity| |exact Hfield|exact Hload|exact Hread].
  intros. eapply ibcc_deref_struct; eauto.
Qed.

Theorem ibcc_actual_argument_pointers : forall version e le m mb mo ob oo args,
  le ! IBM._m = Some (Vptr mb mo) ->
  le ! IBM._t'45 = Some (Vptr ob oo) ->
  eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_copy_args version) [tptr tfloat; tptr tfloat] args ->
  args = [Vptr mb (Ptrofs.add mo (Ptrofs.repr 60));
    Vptr ob (Ptrofs.add oo (Ptrofs.repr 32))].
Proof.
  intros version e le m mb mo ob oo args Hm Hobject Hargs.
  destruct (ibcc_selected_fields version) as (Hpos & _ & Hheader & Hgfx & Hgpos).
  assert (forall answer, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_state answer -> answer = Vptr mb mo) as Hstate
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall answer, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_object answer -> answer = Vptr ob oo) as Hobj
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall answer, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_header answer -> answer = Vptr ob oo) as Hhead.
  { intros answer Hread. pose proof (ibcc_aggregate_field _ _ _ _
      ibcc_object IBM._Object IBM._header (Tstruct IBM._ObjectNode noattr) ob oo 0 answer
      eq_refl Hobj Hheader (or_intror eq_refl) Hread) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (forall answer, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_graphics answer -> answer = Vptr ob oo) as Hgraph.
  { intros answer Hread. pose proof (ibcc_aggregate_field _ _ _ _
      ibcc_header IBM._ObjectNode IBM._gfx (Tstruct IBM._GraphNodeObject noattr) ob oo 0 answer
      eq_refl Hhead Hgfx (or_intror eq_refl) Hread) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (forall answer, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_destination answer ->
    answer = Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))) as Hdest.
  { intros. eapply ibcc_aggregate_field with (base := ibcc_state)
      (tag := IBM._MarioState) (field := IBM._pos) (ty := tarray tfloat 3)
      (delta := 60); eauto; reflexivity. }
  assert (forall answer, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_source answer ->
    answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32))) as Hsource.
  { intros. eapply ibcc_aggregate_field with (base := ibcc_graphics)
      (tag := IBM._GraphNodeObject) (field := IBM._pos) (ty := tarray tfloat 3)
      (delta := 32); eauto; reflexivity. }
  rewrite ibcc_arguments_are_generated in Hargs.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ ibcc_destination _ |- _ =>
    apply Hdest in H; subst end.
  match goal with H : eval_expr _ _ _ _ ibcc_source _ |- _ =>
    apply Hsource in H; subst end.
  repeat match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst; clear H end.
  reflexivity.
Qed.

Lemma ibcc_ordinary_storage_separate : forall version mb ob,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  mb <> ob.
Proof.
  intros. eapply Genv.global_addresses_distinct; eauto. discriminate.
Qed.

Lemma ibcc_loaded_block_valid : forall chunk m b ofs value,
  Mem.load chunk m b ofs = Some value -> Mem.valid_block m b.
Proof.
  intros. eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; [eapply Mem.load_valid_access; eassumption|constructor].
Qed.

Definition InkRetryEntryHeightCut : Prop :=
  forall version e le m mb mo ob oo t le' m' out,
  e ! IBM._vec3f_copy = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  le ! IBM._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) =
    Some (Vptr ob oo) ->
  Mem.valid_block m ob ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' m' out ->
  exists copy_e y_le y_m after_le after_m value copy_memory
    pre store suf query_trace,
    t = (pre ++ (store ++ suf)) ++ query_trace /\
    Mem.load Mfloat32 m ob
      (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36))) = Some value /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) copy_e
      (PTree.set IBV._t'4 value
        (PTree.set IBV._t'3 (Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))) y_le)) y_m
      ibk_y_store store after_le after_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBM._t'45 (Vptr ob oo) le) copy_memory
      (ibk_second_query version) query_trace le' m' out.

(** Same retry, same object read, same copy, same subsequent floor query.
    The symbol facts derive separation; the ordinary live pointer/read facts
    are still premises, not a proof of every preceding gameplay frame. *)
Theorem ibcc_retry_reads_entry_display_height : InkRetryEntryHeightCut.
Proof.
  unfold InkRetryEntryHeightCut.
  intros version e le m mb mo ob oo t le' m' out
    Hlocal HstateSymbol HobjectSymbol Hm Hobject Hvalid Hretry.
  destruct (ibk_taken_retry_has_real_copy_predecessor _ _ _ _ _ _ _ _ Hlocal Hretry)
    as (object & args & result & copy_memory & copy_trace & query_trace &
      Htrace & HobjectRead & Hargs & Hcall & Hquery).
  assert (object = Vptr ob oo) by (eapply ibcc_actual_object_read; eauto).
  subst object.
  assert ((PTree.set IBM._t'45 (Vptr ob oo) le) ! IBM._m = Some (Vptr mb mo))
    as HmNow by (rewrite PTree.gso by discriminate; exact Hm).
  pose proof (ibcc_actual_argument_pointers _ _ _ _ _ _ _ _ _
    HmNow (PTree.gss _ _ _) Hargs) as HargValues.
  subst args.
  pose proof (ibcc_ordinary_storage_separate _ _ _ HstateSymbol HobjectSymbol) as Hseparate.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ Hobject) as HstateValid.
  destruct (ibc_actual_copy_reads_entry_height _ _ _ _ _ _ _ _ _
    Hseparate HstateValid Hvalid Hcall)
    as (copy_e & y_le & y_m & after_le & after_m & value & pre & store & suf &
      Hcopytrace & Hload & Hread & Hstore).
  rewrite Ptrofs.add_assoc in Hload.
  change (Ptrofs.add (Ptrofs.repr 32) (Ptrofs.repr 4)) with (Ptrofs.repr 36) in Hload.
  exists copy_e, y_le, y_m, after_le, after_m, value, copy_memory,
    pre, store, suf, query_trace.
  repeat split; try assumption. rewrite Hcopytrace in Htrace. exact Htrace.
Qed.

(** In the normal floating-point case this is an exact MarioState Y store,
    not just a statement that an unspecified destination receives a value. *)
Definition InkRetryEntrySingleStore : Prop :=
  forall version e le m mb mo ob oo height t le' m' out,
  e ! IBM._vec3f_copy = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  le ! IBM._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) =
    Some (Vptr ob oo) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36))) =
    Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' m' out ->
  exists copy_e y_le y_m after_le after_m copy_memory pre suf query_trace,
    t = (pre ++ suf) ++ query_trace /\
    Mem.store Mfloat32 y_m mb
      (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64)))
      (Vsingle height) = Some after_m /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) copy_e
      (PTree.set IBV._t'4 (Vsingle height)
        (PTree.set IBV._t'3 (Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))) y_le)) y_m
      ibk_y_store E0 after_le after_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set IBM._t'45 (Vptr ob oo) le) copy_memory
      (ibk_second_query version) query_trace le' m' out.

Theorem ibcc_retry_stores_entry_display_single : InkRetryEntrySingleStore.
Proof.
  unfold InkRetryEntrySingleStore.
  intros version e le m mb mo ob oo height t le' m' out
    Hlocal Hstate Hpool Hm Hobj Hheight Hrun.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ Hheight) as Hvalid.
  destruct (ibcc_retry_reads_entry_display_height _ _ _ _ _ _ _ _ _ _ _ _
    Hlocal Hstate Hpool Hm Hobj Hvalid Hrun)
    as (copy_e & y_le & y_m & after_le & after_m & value & copy_memory &
      pre & store & suf & query_trace & Htrace & Hread & Hstore & Hquery).
  assert (value = Vsingle height) by congruence. subst value.
  pose proof Hstore as HactualStore.
  destruct (ibk_y_store_preserves_the_read_single _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) Hstore) as (block & offset & Hlocation & Hwrite & -> & _).
  match type of Hlocation with eval_lvalue _ _ ?temps _ _ _ _ _ =>
    assert (temps ! IBV._t'3 =
      Some (Vptr mb (Ptrofs.add mo (Ptrofs.repr 60)))) as Hdest
      by (rewrite PTree.gso by discriminate; apply PTree.gss)
  end.
  destruct (ibc_index_location _ _ _ _ _ _ _ _ _ _ _ Hdest Hlocation)
    as (-> & -> & _).
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1)))
    with (Ptrofs.repr 4) in Hwrite.
  rewrite Ptrofs.add_assoc in Hwrite.
  change (Ptrofs.add (Ptrofs.repr 60) (Ptrofs.repr 4)) with (Ptrofs.repr 64) in Hwrite.
  exists copy_e, y_le, y_m, after_le, after_m, copy_memory, pre, suf, query_trace.
  repeat split; assumption.
Qed.

Definition InkBackwardCallerBoundary : Prop :=
  InkBackwardExecutionBoundary /\ InkCopyEntryHeightCut /\
  InkRetryEntryHeightCut /\ InkRetryEntrySingleStore.

Theorem ibcc_backward_caller_boundary_checked : InkBackwardCallerBoundary.
Proof.
  split; [exact ibk_backward_execution_boundary_checked|].
  split; [exact ibc_actual_copy_reads_entry_height|].
  split; [exact ibcc_retry_reads_entry_display_height|].
  exact ibcc_retry_stores_entry_display_single.
Qed.
