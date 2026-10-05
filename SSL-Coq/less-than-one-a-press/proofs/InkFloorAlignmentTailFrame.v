(** The final alignment pointer assignment is a real, position-preserving
    store.  The preceding matrix helper still has explicit call obligations:
    its direct stores and fresh scratch allocations are accounted for here,
    but a whole-call matrix frame is deliberately not assumed. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_math_util jp_math_util.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkFloorAlignmentBackward InkCopyCaller InkQuicksandSource
  InkQuicksandExpressions InkQuicksandStores InkRawCopyStores
  InkBackwardSource InkBackwardExecution InkFloorResetExecution InkPlatformWriteFrame
  ObjectContactNecessity ContactConsumerExecution OrdinaryArea1EntryMemory
  Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IFAT := us_math_util.

Definition ifat_matrix_global :=
  Evar IMB._sFloorAlignMatrix (tarray (tarray (tarray tfloat 4) 4) 2).
Definition ifat_matrix_rhs := Ebinop Oadd ifat_matrix_global
  (Etempvar IMB._t'2 tushort) (tptr (tarray (tarray tfloat 4) 4)).
Definition ifat_object := Ederef
  (Etempvar IMB._t'1 (tptr (Tstruct IMB._Object noattr)))
  (Tstruct IMB._Object noattr).
Definition ifat_header := Efield ifat_object IMB._header
  (Tstruct IMB._ObjectNode noattr).
Definition ifat_graphics := Efield ifat_header IMB._gfx
  (Tstruct IMB._GraphNodeObject noattr).
Definition ifat_matrix_lhs := Efield ifat_graphics IMB._throwMatrix iq_matrix_type.
Definition ifat_final version := rank12b_drop_sequences 1 (imb_align_tail version).

Theorem ifat_final_assignment_is_generated : forall version,
  imb_align_tail version = Ssequence (ibk_head (imb_align_tail version))
    (ifat_final version) /\
  ifat_final version = Ssequence (Sset IMB._t'1 ibk_object_read)
    (Ssequence (Sset IMB._t'2 (Efield ibcc_state IMB._unk00 tushort))
      (Sassign ifat_matrix_lhs ifat_matrix_rhs)).
Proof. intros []; split; reflexivity. Qed.

Lemma ifat_graphics_value : forall version e le m ob oo answer,
  le ! IMB._t'1 = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ifat_graphics answer -> answer = Vptr ob oo.
Proof.
  intros version e le m ob oo answer Ho Hr.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & _).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ifat_object v -> v = Vptr ob oo) as Hobject
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ifat_header v -> v = Vptr ob oo) as Hhead.
  { intros v Hread. pose proof (ibcc_aggregate_field _ _ _ _ ifat_object
      IMB._Object IMB._header (Tstruct IMB._ObjectNode noattr) ob oo 0 v
      eq_refl Hobject Hheader (or_intror eq_refl) Hread) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  pose proof (ibcc_aggregate_field _ _ _ _ ifat_header IMB._ObjectNode IMB._gfx
    (Tstruct IMB._GraphNodeObject noattr) ob oo 0 answer eq_refl Hhead Hgfx
    (or_intror eq_refl) Hr) as H.
  rewrite Ptrofs.add_zero in H. exact H.
Qed.

Lemma ifat_matrix_lhs_location : forall version e le m ob oo b ofs bf,
  le ! IMB._t'1 = Some (Vptr ob oo) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    ifat_matrix_lhs b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr 80) /\ bf = Full.
Proof.
  intros version e le m ob oo b ofs bf Ho Hr.
  eapply ibcc_field_location with (base := ifat_graphics)
    (tag := IMB._GraphNodeObject) (field := IMB._throwMatrix)
    (ty := iq_matrix_type) (delta := 80).
  - reflexivity.
  - intros; eapply ifat_graphics_value; eauto.
  - exact (proj2 (iq_selected_fields version)).
  - exact Hr.
Qed.

Lemma ifat_matrix_global_value : forall version e le m qb answer,
  e ! IMB._sFloorAlignMatrix = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IMB._sFloorAlignMatrix = Some qb ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ifat_matrix_global answer -> answer = Vptr qb Ptrofs.zero.
Proof.
  intros version e le m qb answer Hlocal Hsymbol Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ ifat_matrix_global _ _ _ |- _ =>
    inversion Hl; subst; try congruence end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; try discriminate end.
  congruence.
Qed.

Lemma ifat_matrix_rhs_points_to_global : forall version e le m qb answer,
  e ! IMB._sFloorAlignMatrix = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IMB._sFloorAlignMatrix = Some qb ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ifat_matrix_rhs answer -> exists qo, answer = Vptr qb qo.
Proof.
  intros version e le m qb answer Hlocal Hsymbol Hr.
  inversion Hr; subst.
  - match goal with Hbase : eval_expr _ _ _ _ ifat_matrix_global ?v |- _ =>
      assert (v = Vptr qb Ptrofs.zero) by
        (eapply ifat_matrix_global_value; eauto); subst v end.
    match goal with Hsem : sem_binary_operation _ Oadd _ _ ?value _ _ = Some answer |- _ =>
      destruct value; cbn [ifat_matrix_global typeof sem_binary_operation sem_add]
        in Hsem; try discriminate; inversion Hsem; subst;
        eexists; reflexivity end.
  - match goal with Hbad : eval_lvalue _ _ _ _ ifat_matrix_rhs _ _ _ |- _ =>
      inversion Hbad end.
Qed.

(** This theorem starts after the matrix call.  Its Object receiver is read
    from the actual MarioState, not granted as an unrelated temporary. *)
Theorem ifat_final_stage_has_only_the_pointer_store :
  forall version e le m mb mo ob oo qb t le' after out,
  le ! IMB._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) =
    Some (Vptr ob oo) ->
  e ! IMB._sFloorAlignMatrix = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IMB._sFloorAlignMatrix = Some qb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifat_final version) t le' after out ->
  exists qo,
    Mem.store Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 80)))
      (Vptr qb qo) = Some after /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m mb mo ob oo qb t le' after out Hm Ho Hlocal Hsymbol Hrun.
  rewrite (proj2 (ifat_final_assignment_is_generated version)) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?value |- _ =>
    assert (value = Vptr ob oo) by (eapply ibcc_actual_object_read; eauto);
    subst value end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ ?temps _ ifat_matrix_lhs _ _ _ |- _ =>
    assert (temps ! IMB._t'1 = Some (Vptr ob oo)) as Hreceiver
      by (rewrite PTree.gso by discriminate; apply PTree.gss);
    destruct (ifat_matrix_lhs_location _ _ _ _ _ _ _ _ _ Hreceiver Hl)
      as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ ifat_matrix_rhs ?value |- _ =>
    destruct (ifat_matrix_rhs_points_to_global _ _ _ _ _ _ Hlocal Hsymbol Hr)
      as (qo & ->) end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn [ifat_matrix_lhs ifat_matrix_rhs iq_matrix_type typeof] in Hcast;
    inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn [ifat_matrix_lhs iq_matrix_type access_mode] in Hmode;
    inversion Hmode; subst end.
  eexists. split; [eassumption|]. split; reflexivity.
Qed.

Definition InkAlignmentFinalPointerFrame : Prop :=
  forall version e le m mb ob slot qb t le' after out,
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IMB._sFloorAlignMatrix = Some qb ->
  e ! IMB._sFloorAlignMatrix = None ->
  le ! IMB._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifat_final version) t le' after out ->
  exists qo,
    Mem.load Mint32 after ob (object_slot_offset slot + 80) = Some (Vptr qb qo) /\
    iq_matrix_storage_separate mb ob slot (Some (qb,qo)) /\
    (forall chunk ofs, Mem.load chunk after mb ofs = Mem.load chunk m mb ofs) /\
    (forall delta, In delta [32;36;40;160;164;168] ->
      Mem.load Mfloat32 after ob (object_slot_offset slot + delta) =
        Mem.load Mfloat32 m ob (object_slot_offset slot + delta)).

Theorem ifat_final_pointer_assignment_preserves_position_records :
  InkAlignmentFinalPointerFrame.
Proof.
  unfold InkAlignmentFinalPointerFrame.
  intros version e le m mb ob slot qb t le' after out
    Hslot Hstate Hpool Hmatrix Hlocal Hm Hobject Hrun.
  assert (mb <> ob) as HstatePool by
    (exact (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool)).
  assert (qb <> mb) as HmatrixState by
    (eapply Genv.global_addresses_distinct; [|exact Hmatrix|exact Hstate]; discriminate).
  assert (qb <> ob) as HmatrixPool by
    (eapply Genv.global_addresses_distinct; [|exact Hmatrix|exact Hpool]; discriminate).
  destruct (ifat_final_stage_has_only_the_pointer_store version e le m mb Ptrofs.zero
    ob (Ptrofs.repr (object_slot_offset slot)) qb t le' after out
    Hm Hobject Hlocal Hmatrix Hrun) as (qo & Hstore & _).
  rewrite irc_slot_address in Hstore by (auto; lia).
  exists qo. split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  split; [split; [exact HmatrixState|left; exact HmatrixPool]|].
  split.
  - intros chunk ofs. eapply Mem.load_store_other; [exact Hstore|left; exact HstatePool].
  - intros delta Hin. eapply Mem.load_store_other; [exact Hstore|].
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
      cbn [size_chunk]; first [right; left; lia|right; right; lia].
Qed.

(** Extract the two actual adjacent tail segments from a completed alignment
    call.  The final frame is available under the reached Object read; it
    does not silently transfer that read across the unframed matrix helper. *)
Definition InkAlignmentCompletedTailPositionCut : Prop :=
  forall version m mb ob slot qb floor t after result,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Genv.find_symbol ge IMB._sFloorAlignMatrix = Some qb ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle floor) ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (imb_body version IMBAlign))
    [Vptr mb Ptrofs.zero] t after result ->
  exists snap_le snap_m matrix_le matrix_m final_le tm tf out,
    Mem.store Mfloat32 m mb 64 (Vsingle floor) = Some snap_m /\
    ocn_exec ge empty_env snap_le snap_m (ibk_head (imb_align_tail version))
      tm matrix_le matrix_m Out_normal /\
    ocn_exec ge empty_env matrix_le matrix_m (ifat_final version)
      tf final_le after out /\
    (Mem.load Mint32 matrix_m mb 136 =
      Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
      exists qo,
        Mem.load Mint32 after ob (object_slot_offset slot + 80) = Some (Vptr qb qo) /\
        iq_matrix_storage_separate mb ob slot (Some (qb,qo)) /\
        (forall chunk ofs, Mem.load chunk after mb ofs = Mem.load chunk matrix_m mb ofs) /\
        (forall delta, In delta [32;36;40;160;164;168] ->
          Mem.load Mfloat32 after ob (object_slot_offset slot + delta) =
            Mem.load Mfloat32 matrix_m ob (object_slot_offset slot + delta))).

Theorem ifat_completed_alignment_reaches_the_position_framed_final_store :
  InkAlignmentCompletedTailPositionCut.
Proof.
  unfold InkAlignmentCompletedTailPositionCut.
  cbn zeta.
  intros version m mb ob slot qb floor t after result
    Hslot Hstate Hpool Hmatrix Hfloor Hcall.
  destruct (imb_alignment_copies_entry_floor_and_preserves_object version m mb ob
    floor t after result Hstate Hpool Hfloor Hcall)
    as (snap_le & snap_m & final_le & out & Hsnap & _ & _ & Hm & Htail).
  rewrite (proj1 (ifat_final_assignment_is_generated version)) in Htail.
  assert (ibk_normal (ibk_head (imb_align_tail version)) = true) as Hnormal
    by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Htail)
    as (matrix_le & matrix_m & tm & tf & _ & HmatrixRun & Hfinal).
  exists snap_le, snap_m, matrix_le, matrix_m, final_le, tm, tf, out.
  repeat apply conj; try assumption.
  intros Hobject.
  assert (matrix_le ! IMB._m = Some (Vptr mb Ptrofs.zero)) as HmatrixM.
  { erewrite ifr_execution_keeps_temp; [exact Hm|exact HmatrixRun|].
    destruct version; reflexivity. }
  eapply (ifat_final_pointer_assignment_preserves_position_records version
    empty_env matrix_le matrix_m mb ob slot qb tf final_le after out);
    [exact Hslot|exact Hstate|exact Hpool|exact Hmatrix|apply PTree.gempty|
     exact HmatrixM|exact Hobject|exact Hfinal].
Qed.

(** A bounded, sound direct-store inventory for the actual matrix helper.
    Calls are recorded separately below; they are not granted this frame. *)
Definition ifat_matrix_body version := match version with
| VersionUS => us_math_util.f_mtxf_align_terrain_triangle
| VersionJP => jp_math_util.f_mtxf_align_terrain_triangle end.
Definition ifat_scratch := map fst (fn_vars (ifat_matrix_body VersionUS)).
Fixpoint ifat_store_lvalues (s : statement) : list expr := match s with
| Sassign lhs _ => [lhs]
| Ssequence a b | Sifthenelse _ a b | Sloop a b =>
    ifat_store_lvalues a ++ ifat_store_lvalues b
| _ => [] end.
Fixpoint ifat_calls (s : statement) : list ident := match s with
| Scall _ (Evar id _) _ => [id]
| Ssequence a b | Sifthenelse _ a b | Sloop a b => ifat_calls a ++ ifat_calls b
| _ => [] end.

Theorem ifat_matrix_direct_store_and_call_inventory : forall version,
  fn_vars (ifat_matrix_body version) = fn_vars (ifat_matrix_body VersionUS) /\
  forallb (ipw_write ifat_scratch [IFAT._mtx])
    (ifat_store_lvalues (fn_body (ifat_matrix_body version))) = true /\
  ifat_calls (fn_body (ifat_matrix_body version)) =
    [IFAT._find_floor; IFAT._find_floor; IFAT._find_floor;
     IFAT._vec3f_set; IFAT._find_vector_perpendicular_to_plane;
     IFAT._vec3f_normalize; IFAT._vec3f_cross; IFAT._vec3f_normalize;
     IFAT._vec3f_cross; IFAT._vec3f_normalize] /\
  ifat_calls (fn_body (match version with
    | VersionUS => us_math_util.f_vec3f_normalize
    | VersionJP => jp_math_util.f_vec3f_normalize end)) = [IFAT._sqrtf].
Proof. intros []; repeat split; reflexivity. Qed.

Theorem ifat_reached_direct_matrix_store_frames_other_block :
  forall version e le m protected lhs rhs t le' after out,
  In lhs (ifat_store_lvalues (fn_body (ifat_matrix_body version))) ->
  ipw_context (Clight.globalenv (selected_clight_target version)) e le protected
    ifat_scratch [IFAT._mtx] [] ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign lhs rhs) t le' after out ->
  t = E0 /\ ipw_frame protected m after.
Proof.
  intros version e le m protected lhs rhs t le' after out Hin Hcontext Hrun.
  pose proof (proj1 (proj2 (ifat_matrix_direct_store_and_call_inventory version))) as Hsource.
  rewrite forallb_forall in Hsource.
  eapply ipw_write_frame; [exact Hcontext|exact (Hsource lhs Hin)|exact Hrun].
Qed.

(** Actual entry derives separation of every scratch allocation from any
    valid pre-existing protected block.  The matrix argument is separately
    required to be outside that block, as ordinary global symbols supply. *)
Lemma ifat_alloc_keeps_other_names : forall ge e m vars e' m',
  alloc_variables ge e m vars e' m' -> forall id,
  ~ In id (map fst vars) -> e' ! id = e ! id.
Proof.
  intros ge e m vars e' m' Halloc. induction Halloc; intros query Houtside.
  - reflexivity.
  - cbn in Houtside. rewrite IHHalloc by tauto.
    apply PTree.gso. intro Heq. subst query. apply Houtside. left; reflexivity.
Qed.

Lemma ifat_alloc_defines_local_names : forall ge e m vars e' m',
  alloc_variables ge e m vars e' m' -> forall id,
  In id (map fst vars) -> exists b ty, e' ! id = Some (b,ty).
Proof.
  intros ge e m vars e' m' Halloc. induction Halloc; intros query Hin.
  - contradiction.
  - cbn in Hin. destruct Hin as [<-|Hin]; [|exact (IHHalloc query Hin)].
    destruct (in_dec Pos.eq_dec id (map fst vars)) as [Hlater|Houtside].
    + exact (IHHalloc id Hlater).
    + rewrite (ifat_alloc_keeps_other_names _ _ _ _ _ _ Halloc id Houtside).
      do 2 eexists. apply PTree.gss.
Qed.

Theorem ifat_matrix_entry_has_separate_scratch :
  forall version ge m qb qo pos yaw radius e le entry protected,
  Mem.valid_block m protected -> qb <> protected ->
  function_entry2 ge (ifat_matrix_body version)
    [Vptr qb qo; pos; yaw; radius] m e le entry ->
  (forall id b ty, e ! id = Some (b,ty) -> b <> protected) /\
  ipw_frame protected m entry /\
  ipw_context ge e le protected ifat_scratch [IFAT._mtx] [].
Proof.
  intros version ge m qb qo pos yaw radius e le entry protected Hvalid Hmatrix Hentry.
  assert (fn_params (ifat_matrix_body version) =
    [(IFAT._mtx, tptr (tarray tfloat 4)); (IFAT._pos, tptr tfloat);
     (IFAT._yaw,tshort); (IFAT._radius,tfloat)]) as Hparams
    by (destruct version; reflexivity).
  inversion Hentry; subst.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    destruct (ipw_alloc_frame _ _ _ _ _ _ Ha protected Hvalid
      ltac:(intros id b ty Hread; rewrite PTree.gempty in Hread; discriminate))
      as (Hlocals & Hframe & _) end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IFAT._mtx = Some (Vptr qb qo)) as Hmtx by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb; subst temps;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss) end.
  split; [exact Hlocals|]. split; [exact Hframe|].
  split.
  - intros id Hin. split; [intros; eapply Hlocals; eauto|].
    intros Hnone target Hsymbol.
    assert (In id (map fst (fn_vars (ifat_matrix_body version)))) as Hvar
      by (destruct version; exact Hin).
    match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
      destruct (ifat_alloc_defines_local_names _ _ _ _ _ _ Ha id Hvar)
        as (local & ty & Hdefined)
    end.
    congruence.
  - split.
    + intros id Hin b ofs Hread. destruct Hin as [<-|[]].
      rewrite Hmtx in Hread. inversion Hread; subst. exact Hmatrix.
    + intros id Hin. contradiction.
Qed.

Definition InkAlignmentTailFrameBoundary : Prop :=
  InkAlignmentFinalPointerFrame /\ InkAlignmentCompletedTailPositionCut /\
  (forall version,
    forallb (ipw_write ifat_scratch [IFAT._mtx])
      (ifat_store_lvalues (fn_body (ifat_matrix_body version))) = true /\
    ifat_calls (fn_body (ifat_matrix_body version)) =
      [IFAT._find_floor; IFAT._find_floor; IFAT._find_floor;
       IFAT._vec3f_set; IFAT._find_vector_perpendicular_to_plane;
       IFAT._vec3f_normalize; IFAT._vec3f_cross; IFAT._vec3f_normalize;
       IFAT._vec3f_cross; IFAT._vec3f_normalize]).

Theorem ifat_alignment_tail_frame_boundary_checked : InkAlignmentTailFrameBoundary.
Proof.
  split; [exact ifat_final_pointer_assignment_preserves_position_records|].
  split; [exact ifat_completed_alignment_reaches_the_position_framed_final_store|].
  intro version. destruct (ifat_matrix_direct_store_and_call_inventory version)
    as (_ & Hstore & Hcalls & _). auto.
Qed.
