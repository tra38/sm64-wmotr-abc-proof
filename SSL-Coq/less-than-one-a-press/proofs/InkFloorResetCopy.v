(** The actual floor snap is followed by a display copy of the NEW height.
    This rules out retaining the OLD display at that reset checkpoint, not
    every later writer or every complete no-A history. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyEntry InkCopyCaller InkFloorResetSource
  InkFloorResetExecution ObjectContactNecessity SecretContactExecution
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma ifrc_graphics_position_value : forall version e le m ob oo answer,
  le ! IFR._marioObj = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    ifr_graphics_position answer -> answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)).
Proof.
  intros version e le m ob oo answer Hobject Hread.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & Hpos).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ifr_object v -> v = Vptr ob oo) as Hobj
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m (Efield ifr_object IFR._header (Tstruct IFR._ObjectNode noattr)) v ->
    v = Vptr ob oo) as Hhead.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _ ifr_object IFR._Object
      IFR._header (Tstruct IFR._ObjectNode noattr) ob oo 0 v
      eq_refl Hobj Hheader (or_intror eq_refl) Hr) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ifr_graphics v -> v = Vptr ob oo) as Hgraph.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _
      (Efield ifr_object IFR._header (Tstruct IFR._ObjectNode noattr)) IFR._ObjectNode
      IFR._gfx (Tstruct IFR._GraphNodeObject noattr) ob oo 0 v
      eq_refl Hhead Hgfx (or_intror eq_refl) Hr) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  eapply ibcc_aggregate_field with (base := ifr_graphics)
    (tag := IFR._GraphNodeObject) (field := IFR._pos) (ty := tarray tfloat 3)
    (delta := 32); eauto; reflexivity.
Qed.

Lemma ifrc_copy_arguments : forall version e le m mb mo ob oo args,
  le ! IFR._m = Some (Vptr mb mo) ->
  le ! IFR._marioObj = Some (Vptr ob oo) ->
  eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
    [ifr_graphics_position; ibcc_destination] [tptr tfloat; tptr tfloat] args ->
  args = [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32));
    Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))].
Proof.
  intros version e le m mb mo ob oo args Hm Hobject Hargs.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ ifr_graphics_position ?value |- _ =>
    assert (value = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)))
      by (eapply ifrc_graphics_position_value; eauto); subst value end.
  match goal with H : eval_expr _ _ _ _ ibcc_destination ?value |- _ =>
    assert (value = Vptr mb (Ptrofs.add mo (Ptrofs.repr 60)))
      by (eapply ifr_state_position_value; eauto); subst value end.
  repeat match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst; clear H end.
  reflexivity.
Qed.

Lemma ifrc_copy_calls_real_body : forall version kind e le m t le' m' out,
  e ! IFR._vec3f_copy = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifr_copy_call version kind) t le' m' out ->
  exists args result,
    eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
      [ifr_graphics_position; ibcc_destination] [tptr tfloat; tptr tfloat] args /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ibk_copy_body version)) args t m' result /\
    le' = le /\ out = Out_normal.
Proof.
  intros version kind e le m t le' m' out Hlocal Hrun.
  destruct (ibk_selected_copy_resolves version) as (b & Hsymbol & Hfunction).
  destruct (ifr_source_cuts version kind) as (_ & _ & _ & _ & Hcall).
  rewrite Hcall in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hexpr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  eauto 8.
Qed.

Definition ifrc_reset_witness version kind e le m mb mo ob oo height t le' m' out : Prop :=
  exists snap_m copy_e entry_le entry_m y_le y_m after_le after_m
    body_le body_m body_out copy_result copy_memory copy_pre copy_suf suffix_trace,
    t = (copy_pre ++ copy_suf) ++ suffix_trace /\
    Mem.store Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64)))
      (Vsingle height) = Some snap_m /\
    (forall chunk offset, Mem.load chunk snap_m ob offset = Mem.load chunk m ob offset) /\
    function_entry2 (Clight.globalenv (selected_clight_target version))
      (ibk_copy_body version)
      [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)); Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))]
      snap_m copy_e entry_le entry_m /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) copy_e entry_le entry_m
      (ocn_prepend (ibk_copy_before_y version) Sskip) copy_pre y_le y_m Out_normal /\
    eval_expr (Clight.globalenv (selected_clight_target version)) copy_e y_le y_m
      (Evar IBV._dest (tptr tfloat)) (Vptr ob (Ptrofs.add oo (Ptrofs.repr 32))) /\
    eval_expr (Clight.globalenv (selected_clight_target version)) copy_e
      (PTree.set IBV._t'3 (Vptr ob (Ptrofs.add oo (Ptrofs.repr 32))) y_le) y_m
      ibk_source_y (Vsingle height) /\
    Mem.store Mfloat32 y_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36)))
      (Vsingle height) = Some after_m /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) copy_e
      (PTree.set IBV._t'4 (Vsingle height)
        (PTree.set IBV._t'3 (Vptr ob (Ptrofs.add oo (Ptrofs.repr 32))) y_le)) y_m
      ibk_y_store E0 after_le after_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) copy_e after_le after_m
      (ibk_copy_after_y version) copy_suf body_le body_m body_out /\
    outcome_result_value body_out (fn_return (ibk_copy_body version)) copy_result body_m /\
    Mem.free_list body_m (blocks_of_env (Clight.globalenv (selected_clight_target version)) copy_e) =
      Some copy_memory /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e
      (PTree.set (ifr_floor_temp kind) (Vsingle height) le) copy_memory
      (ifr_after_copy version kind) suffix_trace le' m' out.

Definition InkFloorResetHeightCut : Prop :=
  forall version kind e le m mb mo ob oo height t le' m' out,
  e ! IFR._vec3f_copy = None ->
  mb <> ob -> Mem.valid_block m ob ->
  le ! IFR._m = Some (Vptr mb mo) ->
  le ! IFR._marioObj = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 112))) =
    Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifr_reset_tail version kind) t le' m' out ->
  ifrc_reset_witness version kind e le m mb mo ob oo height t le' m' out.

(** No bound on how far the floor snap lowers State is inserted. At the
    reset checkpoint the display receives that same new height. The State
    store itself preserves ALL loads in the distinct collision/display
    object allocation; changing State alone is not a raw-Object lowering. *)
Theorem ifrc_floor_snap_resets_display_to_new_height : InkFloorResetHeightCut.
Proof.
  unfold InkFloorResetHeightCut, ifrc_reset_witness.
  intros version kind e le m mb mo ob oo height t le' m' out
    Hlocal Hdifferent Hvalid Hm Hobject Hfloor Hrun.
  destruct (ifr_source_cuts version kind) as (_ & _ & Htail & _).
  destruct (ifr_prefix_properties version kind) as (_ & _ & _ & HsnapNormal & HcopyNormal & _).
  rewrite Htail in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HsnapNormal Hrun)
    as (snap_le & snap_m & snap_t & rest_t & Htrace & Hsnap & Hrest).
  destruct (ifr_snap_writes_floor_height _ _ _ _ _ _ _ _ _ _ _ _ Hm Hfloor Hsnap)
    as (HsnapStore & -> & -> & _).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HcopyNormal Hrest)
    as (copy_le & copy_memory & copy_trace & suffix_trace & HrestTrace & Hcopy & Hsuffix).
  destruct (ifrc_copy_calls_real_body _ _ _ _ _ _ _ _ _ Hlocal Hcopy)
    as (args & result & Hargs & Hcall & -> & _).
  assert ((PTree.set (ifr_floor_temp kind) (Vsingle height) le) ! IFR._m = Some (Vptr mb mo))
    as HmNow by (rewrite PTree.gso; [exact Hm|destruct kind; discriminate]).
  assert ((PTree.set (ifr_floor_temp kind) (Vsingle height) le) ! IFR._marioObj = Some (Vptr ob oo))
    as HobjectNow by (rewrite PTree.gso; [exact Hobject|destruct kind; discriminate]).
  pose proof (ifrc_copy_arguments _ _ _ _ _ _ _ _ _ HmNow HobjectNow Hargs) as Hvalues.
  subst args.
  assert (Mem.load Mfloat32 snap_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) =
    Some (Vsingle height)) as HnewY by (exact (Mem.load_store_same _ _ _ _ _ _ HsnapStore)).
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ HnewY) as HsourceValid.
  assert (Mem.valid_block snap_m ob) as HdestValid by (eapply Mem.store_valid_block_1; eauto).
  assert (ob <> mb) as Hreverse by congruence.
  inversion Hcall; subst.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _
    (fn_body (ibk_copy_body version)) _ _ _ _ |- _ =>
    destruct (ibk_copy_body_has_ordered_y_predecessor _ _ _ _ _ _ _ _ _ Hbody)
      as (y_le & y_m & after_le & after_m & destination & value & copy_pre & store & copy_suf &
        HcopyTrace & Hprefix & HdestRead & HsourceRead & Hstore & HcopySuffix) end.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_entry_and_prefix_preserve_source_y _ _ _ _ _ _ _ _ _ _ _ _ _
      Hreverse HdestValid HsourceValid Hentry Hprefix)
      as (_ & Hsource & HsourceFrame & local & HlocalBinding & HlocalRead) end.
  assert (destination = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)))
    by (eapply ibc_pointer_local_read; eauto). subst destination.
  assert ((PTree.set IBV._t'3 (Vptr ob (Ptrofs.add oo (Ptrofs.repr 32))) y_le) ! IBV._src =
    Some (Vptr mb (Ptrofs.add mo (Ptrofs.repr 60)))) as HsourceNow
    by (rewrite PTree.gso by discriminate; exact Hsource).
  pose proof (ibc_float_read _ _ _ _ _ _ _ _ _ HsourceNow HsourceRead) as HentryRead.
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1)))
    with (Ptrofs.repr 4) in HentryRead.
  rewrite HsourceFrame in HentryRead.
  rewrite Ptrofs.add_assoc in HentryRead.
  change (Ptrofs.add (Ptrofs.repr 60) (Ptrofs.repr 4)) with (Ptrofs.repr 64) in HentryRead.
  assert (value = Vsingle height) by congruence. subst value.
  pose proof Hstore as HactualStore.
  destruct (ibk_y_store_preserves_the_read_single _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) Hstore) as (block & offset & Hlocation & Hwrite & -> & _).
  match type of Hlocation with eval_lvalue _ _ ?temps _ _ _ _ _ =>
    assert (temps ! IBV._t'3 = Some (Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)))) as Hdest
      by (rewrite PTree.gso by discriminate; apply PTree.gss) end.
  destruct (ibc_index_location _ _ _ _ _ _ _ _ _ _ _ Hdest Hlocation) as (-> & -> & _).
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1)))
    with (Ptrofs.repr 4) in Hwrite.
  rewrite Ptrofs.add_assoc in Hwrite.
  change (Ptrofs.add (Ptrofs.repr 32) (Ptrofs.repr 4)) with (Ptrofs.repr 36) in Hwrite.
  exists snap_m. do 12 eexists. exists copy_pre, copy_suf, suffix_trace.
  split.
  - rewrite HcopyTrace. reflexivity.
  - split; [exact HsnapStore|]. split.
    + intros. eapply Mem.load_store_other; [exact HsnapStore|left; congruence].
    + repeat match goal with |- _ /\ _ => split; [eassumption|] end.
      eassumption.
Qed.

(** Connect the full stop-and-snap call to the memory-linked reset witness.
    The actual floor read at the reached cut remains visible: no earlier
    helper's memory effect, nor a particular numerical floor, is assumed. *)
Definition InkStopCallResetCut : Prop :=
  forall version m mb mo ob oo t m' result,
  mb <> ob ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) =
    Some (Vptr ob oo) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifr_body version IFRStop)) [Vptr mb mo] t m' result ->
  exists le cut_m final_le pre suf out,
    t = pre ++ suf /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le cut_m
      (ifr_reset_tail version IFRStop) suf final_le m' out /\
    (forall height, Mem.valid_block cut_m ob ->
      Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 112))) =
        Some (Vsingle height) ->
      ifrc_reset_witness version IFRStop empty_env le cut_m mb mo ob oo height suf final_le m' out).

Theorem ifrc_completed_stop_call_reaches_reset : InkStopCallResetCut.
Proof.
  unfold InkStopCallResetCut.
  intros version m mb mo ob oo t m' result Hseparate Hobject Hcall.
  destruct (ifr_actual_call_remembers_entry_object _ _ _ _ _ _ _ _ _ _ Hobject Hcall)
    as (le & cut_m & final_le & pre & suf & out & Htrace & Hm & Hobj & Hrun).
  exists le, cut_m, final_le, pre, suf, out. split; [exact Htrace|].
  split; [exact Hrun|]. intros height Hvalid Hfloor.
  eapply ifrc_floor_snap_resets_display_to_new_height; eauto.
Qed.

(** The same backward cut for a complete stationary call retains the real
    moving-ground choice. Only its actual false branch is a floor reset. *)
Definition InkStationaryCallResetCut : Prop :=
  forall version m mb mo ob oo t m' result,
  mb <> ob ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) =
    Some (Vptr ob oo) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ifr_body version IFRStationary)) [Vptr mb mo] t m' result ->
  exists le cut_m final_le pre branch_trace return_trace moving branch_le branch_m out,
    t = pre ++ (branch_trace ++ return_trace) /\
    ocn_test_value (Clight.globalenv (selected_clight_target version)) empty_env le cut_m
      (Etempvar IFR._takeStep tuint) moving /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le cut_m
      (if moving then ifr_moving_branch version else ifr_reset_tail version IFRStationary)
      branch_trace branch_le branch_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env branch_le branch_m
      (Sreturn (Some (Etempvar IFR._stepResult tuint))) return_trace final_le m' out /\
    (moving = false -> forall height, Mem.valid_block cut_m ob ->
      Mem.load Mfloat32 cut_m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 112))) =
        Some (Vsingle height) ->
      ifrc_reset_witness version IFRStationary empty_env le cut_m mb mo ob oo height
        branch_trace branch_le branch_m Out_normal).

Theorem ifrc_completed_stationary_call_retains_choice : InkStationaryCallResetCut.
Proof.
  unfold InkStationaryCallResetCut.
  intros version m mb mo ob oo t m' result Hseparate Hobject Hcall.
  destruct (ifr_actual_call_remembers_entry_object _ _ _ _ _ _ _ _ _ _ Hobject Hcall)
    as (le & cut_m & final_le & pre & suf & out & Htrace & Hm & Hobj & Hrun).
  destruct (ifr_actual_stationary_choice _ _ _ _ _ _ _ _ Hrun)
    as (moving & branch_le & branch_m & branch_trace & return_trace &
      Hsuffix & Htest & Hbranch & Hreturn).
  exists le, cut_m, final_le, pre, branch_trace, return_trace,
    moving, branch_le, branch_m, out.
  split; [rewrite Hsuffix in Htrace; exact Htrace|].
  split; [exact Htest|]. split; [exact Hbranch|]. split; [exact Hreturn|].
  intros -> height Hvalid Hfloor.
  eapply ifrc_floor_snap_resets_display_to_new_height; eauto.
Qed.

Definition InkFloorResetCheckedBoundary : Prop :=
  (forall version kind, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      (ifr_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ifr_body version kind))) /\
  InkBackwardCallerBoundary /\ InkFloorResetObjectPrelude /\
  InkFloorResetHeightCut /\ InkStopCallResetCut /\ InkStationaryCallResetCut.

Theorem ifrc_floor_reset_boundary_checked : InkFloorResetCheckedBoundary.
Proof.
  split; [exact ifr_selected_bodies_resolve|].
  split; [exact ibcc_backward_caller_boundary_checked|].
  split; [exact ifr_actual_call_remembers_entry_object|].
  split; [exact ifrc_floor_snap_resets_display_to_new_height|].
  split; [exact ifrc_completed_stop_call_reaches_reset|].
  exact ifrc_completed_stationary_call_retains_choice.
Qed.
