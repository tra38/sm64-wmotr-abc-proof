(** Actual ground-step refresh: an old display cannot supply this Y write.
    The height copied is the movement height AFTER the quarter steps. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkGroundBackwardSource
  InkBackwardSource InkBackwardExecution InkCopyEntry InkCopyCaller
  InkFloorResetSource InkFloorResetExecution ObjectContactNecessity
  ContactConsumerExecution SecretContactExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma igb_display_address : forall version e le m ob oo answer,
  le ! IFR._t'6 = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m igb_display answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)).
Proof.
  intros version e le m ob oo answer Hobject Hread.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & Hpos).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m igb_object v -> v = Vptr ob oo) as Hobj
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m (Efield igb_object IFR._header (Tstruct IFR._ObjectNode noattr)) v ->
    v = Vptr ob oo) as Hhead.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _ igb_object IFR._Object
      IFR._header (Tstruct IFR._ObjectNode noattr) ob oo 0 v
      eq_refl Hobj Hheader (or_intror eq_refl) Hr) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m igb_graphics v -> v = Vptr ob oo) as Hgraph.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _
      (Efield igb_object IFR._header (Tstruct IFR._ObjectNode noattr)) IFR._ObjectNode
      IFR._gfx (Tstruct IFR._GraphNodeObject noattr) ob oo 0 v
      eq_refl Hhead Hgfx (or_intror eq_refl) Hr) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  eapply ibcc_aggregate_field with (base := igb_graphics)
    (tag := IFR._GraphNodeObject) (field := IFR._pos) (ty := tarray tfloat 3)
    (delta := 32); eauto; reflexivity.
Qed.

Lemma igb_copy_arguments : forall version e le m mb mo ob oo args,
  le ! IFR._m = Some (Vptr mb mo) -> le ! IFR._t'6 = Some (Vptr ob oo) ->
  eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
    [igb_display; ibcc_destination] [tptr tfloat; tptr tfloat] args ->
  args = [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)); Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))].
Proof.
  intros version e le m mb mo ob oo args Hm Hobject Hargs.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ igb_display ?value |- _ =>
    assert (value = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)))
      by (eapply igb_display_address; eauto); subst value end.
  match goal with H : eval_expr _ _ _ _ ibcc_destination ?value |- _ =>
    assert (value = Vptr mb (Ptrofs.add mo (Ptrofs.repr 60)))
      by (eapply ifr_state_position_value; eauto); subst value end.
  repeat match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst; clear H end.
  reflexivity.
Qed.

Lemma igb_refresh_calls_selected_copy : forall version e le m mb mo ob oo t le' m' out,
  e ! IFR._vec3f_copy = None -> le ! IFR._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) = Some (Vptr ob oo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (igb_refresh version) t le' m' out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m (Internal (ibk_copy_body version))
    [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)); Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))]
    t m' result.
Proof.
  intros version e le m mb mo ob oo t le' m' out Hlocal Hm Hobject Hrun.
  destruct (igb_source_cuts version) as (_ & _ & _ & Hshape & _). rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IFR._t'6 ibk_object_read) _ _ _ _ _ eq_refl Hrun)
    as (copy_le & copy_m & pre & rest & Htrace & Hread & Hcopy).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?v |- _ =>
    assert (v = Vptr ob oo) by (eapply ibcc_actual_object_read; eauto); subst v end.
  destruct (ibk_selected_copy_resolves version) as (b & Hsymbol & Hfunction).
  inversion Hcopy; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hr : eval_exprlist ?ge ?env ?temps ?memory _ _ ?args |- _ =>
    assert (args = [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32));
      Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))]) as Hargs by
      (eapply (igb_copy_arguments version env temps memory mb mo ob oo);
        [rewrite PTree.gso by discriminate; exact Hm|apply PTree.gss|exact Hr]); subst args end.
  eauto.
Qed.

Definition igb_refresh_witness version m mb mo ob oo height t m' : Prop :=
  exists result copy_e y_le y_m after_le after_m pre suffix,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
      (Internal (ibk_copy_body version))
      [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)); Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))]
      t m' result /\
    t = pre ++ (E0 ++ suffix) /\
    eval_expr (Clight.globalenv (selected_clight_target version)) copy_e
      (PTree.set IBV._t'3 (Vptr ob (Ptrofs.add oo (Ptrofs.repr 32))) y_le) y_m
      ibk_source_y (Vsingle height) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) copy_e
      (PTree.set IBV._t'4 (Vsingle height)
        (PTree.set IBV._t'3 (Vptr ob (Ptrofs.add oo (Ptrofs.repr 32))) y_le)) y_m
      ibk_y_store E0 after_le after_m Out_normal /\
    Mem.store Mfloat32 y_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36)))
      (Vsingle height) = Some after_m /\
    Mem.load Mfloat32 after_m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36))) =
      Some (Vsingle height).

Definition InkGroundRefreshHeightCut : Prop :=
  forall version e le m mb mo ob oo height t le' m' out,
  e ! IFR._vec3f_copy = None -> mb <> ob -> Mem.valid_block m ob ->
  le ! IFR._m = Some (Vptr mb mo) ->
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 136))) = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 64))) = Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (igb_refresh version) t le' m' out ->
  igb_refresh_witness version m mb mo ob oo height t m'.

Theorem igb_refresh_reads_current_movement_height : InkGroundRefreshHeightCut.
Proof.
  unfold InkGroundRefreshHeightCut, igb_refresh_witness.
  intros version e le m mb mo ob oo height t le' m' out Hlocal Hseparate Hvalid Hm Hobject Hheight Hrun.
  destruct (igb_refresh_calls_selected_copy _ _ _ _ _ _ _ _ _ _ _ _ Hlocal Hm Hobject Hrun)
    as (result & Hcall).
  assert (ob <> mb) as Hreverse by congruence.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ Hheight) as HsourceValid.
  destruct (ibc_actual_copy_reads_entry_height _ _ _ _ _ _ _ _ _
    Hreverse Hvalid HsourceValid Hcall)
    as (copy_e & y_le & y_m & after_le & after_m & value & pre & store & suffix &
      Htrace & Hload & Hread & Hstore).
  rewrite Ptrofs.add_assoc in Hload.
  change (Ptrofs.add (Ptrofs.repr 60) (Ptrofs.repr 4)) with (Ptrofs.repr 64) in Hload.
  assert (value = Vsingle height) by congruence. subst value.
  pose proof Hstore as Hactual.
  destruct (ibk_y_store_preserves_the_read_single _ _ _ _ _ _ _ _ _
    (PTree.gss _ _ _) Hstore) as (b & ofs & Hlocation & Hwrite & -> & _).
  match type of Hlocation with eval_lvalue _ _ ?temps _ _ _ _ _ =>
    assert (temps ! IBV._t'3 = Some (Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)))) as Hdest
      by (rewrite PTree.gso by discriminate; apply PTree.gss) end.
  destruct (ibc_index_location _ _ _ _ _ _ _ _ _ _ _ Hdest Hlocation) as (-> & -> & _).
  change (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr 1)))
    with (Ptrofs.repr 4) in Hwrite.
  rewrite Ptrofs.add_assoc in Hwrite.
  change (Ptrofs.add (Ptrofs.repr 32) (Ptrofs.repr 4)) with (Ptrofs.repr 36) in Hwrite.
  exists result, copy_e, y_le, y_m, after_le, after_m, pre, suffix.
  repeat split; try assumption. exact (Mem.load_store_same _ _ _ _ _ _ Hwrite).
Qed.
