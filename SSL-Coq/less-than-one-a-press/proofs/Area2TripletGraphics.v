(** The entire generated graphics-update helper preserves the object's raw
    fields. In particular it cannot move the inactive triplet parent, make
    it tangible, enable movement flags, or change its spawning action. *)
From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_behavior_script jp_behavior_script.
From LessThanOneAPress.Proofs Require Import GameTypes InkCopyCaller
  EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module TG := us_behavior_script.

Inductive TripletGraphicsCell := GfxX | GfxY | GfxZ | GfxPitch | GfxYaw | GfxRoll.
Definition tg_element c := match c with GfxX | GfxY | GfxZ => tfloat | _ => tshort end.
Definition tg_field c := match c with GfxX | GfxY | GfxZ => TG._pos | _ => TG._angle end.
Definition tg_base c := match c with GfxX | GfxY | GfxZ => 32 | _ => 26 end.
Definition tg_index c := match c with GfxX | GfxPitch => 0 | GfxY | GfxYaw => 1 | _ => 2 end.
Definition tg_offset c := match c with
| GfxX => 32 | GfxY => 36 | GfxZ => 40
| GfxPitch => 26 | GfxYaw => 28 | GfxRoll => 30 end.
Definition tg_object := Ederef (Etempvar TG._obj (tptr (Tstruct TG._Object noattr)))
  (Tstruct TG._Object noattr).
Definition tg_header := Efield tg_object TG._header (Tstruct TG._ObjectNode noattr).
Definition tg_graphics := Efield tg_header TG._gfx (Tstruct TG._GraphNodeObject noattr).
Definition tg_array c := Efield tg_graphics (tg_field c) (tarray (tg_element c) 3).
Definition tg_lhs c := Ederef (Ebinop Oadd (tg_array c)
  (Econst_int (Int.repr (tg_index c)) tint) (tptr (tg_element c))) (tg_element c).
Definition tg_body version := match version with
| VersionUS => us_behavior_script.f_obj_update_gfx_pos_and_angle
| VersionJP => jp_behavior_script.f_obj_update_gfx_pos_and_angle end.

Inductive tg_code : statement -> Prop :=
| tg_set : forall id a, id <> TG._obj -> tg_code (Sset id a)
| tg_store : forall c a, tg_code (Sassign (tg_lhs c) a)
| tg_seq : forall a b, tg_code a -> tg_code b -> tg_code (Ssequence a b).

Ltac tg_check_code :=
  lazymatch goal with
  | |- tg_code (Ssequence _ _) => apply tg_seq; tg_check_code
  | |- tg_code (Sset _ _) => apply tg_set; discriminate
  | |- tg_code (Sassign _ ?a) => first
      [exact (tg_store GfxX a) | exact (tg_store GfxY a) | exact (tg_store GfxZ a)
      |exact (tg_store GfxPitch a) |exact (tg_store GfxYaw a) |exact (tg_store GfxRoll a)]
  end.
Theorem tg_complete_generated_body : forall version, tg_code (fn_body (tg_body version)).
Proof.
  intros []; unfold tg_body;
    cbn [us_behavior_script.f_obj_update_gfx_pos_and_angle
      jp_behavior_script.f_obj_update_gfx_pos_and_angle fn_body]; tg_check_code.
Qed.

Lemma tg_selected_array_layout : forall version c,
  ibcc_field_ok (prog_comp_env (selected_clight_target version))
    TG._GraphNodeObject (tg_field c) (tg_base c) = true.
Proof.
  intros version c. rewrite <- rank15_selected_header_environment_exact.
  destruct version, c; vm_compute; reflexivity.
Qed.

Lemma tg_array_read : forall version c e le m ob oo answer,
  le ! TG._obj = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (tg_array c) answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr (tg_base c))).
Proof.
  intros version c e le m ob oo answer Hobj Hread.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & _).
  assert (forall value, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m tg_object value -> value = Vptr ob oo) as Hobject
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall value, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m tg_header value -> value = Vptr ob oo) as Hhead.
  { intros value H. pose proof (ibcc_aggregate_field _ _ _ _ tg_object TG._Object
      TG._header (Tstruct TG._ObjectNode noattr) ob oo 0 value eq_refl Hobject
      Hheader (or_intror eq_refl) H) as E. rewrite Ptrofs.add_zero in E. exact E. }
  assert (forall value, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m tg_graphics value -> value = Vptr ob oo) as Hgraph.
  { intros value H. pose proof (ibcc_aggregate_field _ _ _ _ tg_header TG._ObjectNode
      TG._gfx (Tstruct TG._GraphNodeObject noattr) ob oo 0 value eq_refl Hhead
      Hgfx (or_intror eq_refl) H) as E. rewrite Ptrofs.add_zero in E. exact E. }
  eapply ibcc_aggregate_field with (base := tg_graphics) (tag := TG._GraphNodeObject)
    (field := tg_field c) (ty := tarray (tg_element c) 3).
  - reflexivity.
  - exact Hgraph.
  - exact (tg_selected_array_layout version c).
  - left. reflexivity.
  - exact Hread.
Qed.

Lemma tg_store_location : forall version c e le m ob oo b ofs bf,
  le ! TG._obj = Some (Vptr ob oo) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (tg_lhs c) b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr (tg_offset c)) /\ bf = Full.
Proof.
  intros version c e le m ob oo b ofs bf Hobj Hlhs.
  unfold tg_lhs in Hlhs. inversion Hlhs; subst.
  match goal with H : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion H; subst; clear H end.
  all: try solve [match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end].
  match goal with H : eval_expr _ _ _ _ (tg_array c) _ |- _ =>
    apply (tg_array_read version c e le m ob oo _ Hobj) in H; subst end.
  match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    inversion H; subst; clear H end.
  all: try solve [match goal with H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H end].
  match goal with H : sem_binary_operation _ Oadd _ _ _ _ _ = Some _ |- _ =>
    rename H into Hsem end.
  destruct c; cbn in Hsem; inversion Hsem; subst;
    rewrite ?Ptrofs.add_zero, ?Ptrofs.add_assoc; repeat split; reflexivity.
Qed.

Definition tg_raw_frame ob oo before after := forall chunk index,
  0 <= index ->
  Mem.load chunk after ob (Ptrofs.unsigned oo + 136 + 4 * index) =
  Mem.load chunk before ob (Ptrofs.unsigned oo + 136 + 4 * index).

Lemma tg_plain_offset : forall oo c,
  Ptrofs.unsigned oo + 608 <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (tg_offset c))) =
    Ptrofs.unsigned oo + tg_offset c.
Proof.
  intros oo c Hbound. rewrite Ptrofs.add_unsigned.
  rewrite (Ptrofs.unsigned_repr (tg_offset c)) by
    (destruct c; cbn [tg_offset]; change Ptrofs.max_unsigned with 4294967295; lia).
  apply Ptrofs.unsigned_repr. destruct c; cbn [tg_offset] in *;
    pose proof (Ptrofs.unsigned_range oo); lia.
Qed.

Lemma tg_code_preserves_raw : forall version s,
  tg_code s -> forall e le m ob oo trace le' m' out,
  le ! TG._obj = Some (Vptr ob oo) ->
  Ptrofs.unsigned oo + 608 <= Ptrofs.max_unsigned ->
  ClightBigstep.Clight2.exec_stmt
    (Clight.globalenv (selected_clight_target version)) e le m s trace le' m' out ->
  le' ! TG._obj = Some (Vptr ob oo) /\ tg_raw_frame ob oo m m' /\ out = Out_normal.
Proof.
  intros version s Hcode. induction Hcode;
    intros e le m ob oo trace le' m' out Hobj Hbound Hrun; inversion Hrun; subst.
  - split; [rewrite PTree.gso by congruence; exact Hobj|].
    split; [intros chunk index Hindex; reflexivity|reflexivity].
  - match goal with Hlhs : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
      destruct (tg_store_location _ _ _ _ _ _ _ _ _ _ Hobj Hlhs) as (-> & -> & ->) end.
    split; [exact Hobj|]. split; [|reflexivity]. intros chunk index Hindex.
    match goal with Hstore : assign_loc _ _ _ _ _ _ _ _ |- _ =>
      inversion Hstore; subst; try (destruct c; discriminate) end.
    lazymatch goal with Hmode : access_mode (typeof (tg_lhs c)) = By_value ?stored,
      Hstore : Mem.storev ?stored _ _ _ = Some _ |- _ =>
      pose proof (tg_plain_offset oo c Hbound) as Hoffset;
      cbn [Mem.storev] in Hstore;
      rewrite Hoffset in Hstore;
      eapply Mem.load_store_other; [exact Hstore|right; right];
      destruct c; cbn [tg_lhs tg_element typeof access_mode] in Hmode;
      inversion Hmode; subst; cbn [size_chunk tg_offset]; lia end.
  - match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ a _ _ _ Out_normal |- _ =>
      destruct (IHHcode1 _ _ _ _ _ _ _ _ _ Hobj Hbound Hfirst)
        as (Hobj1 & Hframe1 & _) end.
    match goal with Hlast : ClightBigstep.exec_stmt _ _ _ _ _ b _ _ _ _ |- _ =>
      destruct (IHHcode2 _ _ _ _ _ _ _ _ _ Hobj1 Hbound Hlast)
        as (Hobj2 & Hframe2 & Hout) end.
    split; [exact Hobj2|]. split; [|exact Hout].
    intros chunk index Hindex. rewrite Hframe2, Hframe1 by assumption. reflexivity.
  - match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ a _ _ _ _ |- _ =>
      destruct (IHHcode1 _ _ _ _ _ _ _ _ _ Hobj Hbound Hfirst)
        as (_ & _ & Hout); contradiction end.
Qed.

Definition TripletGraphicsPreservation : Prop :=
  forall version e le m ob oo trace le' m' out,
  le ! TG._obj = Some (Vptr ob oo) ->
  Ptrofs.unsigned oo + 608 <= Ptrofs.max_unsigned ->
  ClightBigstep.Clight2.exec_stmt
    (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (tg_body version)) trace le' m' out ->
  tg_raw_frame ob oo m m' /\ out = Out_normal.
Theorem tg_graphics_update_preserves_raw_fields : TripletGraphicsPreservation.
Proof.
  intros version e le m ob oo trace le' m' out Hobj Hbound Hrun.
  destruct (tg_code_preserves_raw version _ (tg_complete_generated_body version)
    _ _ _ _ _ _ _ _ _ Hobj Hbound Hrun) as (_ & Hframe & Hout). auto.
Qed.
