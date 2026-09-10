(** Construct the first action-pass write, including all four nested
    graphical-record selections, from normal readable/writable storage. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkCopyCaller InkActionPassStart InkActionVisibilityFrame InkBodyResetConstruction
  ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma ivc_zero_aggregate : forall (ge : genv) e le m base tag member ty b ofs,
  typeof base = Tstruct tag noattr -> access_mode ty = By_copy ->
  ibcc_field_ok ge tag member 0 = true ->
  eval_expr ge e le m base (Vptr b ofs) ->
  eval_expr ge e le m (Efield base member ty) (Vptr b ofs).
Proof.
  intros ge e le m base tag member ty b ofs Htype Hmode Hfield Hbase.
  destruct (ibcc_field_ok_sound _ _ _ _ Hfield) as (co & Hco & Hoff).
  eapply eval_Elvalue with (ofs := ofs) (bf := Full).
  - replace ofs with (Ptrofs.add ofs (Ptrofs.repr 0))
      by (change (Ptrofs.add ofs Ptrofs.zero = ofs); apply Ptrofs.add_zero).
    eapply eval_Efield_struct; eauto.
  - apply deref_loc_copy. exact Hmode.
Qed.

Lemma ivc_node_read : forall version e le m temp pool ofs,
  le ! temp = Some (Vptr pool ofs) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (iav_node temp) (Vptr pool ofs).
Proof.
  intros version e le m temp pool ofs Htemp.
  destruct (iav_layout version) as (Hheader & Hgfx & Hnode & Hflags).
  unfold iav_node. eapply ivc_zero_aggregate; [reflexivity|reflexivity|exact Hnode|].
  unfold iav_gfx. eapply ivc_zero_aggregate; [reflexivity|reflexivity|exact Hgfx|].
  unfold iav_header. eapply ivc_zero_aggregate; [reflexivity|reflexivity|exact Hheader|].
  unfold iav_object. eapply eval_Elvalue.
  - apply eval_Ederef. apply eval_Etempvar. exact Htemp.
  - apply deref_loc_copy. reflexivity.
Qed.

Lemma ivc_flags_lvalue : forall version e le m temp pool ofs,
  le ! temp = Some (Vptr pool ofs) ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (iav_flags temp) pool (Ptrofs.add ofs (Ptrofs.repr 2)) Full.
Proof.
  intros version e le m temp pool ofs Htemp.
  destruct (ibcc_field_ok_sound _ _ _ _ (proj2 (proj2 (proj2 (iav_layout version)))))
    as (co & Hco & Hoff).
  unfold iav_flags. eapply eval_Efield_struct with (co := co).
  - apply ivc_node_read. exact Htemp.
  - reflexivity.
  - exact Hco.
  - exact Hoff.
Qed.

Definition ivc_word flags := Int.and flags (Int.not (Int.shl (Int.repr 1) (Int.repr 4))).
Definition ivc_after_temps version le flags := PTree.set (iav_read_temp version) (Vint flags) le.

Lemma ivc_rhs_source : forall version,
  iav_write_rhs version = Ebinop Oand (Etempvar (iav_read_temp version) tshort)
    (Eunop Onotint (Ebinop Oshl (Econst_int (Int.repr 1) tint)
      (Econst_int (Int.repr 4) tint) tint) tint) tint.
Proof. intros []; reflexivity. Qed.

Theorem ivc_construct_visibility : forall version e le m pool ofs flags,
  le ! (ias_o1 version) = Some (Vptr pool ofs) ->
  le ! (ias_o2 version) = Some (Vptr pool ofs) ->
  Mem.load Mint16signed m pool (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 2))) =
    Some (Vint flags) ->
  Mem.valid_access m Mint16signed pool
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 2))) Writable ->
  exists after,
    Mem.store Mint16signed m pool (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 2)))
      (Vint (Int.sign_ext 16 (ivc_word flags))) = Some after /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ias_flag_frontier version) E0 (ivc_after_temps version le flags) after Out_normal.
Proof.
  intros version e le m pool ofs flags Ho1 Ho2 Hflags Haccess.
  destruct (Mem.valid_access_store m Mint16signed pool
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 2)))
    (Vint (Int.sign_ext 16 (ivc_word flags))) Haccess) as (after & Hstore).
  exists after. split; [exact Hstore|]. rewrite iav_source. unfold ivc_after_temps.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_Sset. eapply eval_Elvalue.
    + apply ivc_flags_lvalue. exact Ho2.
    + eapply deref_loc_value with (chunk := Mint16signed); [reflexivity|exact Hflags].
  - eapply exec_Sassign with (v2 := Vint (ivc_word flags))
      (v := Vint (Int.sign_ext 16 (ivc_word flags))) (bf := Full).
    + apply ivc_flags_lvalue. rewrite PTree.gso; [exact Ho1|destruct version; discriminate].
    + rewrite ivc_rhs_source. eapply eval_Ebinop.
      * apply eval_Etempvar. apply PTree.gss.
      * eapply eval_Eunop.
        -- eapply eval_Ebinop; [constructor|constructor|reflexivity].
        -- reflexivity.
      * reflexivity.
    + rewrite ivc_rhs_source. reflexivity.
    + eapply assign_loc_value with (chunk := Mint16signed); [reflexivity|exact Hstore].
Qed.
