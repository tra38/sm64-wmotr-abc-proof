(** Construct the real body-reset call from its concrete reads and writable
    cells.  No completed call or protected-memory effect is assumed. *)
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkCopyCaller InkActionPassHistory InkBodyResetFrame ObjectContactNecessity
  SelectedClightTarget InkSharedReadings OrdinaryArea1EntryMemory.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma ibc_field_lvalue : forall (ge : genv) e le m temp tag field ty delta b,
  le ! temp = Some (Vptr b Ptrofs.zero) ->
  ibcc_field_ok ge tag field delta = true ->
  eval_lvalue ge e le m (ibr_field temp tag field ty) b (Ptrofs.repr delta) Full.
Proof.
  intros ge e le m temp tag field ty delta b Htemp Hfield.
  destruct (ibcc_field_ok_sound _ _ _ _ Hfield) as (co & Hco & Hoff).
  rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  unfold ibr_field, ibr_base. eapply eval_Efield_struct with (co := co).
  - eapply eval_Elvalue; [apply eval_Ederef; apply eval_Etempvar; exact Htemp|].
    apply deref_loc_copy. reflexivity.
  - reflexivity.
  - exact Hco.
  - exact Hoff.
Qed.

Lemma ibc_field_read : forall (ge : genv) e le m temp tag field ty delta chunk b v,
  le ! temp = Some (Vptr b Ptrofs.zero) ->
  ibcc_field_ok ge tag field delta = true -> access_mode ty = By_value chunk ->
  Mem.load chunk m b (Ptrofs.unsigned (Ptrofs.repr delta)) = Some v ->
  eval_expr ge e le m (ibr_field temp tag field ty) v.
Proof.
  intros. eapply eval_Elvalue; [eapply ibc_field_lvalue; eauto|].
  eapply deref_loc_value; eauto.
Qed.

Definition ibc_cast_ok spec := forall m,
  sem_cast (Vint (Int.repr (ibr_constant spec))) tint (ibr_type spec) m =
    Some (Vint (Int.repr (ibr_constant spec))).
Definition ibc_access m body spec := Mem.valid_access m (ibr_chunk spec) body
  (Ptrofs.unsigned (Ptrofs.repr (ibr_delta spec))) Writable.

Lemma ibc_store_casts : Forall ibc_cast_ok ibr_stores.
Proof. repeat constructor; intro m; reflexivity. Qed.

Lemma ibc_construct_body_stores : forall (ge : genv) e specs le m body,
  Forall (fun spec => ibr_layout_check ge spec = true) specs ->
  Forall (fun spec => access_mode (ibr_type spec) = By_value (ibr_chunk spec)) specs ->
  Forall ibc_cast_ok specs -> Forall (ibc_access m body) specs ->
  le ! IBM._bodyState = Some (Vptr body Ptrofs.zero) ->
  exists after,
    iap_stage_chain ge e le m (map ibr_store_statement specs) E0 le after /\
    (forall chunk b offset permission, Mem.valid_access m chunk b offset permission ->
      Mem.valid_access after chunk b offset permission).
Proof.
  intros ge e specs. induction specs as [|spec specs IH];
    intros le m body Hlayout Hmode Hcasts Haccess Hbody.
  - exists m. split; [constructor|auto].
  - inversion Hlayout; subst. inversion Hmode; subst.
    inversion Hcasts; subst. inversion Haccess; subst.
    destruct (Mem.valid_access_store m (ibr_chunk spec) body
      (Ptrofs.unsigned (Ptrofs.repr (ibr_delta spec)))
      (Vint (Int.repr (ibr_constant spec))) ltac:(assumption)) as [middle Hstore].
    assert (Forall (ibc_access middle body) specs) as Haccess'.
    { eapply Forall_impl; [|eassumption]. intros item Hitem.
      unfold ibc_access in *. eapply Mem.store_valid_access_1; eauto. }
    destruct (IH le middle body ltac:(assumption) ltac:(assumption)
      ltac:(assumption) Haccess' Hbody) as (after & Hchain & Hvalid).
    exists after. split.
    + eapply iap_chain_cons with (t1 := E0) (t2 := E0); [|exact Hchain].
      unfold ibr_store_statement.
      eapply exec_Sassign with (v2 := Vint (Int.repr (ibr_constant spec)))
        (v := Vint (Int.repr (ibr_constant spec))) (bf := Full).
      * eapply ibc_field_lvalue; eauto.
      * constructor.
      * change (sem_cast (Vint (Int.repr (ibr_constant spec))) tint (ibr_type spec) m =
          Some (Vint (Int.repr (ibr_constant spec)))).
        match goal with Hcast : ibc_cast_ok spec |- _ => exact (Hcast m) end.
      * eapply assign_loc_value; eauto.
    + intros. apply Hvalid. eapply Mem.store_valid_access_1; eauto.
Qed.

Lemma ibc_chain_then_tail : forall (ge : genv) e le m items t mid memory,
  iap_stage_chain ge e le m items t mid memory ->
  forall tail u last after out,
  ocn_exec ge e mid memory tail u last after out ->
  ocn_exec ge e le m (ocn_prepend items tail) (t ++ u) last after out.
Proof.
  intros ge e le m items t mid memory Hchain.
  induction Hchain; intros tail u last after out Htail.
  - exact Htail.
  - cbn [ocn_prepend]. rewrite <- app_assoc.
    eapply exec_Sseq_1 with (t1 := t1) (t2 := t2 ++ u).
    + exact H.
    + apply IHHchain. exact Htail.
Qed.

Definition ibc_entry_temps version mb :=
  PTree.set IBM._m (Vptr mb Ptrofs.zero)
    (create_undef_temps (fn_temps (ibr_body version))).

Lemma ibc_real_entry : forall version m mb,
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (ibr_body version) [Vptr mb Ptrofs.zero] m empty_env (ibc_entry_temps version mb) m.
Proof.
  intros. constructor.
  - destruct version; constructor.
  - destruct version; repeat constructor; cbn; tauto.
  - destruct version; vm_compute; intuition congruence.
  - destruct version; apply alloc_variables_nil.
  - destruct version; reflexivity.
Qed.

(** These are initial/live READ AND PERMISSION facts, not assumptions about
    the helper's execution or effect.  At later calls they must be derived
    from the preceding history, rather than granted anew. *)
Record InkBodyResetStorage m mb body : Prop := {
  ibc_body_reference : Mem.load Mint32 m mb 152 = Some (Vptr body Ptrofs.zero);
  ibc_body_is_separate : body <> mb;
  ibc_flags_integer : exists flags, Mem.load Mint32 m mb 4 = Some (Vint flags);
  ibc_flags_writable : Mem.valid_access m Mint32 mb 4 Writable;
  ibc_body_writable : Forall (ibc_access m body) ibr_stores
}.

Theorem ibc_construct_complete_reset : forall version m mb body,
  InkBodyResetStorage m mb body ->
  exists after,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ibr_body version)) [Vptr mb Ptrofs.zero] E0 after Vundef /\
    (forall chunk b offset permission, Mem.valid_access m chunk b offset permission ->
      Mem.valid_access after chunk b offset permission) /\
    exists flags, Mem.load Mint32 after mb 4 = Some (Vint flags).
Proof.
  intros version m mb body [Hbody Hseparate [flags Hflags] Hflagaccess Hbodyaccess].
  destruct (ibr_selected_layout version) as (Hbodylayout & Hflaglayout & Hlayouts).
  assert (Forall (fun spec => ibr_layout_check
    (Clight.globalenv (selected_clight_target version)) spec = true) ibr_stores) as Hlayout.
  { apply Forall_forall. intros x Hx. rewrite forallb_forall in Hlayouts. exact (Hlayouts x Hx). }
  set (read_le := PTree.set IBM._bodyState (Vptr body Ptrofs.zero) (ibc_entry_temps version mb)).
  destruct (ibc_construct_body_stores _ empty_env ibr_stores read_le m body
    Hlayout ibr_store_modes ibc_store_casts Hbodyaccess ltac:(apply PTree.gss))
    as (middle & Hchain & Hvalid).
  assert (Mem.load Mint32 middle mb 4 = Some (Vint flags)) as Hflags'.
  { destruct (ibr_store_chain_frames _ empty_env ibr_stores read_le m E0 read_le middle
      body Ptrofs.zero Hlayout ibr_store_modes ltac:(apply PTree.gss) Hchain)
      as (_ & _ & Hframe).
    change (ink_read middle {| ink_cell_block := mb; ink_cell_chunk := Mint32;
      ink_cell_offset := 4 |} = Some (Vint flags)).
    rewrite (Hframe {| ink_cell_block := mb; ink_cell_chunk := Mint32; ink_cell_offset := 4 |}).
    - exact Hflags.
    - apply Forall_forall. intros. unfold ibr_body_disjoint, ibr_cell_disjoint. left. cbn. congruence. }
  destruct (Mem.valid_access_store middle Mint32 mb 4
    (Vint (Int.and flags (Int.not (Int.repr 64)))) (Hvalid _ _ _ _ Hflagaccess))
    as (after & Hflagstore).
  assert (ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env read_le middle
    ibr_flag_tail E0 (PTree.set IBM._t'1 (Vint flags) read_le) after Out_normal) as Htail.
  { unfold ibr_flag_tail. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    - apply exec_Sset. eapply ibc_field_read with (delta := 4) (chunk := Mint32).
      + unfold read_le, ibc_entry_temps. rewrite PTree.gso by discriminate. apply PTree.gss.
      + exact Hflaglayout.
      + reflexivity.
      + exact Hflags'.
    - eapply exec_Sassign with (v2 := Vint (Int.and flags (Int.not (Int.repr 64))))
        (v := Vint (Int.and flags (Int.not (Int.repr 64)))) (bf := Full).
      + eapply ibc_field_lvalue; [|exact Hflaglayout].
        unfold read_le, ibc_entry_temps. repeat rewrite PTree.gso by discriminate. apply PTree.gss.
      + eapply eval_Ebinop.
        * apply eval_Etempvar. apply PTree.gss.
        * eapply eval_Eunop; [constructor|reflexivity].
        * reflexivity.
      + reflexivity.
      + eapply assign_loc_value with (chunk := Mint32); [reflexivity|exact Hflagstore]. }
  exists after. split.
  - eapply eval_funcall_internal.
    + apply ibc_real_entry.
    + rewrite (proj1 (proj2 (proj2 (ibr_source version)))).
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply ibc_field_read with (delta := 152) (chunk := Mint32).
        -- apply PTree.gss.
        -- exact Hbodylayout.
        -- reflexivity.
        -- exact Hbody.
      * exact (ibc_chain_then_tail _ _ _ _ _ _ _ _ Hchain _ _ _ _ _ Htail).
    + destruct version; reflexivity.
    + reflexivity.
  - split.
    + intros. eapply Mem.store_valid_access_1; [exact Hflagstore|]. apply Hvalid. assumption.
    + exists (Int.and flags (Int.not (Int.repr 64))).
      rewrite (Mem.load_store_same _ _ _ _ _ _ Hflagstore). reflexivity.
Qed.

Theorem ibc_construct_reset_and_shared_frame : forall version m a body,
  InkBodyResetStorage m (area1_state_storage_block a) body ->
  area1_state_storage_block a <> area1_object_pool_block a ->
  body <> area1_object_pool_block a ->
  exists after,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ibr_body version)) [Vptr (area1_state_storage_block a) Ptrofs.zero]
      E0 after Vundef /\ InkSameReadings a m after.
Proof.
  intros version m a body Hstorage Hstatepool Hbodypool.
  destruct (ibc_construct_complete_reset version m _ body Hstorage) as (after & Hcall & _).
  exists after. split; [exact Hcall|].
  eapply (proj2 (ibr_completed_reset_preserves_shared_readings version m a body
    Ptrofs.zero E0 after Vundef Hstatepool (ibc_body_is_separate _ _ _ Hstorage)
    Hbodypool (ibc_body_reference _ _ _ Hstorage) Hcall)).
Qed.
