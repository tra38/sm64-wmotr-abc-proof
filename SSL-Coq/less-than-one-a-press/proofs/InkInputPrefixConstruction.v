(** Construct the input helper's four real initial writes, rather than
    assuming that a completed input pass exists.  All input words are reset
    before the actual button helper is reached. *)
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource InkCopyCaller
  InkActionPassHistory InkBodyResetFrame InkBodyResetConstruction InkSharedReadings
  InkControllerSource InkControllerEdge InkMarioInputReset ObjectContactNecessity
  EyerokRank15LiveMovement OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iic_particle := Sassign (ics_field IBM._m IBM._MarioState IBM._particleFlags tuint)
  (Econst_int Int.zero tint).
Definition iic_collisions := Ssequence
  (Sset IBM._t'15 (ics_field IBM._m IBM._MarioState IBM._marioObj (tptr (Tstruct IBM._Object noattr))))
  (Ssequence (Sset IBM._t'16 (ics_field IBM._t'15 IBM._Object IBM._collidedObjInteractTypes tuint))
    (Sassign (ics_field IBM._m IBM._MarioState IBM._collidedObjInteractTypes tuint)
      (Etempvar IBM._t'16 tuint))).
Definition iic_flags := Ssequence
  (Sset IBM._t'14 (ics_field IBM._m IBM._MarioState IBM._flags tuint))
  (Sassign (ics_field IBM._m IBM._MarioState IBM._flags tuint)
    (Ebinop Oand (Etempvar IBM._t'14 tuint) (Econst_int (Int.repr 16777215) tint) tuint)).
Definition iic_stages version := [iic_particle; ics_reset version; iic_collisions; iic_flags].
Definition iic_button_frontier version := Ssequence (imr_button_call version) (imr_after_buttons version).
Definition iic_ready le ob oo collided flags := PTree.set IBM._t'14 (Vint flags)
  (PTree.set IBM._t'16 (Vint collided) (PTree.set IBM._t'15 (Vptr ob oo) le)).

Lemma iic_source : forall version,
  fn_body (ics_body version ICInputs) = ocn_prepend (iic_stages version) (iic_button_frontier version).
Proof. intros []; reflexivity. Qed.

Lemma iic_layout : forall version,
  let ce := prog_comp_env (selected_clight_target version) in
  ibcc_field_ok ce IBM._MarioState IBM._particleFlags 8 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._input 2 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._marioObj 136 = true /\
  ibcc_field_ok ce IBM._Object IBM._collidedObjInteractTypes 112 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._collidedObjInteractTypes 164 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._flags 4 = true.
Proof.
  intro version. cbn zeta. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Lemma iic_field_at : forall (ge : genv) e le m temp tag member ty delta chunk b ofs v,
  le ! temp = Some (Vptr b ofs) -> ibcc_field_ok ge tag member delta = true ->
  access_mode ty = By_value chunk ->
  Mem.load chunk m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some v ->
  eval_expr ge e le m (ics_field temp tag member ty) v.
Proof.
  intros ge e le m temp tag member ty delta chunk b ofs v Htemp Hfield Hmode Hload.
  destruct (ibcc_field_ok_sound _ _ _ _ Hfield) as (co & Hco & Hoff).
  eapply eval_Elvalue.
  - unfold ics_field. eapply eval_Efield_struct with (co := co).
    + eapply eval_Elvalue; [apply eval_Ederef; apply eval_Etempvar; exact Htemp|].
      apply deref_loc_copy. reflexivity.
    + reflexivity.
    + exact Hco.
    + exact Hoff.
  - eapply deref_loc_value; eauto.
Qed.

Definition iic_outside_cell chunk offset cell : Prop :=
  ink_cell_offset cell + size_chunk (ink_cell_chunk cell) <= offset \/
  offset + size_chunk chunk <= ink_cell_offset cell.

Lemma iic_store_shared_frame : forall a m chunk offset value after,
  area1_state_storage_block a <> area1_object_pool_block a ->
  In (chunk, offset) [(Mint32, 8); (Mint16unsigned, 2); (Mint32, 164); (Mint32, 4)] ->
  Mem.store chunk m (area1_state_storage_block a) offset value = Some after ->
  InkSameReadings a m after.
Proof.
  intros a m chunk offset value after Hseparate Hwhich Hstore cell Hin.
  eapply ibr_single_store_frames; [exact Hstore|].
  cbn [In] in Hwhich. repeat destruct Hwhich as [Hwhich|Hwhich];
    try contradiction; inversion Hwhich; subst; clear Hwhich;
    cbn [ink_shared_cells In] in Hin;
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
    try contradiction; subst cell; unfold ibr_cell_disjoint;
    cbn [ink_cell ink_cell_block ink_cell_offset ink_cell_chunk size_chunk];
    intuition (try congruence; lia).
Qed.

(** Just the readable values and four write permissions needed here. *)
Record InkInputPrefixStorage m mb ob oo : Prop := {
  iic_state_object_separate : mb <> ob;
  iic_object_read : Mem.load Mint32 m mb 136 = Some (Vptr ob oo);
  iic_collision_read : exists bits,
    Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 112))) = Some (Vint bits);
  iic_flags_read : exists flags, Mem.load Mint32 m mb 4 = Some (Vint flags);
  iic_writable : Forall (fun cell => Mem.valid_access m (fst cell) mb (snd cell) Writable)
    [(Mint32, 8); (Mint16unsigned, 2); (Mint32, 164); (Mint32, 4)]
}.

Theorem iic_construct_input_prefix : forall version m mb ob oo le,
  InkInputPrefixStorage m mb ob oo -> le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  exists after ready,
    iap_stage_chain (Clight.globalenv (selected_clight_target version)) empty_env le m
      (iic_stages version) E0 ready after /\
    ready ! IBM._m = Some (Vptr mb Ptrofs.zero) /\
    Mem.load Mint16unsigned after mb 2 = Some (Vint Int.zero) /\
    (forall cell, (ink_cell_block cell <> mb \/
      (iic_outside_cell Mint32 8 cell /\ iic_outside_cell Mint16unsigned 2 cell /\
       iic_outside_cell Mint32 164 cell /\ iic_outside_cell Mint32 4 cell)) ->
      ink_read after cell = ink_read m cell) /\
    (forall chunk b offset permission, Mem.valid_access m chunk b offset permission ->
      Mem.valid_access after chunk b offset permission).
Proof.
  intros version m mb ob oo le [Hseparate Hobject [collided Hcollided] [flags Hflags] Haccess] Hm.
  destruct (iic_layout version) as (Hp & Hi & Ho & Hoc & Hmc & Hf).
  inversion Haccess as [|? ? Hpaccess Haccess1]; subst.
  inversion Haccess1 as [|? ? Hiaccess Haccess2]; subst.
  inversion Haccess2 as [|? ? Hcaccess Haccess3]; subst.
  inversion Haccess3 as [|? ? Hfaccess Haccess4]; subst.
  destruct (Mem.valid_access_store m Mint32 mb 8 (Vint Int.zero) Hpaccess) as (m1 & Hs1).
  destruct (Mem.valid_access_store m1 Mint16unsigned mb 2 (Vint Int.zero)
    ltac:(eapply Mem.store_valid_access_1; eauto)) as (m2 & Hs2).
  destruct (Mem.valid_access_store m2 Mint32 mb 164 (Vint collided)
    ltac:(eapply Mem.store_valid_access_1; [exact Hs2|];
      eapply Mem.store_valid_access_1; eauto)) as (m3 & Hs3).
  destruct (Mem.valid_access_store m3 Mint32 mb 4 (Vint (Int.and flags (Int.repr 16777215)))
    ltac:(eapply Mem.store_valid_access_1; [exact Hs3|];
      eapply Mem.store_valid_access_1; [exact Hs2|];
      eapply Mem.store_valid_access_1; eauto)) as (after & Hs4).
  assert (Mem.load Mint32 m2 mb 136 = Some (Vptr ob oo)) as Hobject2.
  { rewrite (Mem.load_store_other _ _ _ _ _ _ Hs2) by (right; right; cbn; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ Hs1) by (right; right; cbn; lia). exact Hobject. }
  assert (Mem.load Mint32 m2 ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 112))) =
    Some (Vint collided)) as Hcollided2.
  { rewrite (Mem.load_store_other _ _ _ _ _ _ Hs2) by (left; congruence).
    rewrite (Mem.load_store_other _ _ _ _ _ _ Hs1) by (left; congruence). exact Hcollided. }
  assert (Mem.load Mint32 m3 mb 4 = Some (Vint flags)) as Hflags3.
  { rewrite (Mem.load_store_other _ _ _ _ _ _ Hs3) by (right; left; cbn; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ Hs2) by (right; right; cbn; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ Hs1) by (right; left; cbn; lia). exact Hflags. }
  exists after, (iic_ready le ob oo collided flags). split.
  - unfold iic_stages, iic_ready.
    eapply iap_chain_cons with (t1 := E0) (t2 := E0).
    + unfold iic_particle. eapply exec_Sassign with (v2 := Vint Int.zero) (v := Vint Int.zero).
      * eapply ibc_field_lvalue; [exact Hm|exact Hp].
      * constructor.
      * reflexivity.
      * eapply assign_loc_value; [reflexivity|exact Hs1].
    + eapply iap_chain_cons with (t1 := E0) (t2 := E0).
      * rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (ics_source_cuts version)))))).
        eapply exec_Sassign with (v2 := Vint Int.zero) (v := Vint Int.zero).
        -- eapply ibc_field_lvalue; [exact Hm|exact Hi].
        -- constructor.
        -- reflexivity.
        -- eapply assign_loc_value; [reflexivity|exact Hs2].
      * eapply iap_chain_cons with (t1 := E0) (t2 := E0).
        -- unfold iic_collisions. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_Sset. eapply ibc_field_read with (delta := 136) (chunk := Mint32);
                [exact Hm|exact Ho|reflexivity|exact Hobject2].
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** apply exec_Sset. eapply iic_field_at with (delta := 112) (chunk := Mint32);
                   [apply PTree.gss|exact Hoc|reflexivity|exact Hcollided2].
              ** eapply exec_Sassign with (v2 := Vint collided) (v := Vint collided).
                 --- eapply ibc_field_lvalue; [|exact Hmc].
                     repeat rewrite PTree.gso by discriminate. exact Hm.
                 --- apply eval_Etempvar. apply PTree.gss.
                 --- reflexivity.
                 --- eapply assign_loc_value; [reflexivity|exact Hs3].
        -- eapply iap_chain_cons with (t1 := E0) (t2 := E0); [|constructor].
           unfold iic_flags. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_Sset. eapply ibc_field_read with (delta := 4) (chunk := Mint32).
              ** repeat rewrite PTree.gso by discriminate. exact Hm.
              ** exact Hf.
              ** reflexivity.
              ** exact Hflags3.
           ++ eapply exec_Sassign with (v2 := Vint (Int.and flags (Int.repr 16777215)))
                (v := Vint (Int.and flags (Int.repr 16777215))).
              ** eapply ibc_field_lvalue; [|exact Hf].
                 repeat rewrite PTree.gso by discriminate. exact Hm.
              ** eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|constructor|reflexivity].
              ** reflexivity.
              ** eapply assign_loc_value; [reflexivity|exact Hs4].
  - split.
    + unfold iic_ready. repeat rewrite PTree.gso by discriminate. exact Hm.
    + split.
      * rewrite (Mem.load_store_other _ _ _ _ _ _ Hs4) by (right; left; cbn; lia).
        rewrite (Mem.load_store_other _ _ _ _ _ _ Hs3) by (right; left; cbn; lia).
        rewrite (Mem.load_store_same _ _ _ _ _ _ Hs2). reflexivity.
      * split.
        -- intros cell Houtside. unfold ink_read.
           rewrite (Mem.load_store_other _ _ _ _ _ _ Hs4)
             by (destruct Houtside as [Hb|(H8 & H2 & H164 & H4)]; [left; exact Hb|right; exact H4]).
           rewrite (Mem.load_store_other _ _ _ _ _ _ Hs3)
             by (destruct Houtside as [Hb|(H8 & H2 & H164 & H4)]; [left; exact Hb|right; exact H164]).
           rewrite (Mem.load_store_other _ _ _ _ _ _ Hs2)
             by (destruct Houtside as [Hb|(H8 & H2 & H164 & H4)]; [left; exact Hb|right; exact H2]).
           eapply Mem.load_store_other; [exact Hs1|].
           destruct Houtside as [Hb|(H8 & H2 & H164 & H4)]; [left; exact Hb|right; exact H8].
        -- intros. eapply Mem.store_valid_access_1; [exact Hs4|].
           eapply Mem.store_valid_access_1; [exact Hs3|].
           eapply Mem.store_valid_access_1; [exact Hs2|].
           eapply Mem.store_valid_access_1; eauto.
Qed.
