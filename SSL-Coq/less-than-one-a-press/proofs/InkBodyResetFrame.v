(** Open the next common helper instead of assuming it preserves Mario's
    height/depth record. This exact source footprint is independent of the
    controller history and retains a nonstandard body reference as a case. *)
From Coq Require Import Bool List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_mario jp_mario.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkActionPassStart InkActionPassHistory
  ObjectContactNecessity EyerokRank15LiveMovement SelectedClightTarget
  InkSharedReadings OrdinaryArea1EntryMemory.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ibr_body version := match version with
| VersionUS => us_mario.f_mario_reset_bodystate
| VersionJP => jp_mario.f_mario_reset_bodystate end.

Definition ibr_base temp tag :=
  Ederef (Etempvar temp (tptr (Tstruct tag noattr))) (Tstruct tag noattr).
Definition ibr_field temp tag field ty := Efield (ibr_base temp tag) field ty.

Record InkBodyStore := {
  ibr_member : ident;
  ibr_type : type;
  ibr_chunk : memory_chunk;
  ibr_delta : Z;
  ibr_constant : Z
}.

Definition ibr_stores : list InkBodyStore :=
  [{| ibr_member := IBM._capState; ibr_type := tschar; ibr_chunk := Mint8signed;
      ibr_delta := 4; ibr_constant := 1 |};
   {| ibr_member := IBM._eyeState; ibr_type := tschar; ibr_chunk := Mint8signed;
      ibr_delta := 5; ibr_constant := 0 |};
   {| ibr_member := IBM._handState; ibr_type := tschar; ibr_chunk := Mint8signed;
      ibr_delta := 6; ibr_constant := 0 |};
   {| ibr_member := IBM._modelState; ibr_type := tshort; ibr_chunk := Mint16signed;
      ibr_delta := 8; ibr_constant := 0 |};
   {| ibr_member := IBM._wingFlutter; ibr_type := tschar; ibr_chunk := Mint8signed;
      ibr_delta := 7; ibr_constant := 0 |}].

Definition ibr_store_statement spec := Sassign
  (ibr_field IBM._bodyState IBM._MarioBodyState (ibr_member spec) (ibr_type spec))
  (Econst_int (Int.repr (ibr_constant spec)) tint).
Definition ibr_flags := ibr_field IBM._m IBM._MarioState IBM._flags tuint.
Definition ibr_flag_tail := Ssequence (Sset IBM._t'1 ibr_flags)
  (Sassign ibr_flags (Ebinop Oand (Etempvar IBM._t'1 tuint)
    (Eunop Onotint (Econst_int (Int.repr 64) tint) tint) tuint)).
Definition ibr_pointer_read := Sset IBM._bodyState
  (ibr_field IBM._m IBM._MarioState IBM._marioBodyState (tptr (Tstruct IBM._MarioBodyState noattr))).

Lemma ibr_source : forall version,
  fn_vars (ibr_body version) = [] /\
  fn_params (ibr_body version) = [(IBM._m, tptr (Tstruct IBM._MarioState noattr))] /\
  fn_body (ibr_body version) = Ssequence ibr_pointer_read
    (ocn_prepend (map ibr_store_statement ibr_stores) ibr_flag_tail) /\
  forallb ibk_normal (map ibr_store_statement ibr_stores) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Definition ibr_layout_check ce spec :=
  ibcc_field_ok ce IBM._MarioBodyState (ibr_member spec) (ibr_delta spec).

Lemma ibr_selected_layout : forall version,
  let ce := prog_comp_env (selected_clight_target version) in
  ibcc_field_ok ce IBM._MarioState IBM._marioBodyState 152 = true /\
  ibcc_field_ok ce IBM._MarioState IBM._flags 4 = true /\
  forallb (ibr_layout_check ce) ibr_stores = true.
Proof.
  intro version. cbn zeta. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Lemma ibr_store_modes : Forall
  (fun spec => access_mode (ibr_type spec) = By_value (ibr_chunk spec)) ibr_stores.
Proof. repeat constructor. Qed.

Lemma ibr_field_read_value : forall (ge : genv) e le m temp tag field ty delta chunk
    b ofs value answer,
  le ! temp = Some (Vptr b ofs) ->
  ibcc_field_ok ge tag field delta = true -> access_mode ty = By_value chunk ->
  Mem.load chunk m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some value ->
  eval_expr ge e le m (ibr_field temp tag field ty) answer -> answer = value.
Proof.
  intros ge e le m temp tag field ty delta chunk b ofs value answer Htemp Hfield Hmode Hload Hread.
  assert (forall v, eval_expr ge e le m (ibr_base temp tag) v -> v = Vptr b ofs) as Hbase
    by (intros; eapply ibcc_deref_struct; eauto).
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibcc_field_location ge e le m (ibr_base temp tag) tag field ty b ofs delta
      _ _ _ eq_refl Hbase Hfield Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ ?memory ?loc ?offset ?bf ?v |- _ =>
    change (deref_loc ty memory loc offset bf v) in Hd;
    inversion Hd; subst; try congruence end.
  match goal with Haccess : access_mode _ = By_value _ |- _ =>
    rewrite Hmode in Haccess; inversion Haccess; subst end.
  match goal with Hr : Mem.loadv ?loaded_chunk _ _ = Some _ |- _ =>
    change (Mem.load loaded_chunk m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some answer)
      in Hr; congruence end.
Qed.

(** The address follows the actual pointer value, including its offset. *)
Lemma ibr_field_assignment_store : forall (ge : genv) e le m temp tag field ty delta chunk rhs
    t le' m' out b ofs,
  le ! temp = Some (Vptr b ofs) ->
  ibcc_field_ok ge tag field delta = true -> access_mode ty = By_value chunk ->
  ocn_exec ge e le m (Sassign (ibr_field temp tag field ty) rhs) t le' m' out ->
  t = E0 /\ le' = le /\ out = Out_normal /\
  exists value, Mem.store chunk m b
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) value = Some m'.
Proof.
  intros ge e le m temp tag field ty delta chunk rhs t le' m' out b ofs
    Htemp Hfield Hmode Hrun.
  inversion Hrun; subst; clear Hrun.
  rename le' into le.
  assert (forall value, eval_expr ge e le m (ibr_base temp tag) value ->
    value = Vptr b ofs) as Hbase by (intros; eapply ibcc_deref_struct; eauto).
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibcc_field_location ge e le m (ibr_base temp tag) tag field ty b ofs delta
      _ _ _ eq_refl Hbase Hfield Hl) as (-> & -> & ->) end.
  match goal with Ha : assign_loc ?gen _ ?memory ?loc ?offset ?bf ?v ?after |- _ =>
    change (assign_loc gen ty memory loc offset bf v after) in Ha;
    inversion Ha; subst; try congruence end.
  match goal with Haccess : access_mode _ = By_value _ |- _ =>
    rewrite Hmode in Haccess; inversion Haccess; subst end.
  repeat split. eexists; eassumption.
Qed.

Definition ibr_cell_disjoint target chunk offset (cell : InkReadCell) : Prop :=
  ink_cell_block cell <> target \/
  ink_cell_offset cell + size_chunk (ink_cell_chunk cell) <= offset \/
  offset + size_chunk chunk <= ink_cell_offset cell.

Definition ibr_body_disjoint body ofs spec cell :=
  ibr_cell_disjoint body (ibr_chunk spec)
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (ibr_delta spec)))) cell.

Lemma ibr_single_store_frames : forall chunk m b offset value m' cell,
  Mem.store chunk m b offset value = Some m' ->
  ibr_cell_disjoint b chunk offset cell -> ink_read m' cell = ink_read m cell.
Proof.
  intros. unfold ink_read. eapply Mem.load_store_other; eauto.
Qed.

Lemma ibr_store_chain_frames : forall (ge : genv) e specs le m t le' m' body ofs,
  Forall (fun spec => ibr_layout_check ge spec = true) specs ->
  Forall (fun spec => access_mode (ibr_type spec) = By_value (ibr_chunk spec)) specs ->
  le ! IBM._bodyState = Some (Vptr body ofs) ->
  iap_stage_chain ge e le m (map ibr_store_statement specs) t le' m' ->
  t = E0 /\ le' = le /\
  forall cell, Forall (fun spec => ibr_body_disjoint body ofs spec cell) specs ->
    ink_read m' cell = ink_read m cell.
Proof.
  intros ge e specs. induction specs as [|spec specs IH];
    intros le m t le' m' body ofs Hlayout Hmodes Hbody Hchain.
  - inversion Hchain; subst. repeat split; reflexivity.
  - inversion Hlayout; subst. inversion Hmodes; subst.
    inversion Hchain; subst.
    match goal with Hrun : ocn_exec _ _ _ _ (ibr_store_statement spec) _ _ _ _ |- _ =>
      destruct (ibr_field_assignment_store ge e le m IBM._bodyState IBM._MarioBodyState
        (ibr_member spec) (ibr_type spec) (ibr_delta spec) (ibr_chunk spec)
        (Econst_int (Int.repr (ibr_constant spec)) tint) _ _ _ _ body ofs
        Hbody ltac:(assumption) ltac:(assumption) Hrun)
      as (-> & -> & _ & value & Hstore) end.
    match goal with Hrest : iap_stage_chain _ _ _ _ (map _ specs) _ _ _ |- _ =>
      destruct (IH _ _ _ _ _ body ofs ltac:(assumption) ltac:(assumption) Hbody Hrest)
        as (-> & -> & Hframe) end.
    split; [reflexivity|]. split; [reflexivity|].
    intros cell Hdisjoint. inversion Hdisjoint; subst.
    rewrite Hframe by assumption. eapply ibr_single_store_frames; eauto.
Qed.

Lemma ibr_flag_tail_frames : forall version e le m t le' m' out mb mo,
  le ! IBM._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ibr_flag_tail t le' m' out ->
  t = E0 /\ forall cell,
    ibr_cell_disjoint mb Mint32 (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 4))) cell ->
    ink_read m' cell = ink_read m cell.
Proof.
  intros version e le m t le' m' out mb mo Hm Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IBM._t'1 ibr_flags) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & first & last & Htrace & Hread & Hwrite).
  inversion Hread; subst; clear Hread.
  match type of Hwrite with ocn_exec ?ge ?env ?temps ?memory ?statement ?tr ?temps' ?memory' ?outcome =>
    assert (temps ! IBM._m = Some (Vptr mb mo)) as Hstill
      by (rewrite PTree.gso by discriminate; exact Hm);
    destruct (ibr_field_assignment_store ge env temps memory IBM._m IBM._MarioState
      IBM._flags tuint 4 Mint32 _ tr temps' memory' outcome mb mo Hstill
      (proj1 (proj2 (ibr_selected_layout version))) eq_refl Hwrite)
      as (-> & _ & _ & value & Hstore)
  end.
  split; [reflexivity|]. intros. eapply ibr_single_store_frames; eauto.
Qed.

(** A completed call has exactly the five body-field destinations and the
    Mario flag-word destination. No external-call frame is assumed here. *)
Theorem ibr_completed_reset_exact_frame : forall version m mb body bo t m' result,
  Mem.load Mint32 m mb 152 = Some (Vptr body bo) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ibr_body version)) [Vptr mb Ptrofs.zero] t m' result ->
  t = E0 /\ forall cell,
    Forall (fun spec => ibr_body_disjoint body bo spec cell) ibr_stores ->
    ibr_cell_disjoint mb Mint32 4 cell -> ink_read m' cell = ink_read m cell.
Proof.
  intros version m mb body bo t m' result Hbody Hcall.
  destruct (ibr_source version) as (Hvars & Hparams & Hsource & Hnormal).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IBM._m = Some (Vptr mb Ptrofs.zero)) as Hm by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hsource in Hr;
    destruct (ibk_split_sequence _ _ _ _ ibr_pointer_read _ _ _ _ _ eq_refl Hr)
      as (first_le & first_m & pre & suf & Htrace & Hread & Hrest) end.
  inversion Hread; subst; clear Hread.
  match goal with Hr : eval_expr ?ge ?e ?le ?memory _ ?v |- _ =>
    assert (v = Vptr body bo) as Hvalue by
      (eapply (ibr_field_read_value ge e le memory IBM._m IBM._MarioState IBM._marioBodyState
        (tptr (Tstruct IBM._MarioBodyState noattr)) 152 Mint32 mb Ptrofs.zero
        (Vptr body bo) v Hm (proj1 (ibr_selected_layout version)) eq_refl Hbody Hr));
    subst v end.
  destruct (iap_split_stages _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (middle & memory & first & last & Htrace & Hchain & Htail).
  assert (Forall (fun spec => ibr_layout_check
    (Clight.globalenv (selected_clight_target version)) spec = true) ibr_stores) as Hlayouts.
  { apply Forall_forall. intros x Hx.
    pose proof (proj2 (proj2 (ibr_selected_layout version))) as Hchecked.
    rewrite forallb_forall in Hchecked. exact (Hchecked x Hx). }
  destruct (ibr_store_chain_frames _ _ ibr_stores _ _ _ _ _ body bo
    Hlayouts
    ibr_store_modes ltac:(apply PTree.gss) Hchain) as (-> & -> & Hframe).
  match type of Htail with ocn_exec ?ge ?env ?temps ?memory _ ?tr ?temps' ?memory' ?outcome =>
    assert (temps ! IBM._m = Some (Vptr mb Ptrofs.zero)) as Hstill
      by (rewrite PTree.gso by discriminate; exact Hm);
    destruct (ibr_flag_tail_frames version env temps memory tr temps' memory' outcome
      mb Ptrofs.zero Hstill Htail) as (-> & Hflag)
  end.
  split; [rewrite Htrace; reflexivity|]. intros cell Hdisjoint Hflagdisjoint.
  rewrite Hflag by exact Hflagdisjoint. apply Hframe. exact Hdisjoint.
Qed.

Theorem ibr_completed_reset_preserves_shared_readings : forall version m a body bo t m' result,
  area1_state_storage_block a <> area1_object_pool_block a ->
  body <> area1_state_storage_block a -> body <> area1_object_pool_block a ->
  Mem.load Mint32 m (area1_state_storage_block a) 152 = Some (Vptr body bo) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ibr_body version)) [Vptr (area1_state_storage_block a) Ptrofs.zero] t m' result ->
  t = E0 /\ InkSameReadings a m m'.
Proof.
  intros version m a body bo t m' result Hstatepool Hbodystate Hbodypool Hbody Hcall.
  destruct (ibr_completed_reset_exact_frame _ _ _ _ _ _ _ _ Hbody Hcall) as [Ht Hframe].
  split; [exact Ht|]. intros cell Hin.
  pose proof (ink_shared_cells_regions a cell Hin) as Hregion.
  apply Hframe.
  - apply Forall_forall. intros spec Hspec.
    unfold ibr_body_disjoint, ibr_cell_disjoint. left. destruct Hregion; intuition congruence.
  - unfold ibr_cell_disjoint. destruct Hregion as [[Hb Ho]|[Hb Ho]].
    + right; right. cbn [size_chunk]. lia.
    + left. congruence.
Qed.
