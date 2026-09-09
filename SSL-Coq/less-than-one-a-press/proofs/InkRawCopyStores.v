(** Exact reached stores, with frames derived from their real destinations. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkRawCopySource
  InkRawCopyExpressions InkBackwardExecution InkFloorResetExecution
  ObjectContactNecessity ContactConsumerExecution EyerokRank15LiveMovement
  CompositeLayoutRefinement EntryMemory OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Theorem irc_float_stage_actual_store :
  forall version e le m receiver value source index number cb ob oo t le' m' out,
  receiver <> value ->
  e ! IRC._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IRC._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) ->
  typeof index = tint -> irc_constant index = Some (Int.repr number) ->
  In number [6; 7; 9; 10; 11] ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (irc_float_stage version receiver value source index) t le' m' out ->
  exists read written,
    eval_expr (Clight.globalenv (selected_clight_target version)) e
      (PTree.set receiver (Vptr ob oo) le) m source read /\
    sem_cast read tfloat tfloat m = Some written /\
    Mem.store Mfloat32 m ob
      (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (136 + 4 * number)))) written = Some m' /\
    le' = PTree.set value read (PTree.set receiver (Vptr ob oo) le) /\
    t = E0 /\ out = Out_normal.
Proof.
  intros version e le m receiver value source index number cb ob oo t le' m' out
    Htemps Hlocal Hsymbol Hcurrent Htype Hconstant Hnumber Hrun.
  unfold irc_float_stage, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ rank15_current_object_expression ?object |- _ =>
    assert (object = Vptr ob oo) by (eapply irc_global_pointer_read; eauto); subst object end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ ?temps _ (rank15_raw_float_expression _ _ _) _ _ _ |- _ =>
    assert (temps ! receiver = Some (Vptr ob oo)) as Hreceiver
      by (rewrite PTree.gso by congruence; apply PTree.gss);
    destruct (irc_raw_location _ _ _ _ _ _ _ _ _ _ _ _ Hreceiver Htype Hconstant Hnumber Hl)
      as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar value tfloat) ?answer |- _ =>
    inversion Hr; subst; clear Hr end.
  all: try solve [match goal with
    Hbad : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion Hbad end].
  match goal with Htemp : (PTree.set value _ _) ! value = Some _ |- _ =>
    rewrite PTree.gss in Htemp; inversion Htemp; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  do 2 eexists. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. repeat split; reflexivity.
Qed.

Lemma irc_slot_address : forall slot delta,
  (slot < object_pool_capacity)%nat -> 0 <= delta <= 184 ->
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr delta)) =
    object_slot_offset slot + delta.
Proof.
  intros slot delta Hslot Hdelta.
  pose proof (rank15_pool_slot_offset_in_pointer_range _ Hslot) as Hrange.
  unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (object_slot_offset slot)) by (unfold object_size in Hrange; lia).
  rewrite (Ptrofs.unsigned_repr delta) by (change (0 <= delta <= 4294967295); lia).
  apply Ptrofs.unsigned_repr. unfold object_size in Hrange. lia.
Qed.

(** This interval covers the reached five stores. In particular, it excludes
    the display fields and every separately allocated State/global cell. *)
Definition irc_outside_copy_prefix (ob : block) slot chunk b offset : Prop :=
  b <> ob \/ offset + size_chunk chunk <= object_slot_offset slot + 160 \/
    object_slot_offset slot + 184 <= offset.
Definition irc_prefix_frame ob slot before after : Prop :=
  forall chunk b offset, irc_outside_copy_prefix ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk before b offset.

Lemma irc_store_frames_protected_reads : forall m m' ob slot number written,
  (slot < object_pool_capacity)%nat -> In number [6; 7; 9; 10; 11] ->
  Mem.store Mfloat32 m ob
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot))
      (Ptrofs.repr (136 + 4 * number)))) written = Some m' ->
  irc_prefix_frame ob slot m m'.
Proof.
  intros m m' ob slot number written Hslot Hnumber Hstore.
  assert (6 <= number <= 11) as Hrange by
    (destruct Hnumber as [<-|[<-|[<-|[<-|[<-|[]]]]]]; lia).
  rewrite irc_slot_address in Hstore by (auto; lia).
  intros chunk b offset Hseparate.
  eapply Mem.load_store_other; [exact Hstore|].
  unfold irc_outside_copy_prefix in Hseparate.
  cbn [size_chunk]. destruct Hseparate as [Hb|[Hlow|Hhigh]]; [left; exact Hb|right; left; lia|right; right; lia].
Qed.

Theorem irc_before_y_preserves_protected_reads :
  forall version e items le m t le' m' out cb ob slot,
  Forall (irc_before_stage_ok version) items ->
  (slot < object_pool_capacity)%nat -> cb <> ob ->
  e ! IRC._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IRC._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ocn_prepend items Sskip) t le' m' out ->
  irc_prefix_frame ob slot m m'.
Proof.
  intros version e items. induction items as [|s rest IH];
    intros le m t le' m' out cb ob slot Hitems Hslot Hseparate Hlocal Hsymbol Hcurrent Hrun.
  - inversion Hrun; subst. intros chunk b offset _. reflexivity.
  - inversion Hitems as [|? ? Hstage Hrest]; subst.
    destruct Hstage as (receiver & value & source & index & number &
      -> & Htemps & Hreceiver & Hvalue & Htype & Hconstant & Hnumber).
    assert (In number [6; 7; 9; 10; 11]) as Hallowed
      by (cbn in Hnumber; cbn; tauto).
    destruct (ibk_split_sequence _ _ _ _
      (irc_float_stage version receiver value source index) _ _ _ _ _ eq_refl Hrun)
      as (middle & middle_m & pre & suf & Htrace & Hfirst & Hsuffix).
    destruct (irc_float_stage_actual_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Htemps Hlocal Hsymbol Hcurrent Htype Hconstant Hallowed Hfirst)
      as (read & written & Hread & Hcast & Hstore & _).
    pose proof (irc_store_frames_protected_reads _ _ _ _ _ _ Hslot Hallowed Hstore) as HfirstFrame.
    assert (Mem.load Mint32 middle_m cb 0 =
      Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HcurrentNext.
    { rewrite HfirstFrame; [exact Hcurrent|left; exact Hseparate]. }
    pose proof (IH _ _ _ _ _ _ _ _ _ Hrest Hslot Hseparate Hlocal Hsymbol HcurrentNext Hsuffix) as HrestFrame.
    intros chunk b offset Houtside. rewrite HrestFrame, HfirstFrame; auto.
Qed.
