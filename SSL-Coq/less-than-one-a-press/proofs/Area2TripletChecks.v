(** Conditional fresh-triplet exclusion across successive actual checks.
    The user-granted interlude contract preserves five named parent fields,
    not the outcome of a spawning check. Each check executes the generated
    distance stage and/or complete native command. Unloaded action is carried
    by induction, rather than assumed anew at every callback.

    This is a composition of actual Clight calls under explicit boundary
    contracts. It does not prove that an arbitrary gameplay history supplies
    those contracts or that a partial list covers all checks in that history. *)
From Coq Require Import List ZArith Lia Reals.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes SelectedClightTarget
  Area2TripletSpawner Area2TripletDistance Area2TripletDistanceUpdate
  Area2TripletCommand Area2Rank9ACoinFlight EyerokRank15LiveMovement
  InkCopyCaller InkScheduledActionSource InkNativeActionHistory
  ObjectContactNecessity ReadOnlyClightPaths.
Import ListNotations.
Local Open Scope Z_scope.

Definition tcs_offset oo index :=
  Ptrofs.unsigned (rank15_raw_address oo (Int.repr index)).
Definition tcs_kept_cells : list (memory_chunk * Z) :=
  [(Mint32, 1); (Mint32, 5); (Mfloat32, 6); (Mfloat32, 8); (Mint32, 49)].

(** oFlags, oIntangibleTimer, oPosX, oPosZ and oAction. Their values and
    indices are the ones read by the existing generated-source receipts. *)
Definition tcs_parent ob oo m : Prop :=
  Mem.load Mint32 m ob (tcs_offset oo 1) = Some (Vint (Int.repr 65)) /\
  Mem.load Mint32 m ob (tcs_offset oo 5) = Some (Vint (Int.repr (-1))) /\
  Mem.load Mfloat32 m ob (tcs_offset oo 6) = Some (Vsingle (ts_float 3181)) /\
  Mem.load Mfloat32 m ob (tcs_offset oo 8) = Some (Vsingle (ts_float 3587)) /\
  Mem.load Mint32 m ob (tcs_offset oo 49) = Some (Vint Int.zero).

Definition tcs_parent_frame ob oo before after : Prop :=
  forall chunk index, In (chunk, index) tcs_kept_cells ->
    Mem.load chunk after ob (tcs_offset oo index) =
    Mem.load chunk before ob (tcs_offset oo index).
Definition tcs_to_check_frame ob oo before after : Prop :=
  tcs_parent_frame ob oo before after /\
  Mem.load Mfloat32 after ob (tcs_offset oo 53) =
    Mem.load Mfloat32 before ob (tcs_offset oo 53).

Lemma tcs_frame_refl : forall ob oo m, tcs_to_check_frame ob oo m m.
Proof. unfold tcs_to_check_frame, tcs_parent_frame. intros; split; [intros; reflexivity|reflexivity]. Qed.

Lemma tcs_frame_carries_parent : forall ob oo before after,
  tcs_parent_frame ob oo before after -> tcs_parent ob oo before ->
  tcs_parent ob oo after.
Proof.
  intros ob oo before after Hframe Hparent.
  unfold tcs_parent in *. repeat rewrite Hframe by (cbn; tauto). exact Hparent.
Qed.

Lemma tcs_plain_offset : forall oo index,
  In index [1;5;6;8;49;53] ->
  Ptrofs.unsigned oo + 456 <= Ptrofs.max_unsigned ->
  tcs_offset oo index = Ptrofs.unsigned oo + 136 + 4 * index.
Proof.
  intros oo index Hindex Hbound.
  cbn in Hindex. destruct Hindex as [H|[H|[H|[H|[H|[H|[]]]]]]]; subst index;
    unfold tcs_offset, rank15_raw_address;
    rewrite Ptrofs.add_assoc;
    lazymatch goal with
    | |- Ptrofs.unsigned (Ptrofs.add oo ?off) = ?rhs =>
      let offset := eval vm_compute in (Ptrofs.unsigned off) in
      change (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr offset)) = rhs);
      rewrite Ptrofs.add_unsigned;
      rewrite (Ptrofs.unsigned_repr offset) by
        (change Ptrofs.max_unsigned with 4294967295; lia);
      rewrite Ptrofs.unsigned_repr by
        (pose proof (Ptrofs.unsigned_range oo); lia); lia
    end.
Qed.

(** The real distance store is disjoint from all five retained fields.
    This part is proved, not included in the interlude or library premise. *)
Theorem tcs_distance_store_preserves_parent : forall ob oo before after distance,
  Ptrofs.unsigned oo + 456 <= Ptrofs.max_unsigned ->
  Mem.store Mfloat32 before ob (tcs_offset oo 53) (Vsingle distance) = Some after ->
  tcs_parent_frame ob oo before after.
Proof.
  intros ob oo before after distance Hbound Hstore chunk index Hindex.
  eapply Mem.load_store_other; [exact Hstore|].
  right; left.
  rewrite !tcs_plain_offset by (try assumption; cbn in *; intuition congruence).
  cbn in Hindex. destruct Hindex as [H|[H|[H|[H|[H|[]]]]]];
    inversion H; subst; cbn; lia.
Qed.

(** The exact old-Clight library contract used by this conditional result.
    Only the result, gCurrentObject and the five parent cells are framed.
    It is restricted to the reached named sqrtf and its actual argument.
    The separately proved local bound runtime is not silently substituted
    for Clight's unspecified external oracle. *)
Definition tcs_sqrt_contract version memory argument cb ob oo : Prop :=
  forall fb fd trace after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb ->
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) memory fd
    [Vsingle argument] trace after result ->
  result = Vsingle (Float32.sqrt argument) /\
  Mem.load Mint32 after cb 0 = Mem.load Mint32 memory cb 0 /\
  tcs_parent_frame ob oo memory after.

Definition tcs_far ob oo m : Prop :=
  exists distance, Mem.load Mfloat32 m ob (tcs_offset oo 53) =
    Some (Vsingle distance) /\ Float32.cmp Clt distance ts_threshold = false.

(** Connect six actual Object reads, the named library contract, the
    post-call current-object read and the actual store in one supplied
    execution. Stock X/Z are derived from the carried invariant. *)
Theorem tcs_live_distance_stage_prepares_check :
  forall version e le before cb mb ob oo a mario mo b trace le' after out,
  e ! TU._gCurrentObject = None -> e ! TU._gMarioObject = None ->
  e ! TU._dist_between_objects = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gCurrentObject = Some cb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gMarioObject = Some mb ->
  Mem.load Mint32 before cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 before mb 0 = Some (Vptr mario mo) ->
  tcs_parent ob oo before ->
  Ptrofs.unsigned oo + 456 <= Ptrofs.max_unsigned ->
  td_position before ob oo a -> td_position before mario mo b ->
  ts_in_base (vec_x b) (vec_z b) ->
  rank9cf_finite (Float32.sub (vec_y a) (vec_y b)) ->
  (-16384 <= rank9cf_real (Float32.sub (vec_y a) (vec_y b)) <= 16384)%R ->
  tcs_sqrt_contract version before (td_squared a b) cb ob oo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    (tdu_distance_stage version) trace le' after out ->
  tcs_parent ob oo after /\ tcs_far ob oo after /\ out = Out_normal.
Proof.
  intros version e le before cb mb ob oo a mario mo b trace le' after out
    Hlc Hlm Hlf Hsc Hsm Hc Hm Hparent Hbound Ha Hb Hbase Fy Hy Hcontract Hrun.
  destruct (tdu_live_distance_reaches_field_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hlc Hlm Hlf Hsc Hsm Hc Hm Ha Hb Hrun)
    as (fb & fd & value & returned & Hsymbol & Hfun & Hcall & Hstore & Hout).
  destruct (Hcontract _ _ _ _ _ Hsymbol Hfun Hcall) as (-> & Hcurrent & Hframe).
  assert (Hstored : Mem.store Mfloat32 returned ob (tcs_offset oo 53)
    (Vsingle (Float32.sqrt (td_squared a b))) = Some after).
  { apply Hstore. rewrite Hcurrent. exact Hc. }
  split.
  - eapply tcs_frame_carries_parent.
    + eapply tcs_distance_store_preserves_parent; eauto.
    + eapply tcs_frame_carries_parent; eauto.
  - split; [|exact Hout].
    exists (Float32.sqrt (td_squared a b)). split.
    + erewrite Mem.load_store_same by exact Hstored. reflexivity.
    + assert (Hx : vec_x a = ts_float 3181) by
        (destruct Hparent as (_ & _ & Hx & _); destruct Ha as (Hax & _);
         change (Mem.load Mfloat32 before ob (tcs_offset oo 6) =
           Some (Vsingle (vec_x a))) in Hax; congruence).
      assert (Hz : vec_z a = ts_float 3587) by
        (destruct Hparent as (_ & _ & _ & Hz & _); destruct Ha as (_ & _ & Haz);
         change (Mem.load Mfloat32 before ob (tcs_offset oo 8) =
           Some (Vsingle (vec_z a))) in Haz; congruence).
      unfold td_squared. rewrite Hx, Hz.
      exact (ts_elevator_distance_rejects_native_guard _ _ _ Hbase Fy Hy).
Qed.

(** A completed real distance stage, followed by the precise field frame
    needed between the distance store and this parent's callback. No
    unloaded-action value is required here; the theorem supplies it. *)
Definition tcs_refresh version cb mb ob oo before ready : Prop :=
  exists e le a mario mo b trace le' stored out,
    e ! TU._gCurrentObject = None /\ e ! TU._gMarioObject = None /\
    e ! TU._dist_between_objects = None /\
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gCurrentObject = Some cb /\
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TU._gMarioObject = Some mb /\
    Mem.load Mint32 before cb 0 = Some (Vptr ob oo) /\
    Mem.load Mint32 before mb 0 = Some (Vptr mario mo) /\
    td_position before ob oo a /\ td_position before mario mo b /\
    ts_in_base (vec_x b) (vec_z b) /\
    rank9cf_finite (Float32.sub (vec_y a) (vec_y b)) /\
    (-16384 <= rank9cf_real (Float32.sub (vec_y a) (vec_y b)) <= 16384)%R /\
    tcs_sqrt_contract version before (td_squared a b) cb ob oo /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
      (tdu_distance_stage version) trace le' stored out /\
    tcs_to_check_frame ob oo stored ready.

Lemma tcs_refresh_prepares : forall version cb mb ob oo before ready,
  Ptrofs.unsigned oo + 456 <= Ptrofs.max_unsigned ->
  tcs_parent ob oo before -> tcs_refresh version cb mb ob oo before ready ->
  tcs_parent ob oo ready /\ tcs_far ob oo ready.
Proof.
  intros version cb mb ob oo before ready Hbound Hparent
    (e & le & a & mario & mo & b & trace & le' & stored & out &
      Hlc & Hlm & Hlf & Hsc & Hsm & Hc & Hm & Ha & Hb & Hbase &
      Fy & Hy & Hcontract & Hrun & Hframe & Hdistance).
  destruct (tcs_live_distance_stage_prepares_check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hlc Hlm Hlf Hsc Hsm Hc Hm Hparent Hbound Ha Hb Hbase Fy Hy Hcontract Hrun)
    as (Hstored & Hfar & _).
  split; [eapply tcs_frame_carries_parent; eauto|].
  destruct Hfar as (distance & Hload & Hreject).
  exists distance. split; [rewrite Hdistance; exact Hload|exact Hreject].
Qed.

(** The full generated CALL_NATIVE, including the live script operand and
    post-callback command advance. The only separation condition is between
    the object-pool block and the command-pointer global cell. *)
Definition tcs_native version cb ob oo before after : Prop :=
  exists cell command ofs callback trace result,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) ISN._gCurBhvCommand = Some cell /\
    Mem.load Mint32 before cell 0 = Some (Vptr command ofs) /\
    Mem.load Mint32 before command (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4))) =
      Some (Vptr callback Ptrofs.zero) /\
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TS._bhv_goomba_triplet_spawner_update = Some callback /\
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TS._gCurrentObject = Some cb /\
    Mem.load Mint32 before cb 0 = Some (Vptr ob oo) /\
    ob <> cell /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      before (Internal (isn_body version)) [] trace after result.

(** This certificate selects a call-free, store-free path through the real
    callback body. It rules out its child-spawning branch, not just a final
    memory difference. readonly_path_forces_every_execution gives uniqueness. *)
Definition tcs_rejected_check version ob oo ready : Prop :=
  tcs_parent ob oo ready /\ tcs_far ob oo ready /\
  forall e le, e ! TS._gCurrentObject = None ->
    exists final, readonly_path (Clight.globalenv (selected_clight_target version))
      e ready le (fn_body (ts_body version)) final.

Lemma tcs_native_rejects_and_preserves : forall version cb ob oo before after,
  tcs_parent ob oo before -> tcs_far ob oo before ->
  tcs_native version cb ob oo before after ->
  tcs_rejected_check version ob oo before /\ tcs_parent ob oo after.
Proof.
  intros version cb ob oo before after Hparent Hfar
    (cell & command & ofs & callback & trace & result & Hsymbol & Hcommand &
      Hoperand & Hcallback & Hcs & Hcurrent & Hseparate & Hcall).
  destruct Hfar as (distance & Hdistance & Hreject).
  assert (Haction : Mem.load Mint32 before ob (tcs_offset oo 49) = Some (Vint Int.zero))
    by (exact (proj2 (proj2 (proj2 (proj2 Hparent))))).
  destruct (tcn_native_command_preserves_parent_and_advances _ _ _ _ _ _ _ _ _ _ _ _ _
    Hsymbol Hcommand Hoperand Hcallback Hcs Hcurrent Haction Hdistance Hreject Hcall)
    as (_ & _ & _ & Hframe).
  split.
  - split; [exact Hparent|]. split; [exists distance; auto|].
    intros e le Hlocal. eapply ts_native_readonly_path; eauto.
  - eapply tcs_frame_carries_parent; [|exact Hparent].
    intros chunk index Hindex. apply Hframe; [|exact Hseparate].
    eapply ibcc_loaded_block_valid. exact Haction.
Qed.

(** Later checks. The interlude frame is equality of five loads, NOT
    "the action is unloaded" or "no spawning occurs." Mario and the world
    can otherwise change. Each list element is an actual callback input. *)
Inductive TripletLaterChecks version cb mb ob oo :
    mem -> list mem -> mem -> Prop :=
| tcs_later_nil : forall m, TripletLaterChecks version cb mb ob oo m [] m
| tcs_later_cons : forall previous before ready after checks last,
    tcs_parent_frame ob oo previous before ->
    tcs_refresh version cb mb ob oo before ready ->
    tcs_native version cb ob oo ready after ->
    TripletLaterChecks version cb mb ob oo after checks last ->
    TripletLaterChecks version cb mb ob oo previous (ready :: checks) last.

Theorem tcs_every_later_check_rejects : forall version cb mb ob oo first checks last,
  Ptrofs.unsigned oo + 456 <= Ptrofs.max_unsigned ->
  tcs_parent ob oo first ->
  TripletLaterChecks version cb mb ob oo first checks last ->
  Forall (tcs_rejected_check version ob oo) checks /\ tcs_parent ob oo last.
Proof.
  intros version cb mb ob oo first checks last Hbound Hparent Hchecks.
  induction Hchecks as [m|previous before ready after checks last Hframe Hrefresh Hnative Hrest IH].
  - split; [constructor|exact Hparent].
  - destruct (tcs_refresh_prepares _ _ _ _ _ _ _ Hbound
      (tcs_frame_carries_parent _ _ _ _ Hframe Hparent) Hrefresh) as [Hready Hfar].
    destruct (tcs_native_rejects_and_preserves _ _ _ _ _ _ Hready Hfar Hnative)
      as [Hreject Hafter].
    destruct (IH Hafter) as [Hall Hlast]. split; [constructor; assumption|exact Hlast].
Qed.

(** The first script pass uses the initialized 19000 distance. We start at
    its actual native-command boundary, after script setup (including flags
    and floor drop). Initialization reachability is not reconstructed. *)
Definition TripletFreshChecks version cb mb ob oo first checks last : Prop :=
  exists after rest,
    Mem.load Mfloat32 first ob (tcs_offset oo 53) =
      Some (Vsingle (Float32.of_bits (Int.repr 1184133120))) /\
    tcs_native version cb ob oo first after /\
    TripletLaterChecks version cb mb ob oo after rest last /\
    checks = first :: rest.

Definition TripletConditionalChecksExclusion : Prop :=
  forall version cb mb ob oo first checks last,
    Ptrofs.unsigned oo + 456 <= Ptrofs.max_unsigned ->
    tcs_parent ob oo first ->
    TripletFreshChecks version cb mb ob oo first checks last ->
    Forall (tcs_rejected_check version ob oo) checks /\ tcs_parent ob oo last.

Theorem tcs_fresh_triplet_never_spawns_under_contract : TripletConditionalChecksExclusion.
Proof.
  intros version cb mb ob oo first checks last Hbound Hparent
    (after & rest & Hinitial & Hnative & Hlater & ->).
  assert (Hfar : tcs_far ob oo first).
  { eexists. split; [exact Hinitial|exact (proj1 ts_initial_distance_rejects)]. }
  destruct (tcs_native_rejects_and_preserves _ _ _ _ _ _ Hparent Hfar Hnative)
    as [Hfirst Hafter].
  destruct (tcs_every_later_check_rejects _ _ _ _ _ _ _ _ Hbound Hafter Hlater)
    as [Hall Hlast]. split; [constructor; assumption|exact Hlast].
Qed.

(** The output certificate is stronger than assuming final action zero:
    every supplied execution of each recorded callback body is silent,
    preserves its complete input memory and finishes normally. *)
Theorem tcs_each_certified_body_is_readonly :
  forall version ob oo ready e le trace le' after out,
  tcs_rejected_check version ob oo ready ->
  e ! TS._gCurrentObject = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le ready
    (fn_body (ts_body version)) trace le' after out ->
  trace = E0 /\ after = ready /\ out = Out_normal.
Proof.
  intros version ob oo ready e le trace le' after out (_ & _ & Hpath) Hlocal Hrun.
  destruct (Hpath e le Hlocal) as [final Hreadonly].
  destruct (readonly_path_forces_every_execution _ _ _ _ _ _ Hreadonly
    _ _ _ _ Hrun) as (Ht & _ & Hm & Ho). auto.
Qed.
