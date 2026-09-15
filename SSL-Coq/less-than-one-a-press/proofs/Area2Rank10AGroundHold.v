
(** A scoped conditional exclusion of the eleven-descent hold. The contract
    names the actual queries and input cells; it never assumes alignment.
    Applicability to a complete scheduler/controller execution is separate. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From Flocq Require Import Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank10AGroundAlignment
  Area2Rank10ABlockedStep Area2Rank10AGroundPound Area2Rank9ACoinFlight
  Area2RolloutActionGate InkFloorHistorySource InkFloorHistoryExecution
  InkFloorHistoryBackward InkFloorHistoryCall InkFloorHistoryQuery
  InkBackwardSource InkBackwardExecution InkCopyEntry InkCopyCaller
  InkFloorResetSource InkFloorResetExecution InkFloorCallEffects
  ObjectContactNecessity ContactConsumerExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Float32.cmp Float32.compare.

Definition rank10h_surface := tptr (Tstruct IFH._Surface noattr).
Lemma rank10h_floor_read : forall ge e le m local fb fo value,
  e ! IFH._floor = Some (local,rank10h_surface) ->
  Mem.load Mint32 m local 0 = Some (Vptr fb fo) ->
  eval_expr ge e le m (Evar IFH._floor rank10h_surface) value ->
  value = Vptr fb fo.
Proof.
  intros ge e le m local fb fo value He Hload Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ He Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hl : Mem.loadv _ _ _ = Some value |- _ =>
    change (Mem.load Mint32 m local 0 = Some value) in Hl; congruence end.
Qed.

Lemma rank10h_nonnull_test_false : forall ge e le m fb fo choice,
  le ! IFH._t'21 = Some (Vptr fb fo) ->
  ocn_test_value ge e le m ifh_null_guard choice -> choice = false.
Proof.
  intros ge e le m fb fo choice Hptr [value [Hr Hb]].
  unfold ifh_null_guard in Hr. inversion Hr; subst.
  - match goal with Ht : eval_expr _ _ _ _ (Etempvar IFH._t'21 _) ?v |- _ =>
      assert (v = Vptr fb fo) by (eapply ocn_temp_value; eauto); subst v end.
    match goal with Hc : eval_expr _ _ _ _ (Ecast _ _) _ |- _ => inversion Hc; subst; clear Hc end.
    all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion Hbad end].
    match goal with Hc : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hc; subst end.
    match goal with Hc : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hc; inversion Hc; subst end.
    lazymatch goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      change (option_map Val.of_bool
        (Val.cmpu_bool (Mem.valid_pointer m) Ceq (Vptr fb fo) (Vint Int.zero)) = Some value) in Hsem;
      cbn [Val.cmpu_bool] in Hsem;
      repeat match type of Hsem with context [if ?test then _ else _] =>
        destruct test eqn:?; cbn in Hsem; try discriminate end;
      inversion Hsem; subst; cbn in Hb end.
    rewrite Int.eq_true in Hb. cbn in Hb. congruence.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Definition rank10h_action := Efield ibcc_state IFH._action tuint.
Lemma rank10h_action_read : forall version e le m mb action value,
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 12 = Some (Vint action) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m rank10h_action value ->
  value = Vint action.
Proof.
  intros version e le m mb action value Hm Hload Hr. inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ rank10h_action _ _ _ |- _ =>
    destruct (ibcc_field_location _ _ _ _ ibcc_state IFH._MarioState IFH._action tuint
      mb Ptrofs.zero 12 _ _ _ eq_refl
      ltac:(intros; eapply ibcc_deref_struct; eauto) (proj2 (rag_layout version)) Hl)
      as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hl : Mem.loadv _ _ _ = Some value |- _ =>
    change (Mem.load Mint32 m mb 12 = Some value) in Hl; congruence end.
Qed.
Definition rank10h_shell_test := Ebinop Oand (Etempvar IFH._t'20 tuint)
  (Ebinop Oshl (Econst_int (Int.repr 1) tint) (Econst_int (Int.repr 16) tint) tint) tuint.
Lemma rank10h_shell_test_false : forall ge e le m action choice,
  le ! IFH._t'20 = Some (Vint action) ->
  Int.and action (Int.repr 65536) = Int.zero ->
  ocn_test_value ge e le m rank10h_shell_test choice -> choice = false.
Proof.
  intros ge e le m action choice Haction Hbit [value [Hr Hb]].
  unfold rank10h_shell_test in Hr.
  repeat match goal with H : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion H; subst; clear H end.
  all: try solve [match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end].
  all: repeat match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in H; subst end.
  all: match goal with H : eval_expr _ _ _ _ (Etempvar IFH._t'20 _) ?v |- _ =>
    assert (v = Vint action) by (eapply ocn_temp_value; eauto); subst v end.
  all: repeat match goal with H : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    progress (cbn in H; inversion H; subst; clear H) end.
  change (bool_val (Vint (Int.and action (Int.repr 65536))) tuint m = Some choice) in Hb.
  rewrite Hbit in Hb. cbn in Hb. rewrite Int.eq_true in Hb. cbn in Hb. congruence.
Qed.
Definition rank10h_shell_yes version := match ifh_water version with
| Ssequence (Ssequence _ (Sifthenelse _ yes _)) _ => yes | _ => Sskip end.
Definition rank10h_water_yes version := match ifh_water version with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Lemma rank10h_water_source : forall version,
  ifh_water version = Ssequence
    (Ssequence (Sset IFH._t'20 rank10h_action)
      (Sifthenelse rank10h_shell_test (rank10h_shell_yes version)
        (Sset IFH._t'6 (Econst_int Int.zero tint))))
    (Sifthenelse (Etempvar IFH._t'6 tint) (rank10h_water_yes version) Sskip) /\
  ibk_normal (Sifthenelse rank10h_shell_test (rank10h_shell_yes version)
        (Sset IFH._t'6 (Econst_int Int.zero tint))) = true.
Proof. intros []; split; reflexivity. Qed.
Lemma rank10h_water_noshell : forall version e le m mb action t le' after out,
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 12 = Some (Vint action) ->
  Int.and action (Int.repr 65536) = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_water version) t le' after out ->
  after = m /\ le' = PTree.set IFH._t'6 (Vint Int.zero)
    (PTree.set IFH._t'20 (Vint action) le).
Proof.
  intros version e le m mb action t le' after out Hm Haction Hbit Hrun.
  rewrite (proj1 (rank10h_water_source version)) in Hrun.
  apply ifh_sequence_reassociate in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IFH._t'20 rank10h_action) _ _ _ _ _ eq_refl Hrun)
    as (al & am & at' & rt & Ht & Hset & Hrest).
  inversion Hset; subst.
  match goal with Hr : eval_expr _ _ _ _ rank10h_action ?v |- _ =>
    assert (v = Vint action) by (eapply rank10h_action_read; eauto); subst v end.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (rank10h_water_source version)) Hrest)
    as (sl & sm & st & wt & Hst & Hshell & Hwater).
  inversion Hshell; subst; clear Hshell.
  assert (b = false) by (eapply rank10h_shell_test_false;
    [apply PTree.gss|exact Hbit|unfold ocn_test_value; eauto]). subst b.
  match goal with Hs : ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ =>
    inversion Hs; subst; clear Hs end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  inversion Hwater; subst.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IFH._t'6 _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_temp_value; [exact Hr|apply PTree.gss]); subst v end.
  match goal with Hb : bool_val (Vint Int.zero) _ _ = Some _ |- _ =>
    cbn in Hb; rewrite Int.eq_true in Hb; cbn in Hb; inversion Hb; subst end.
  match goal with Hs : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
    inversion Hs; subst end. split; reflexivity.
Qed.

(** These are observable inputs after the real wall/floor/ceiling query
    prefix. Null is excluded explicitly; the shell override is excluded by
    the actual action bit. Neither a low gap nor a successful snap is here. *)
Record Rank10HQueryResults (e : env) (le : temp_env) (m : mem)
    (mb nb : block) (y floor : float32) : Prop := {
  rank10h_live_floor : exists local fb fo,
    e ! IFH._floor = Some (local,rank10h_surface) /\
    Mem.load Mint32 m local 0 = Some (Vptr fb fo);
  rank10h_action_bits : exists action,
    Mem.load Mint32 m mb 12 = Some (Vint action) /\
    Int.and action (Int.repr 65536) = Int.zero;
  rank10h_proposed_y : Mem.load Mfloat32 m nb 4 = Some (Vsingle y);
  rank10h_returned_height : le ! IFH._floorHeight = Some (Vsingle floor);
  rank10h_returned_ceiling : exists ceiling,
    le ! IFH._ceilHeight = Some (Vsingle ceiling) /\
    rank9cf_finite ceiling /\ (5222 <= rank9cf_real ceiling)%R
}.

Theorem rank10h_queried_tail_aligns : forall version e le m mb nb y floor t le' after out,
  e ! IFH._vec3f_set = None -> e ! IFH._atan2s = None ->
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  le ! IFH._nextPos = Some (Vptr nb Ptrofs.zero) ->
  Rank10HQueryResults e le m mb nb y floor ->
  rank9cf_finite floor -> (0 <= rank9cf_real floor <= 5000)%R ->
  Float32.cmp Cgt y (Float32.add floor ifh_100) = false ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_quarter_tail version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle floor).
Proof.
  intros version e le m mb nb y floor t le' after out
    Hset Hangle Hm Hnext Hquery Ff Bf Hlow Hrun.
  destruct Hquery as [(local & fb & fo & He & Hfl)
    (action & Ha & Hbit) Hy Hfloor (ceiling & Hceil & Fc & Bc)].
  destruct (ifh_missing_floor_returns_or_reaches_actual_water_tail _ _ _ _ _ _ _ _ _ Hrun)
    as (value & Hread & Hcases).
  assert (value = Vptr fb fo) by (eapply rank10h_floor_read; eauto). subst value.
  destruct Hcases as [(Htest & _)|(Htest & wl & wm & wt & rt & Htr & Hwater & Hpost)].
  - pose proof (rank10h_nonnull_test_false _ _ _ _ _ _ _ (PTree.gss _ _ _) Htest).
    discriminate.
  - destruct (rank10h_water_noshell version e (PTree.set IFH._t'21 (Vptr fb fo) le)
      m mb action wt wl wm Out_normal
      ltac:(rewrite PTree.gso by discriminate; exact Hm) Ha Hbit Hwater) as [-> ->].
    assert (Mem.valid_block m mb) as Hvalid by (eapply ibcc_loaded_block_valid; exact Ha).
    lazymatch type of Hpost with ocn_exec _ _ ?temps _ _ _ _ _ _ =>
    pose proof (rank10b_clear_ceiling_reaches_alignment version e temps m nb Ptrofs.zero
      y floor ceiling _ le' after out
      ltac:(repeat rewrite PTree.gso by discriminate; exact Hnext)
      ltac:(repeat rewrite PTree.gso by discriminate; exact Hfloor)
      ltac:(repeat rewrite PTree.gso by discriminate; exact Hceil)
      Hy Hlow Ff Fc Bf Bc Hpost) as Haccept end.
    lazymatch type of Haccept with ocn_exec _ ?environment ?temps ?memory _ _ _ _ _ =>
    eapply (rank10g_accept_completes_y version environment temps memory mb floor);
      [exact Hset|exact Hangle| | |exact Hvalid|exact Haccept] end;
      repeat rewrite PTree.gso by discriminate; assumption.
Qed.

Lemma rank10h_entry_storage : forall version ge before mb nb e le entry,
  Mem.valid_block before mb ->
  function_entry2 ge (ifh_quarter_body version)
    [Vptr mb Ptrofs.zero;Vptr nb Ptrofs.zero] before e le entry ->
  e ! IFH._atan2s = None /\
  Forall (fun '(target,_,_) => target <> mb) (blocks_of_env ge e).
Proof.
  intros version ge before mb nb e le entry Hvalid Hentry.
  destruct (ifh_quarter_source_cuts version) as (_ & Hvars & _).
  inversion Hentry; subst.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ (_ :: _) _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ [] _ _ |- _ => inversion Ha; subst; clear Ha end.
  lazymatch type of Hvalid with Mem.valid_block ?initial mb =>
  lazymatch goal with Ha : Mem.alloc initial _ _ = (?middle,?first),
    Hb : Mem.alloc ?middle _ _ = (?last,?second) |- _ =>
    assert (first <> mb) as Hfirst by
      (intro Heq; subst first; exact (Mem.fresh_block_alloc _ _ _ _ _ Ha Hvalid));
    assert (Mem.valid_block middle mb) as Hv by
      (eapply Mem.valid_block_alloc; [exact Ha|exact Hvalid]);
    assert (second <> mb) as Hsecond by
      (intro Heq; subst second; exact (Mem.fresh_block_alloc _ _ _ _ _ Hb Hv))
  end end.
  split.
  - repeat rewrite PTree.gso by discriminate. apply PTree.gempty.
  - match goal with |- Forall _ (blocks_of_env _ (PTree.set _ (?second,_) (PTree.set _ (?first,_) _))) =>
      first [change (Forall (fun '(target,_,_) => target <> mb) [(first,0,4);(second,0,4)]) |
             change (Forall (fun '(target,_,_) => target <> mb) [(second,0,4);(first,0,4)])] end.
    repeat constructor; assumption.
Qed.

(** A loader/query contract at the actual prefix reached by this call.
    All preceding helpers retain their real execution and memory effects.
    Its fields remain explicit conditional premises, not a coverage result. *)
Definition rank10h_query_contract version before mb nb y floor : Prop :=
  forall e entry_le entry_m cut_le cut_m pre,
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (ifh_quarter_body version) [Vptr mb Ptrofs.zero;Vptr nb Ptrofs.zero]
    before e entry_le entry_m ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e entry_le entry_m
    (ocn_prepend (ifh_quarter_prefix version) Sskip) pre cut_le cut_m Out_normal ->
  Rank10HQueryResults e cut_le cut_m mb nb y floor.

Theorem rank10h_completed_quarter_aligns : forall version before mb nb y floor t after result,
  Mem.valid_block before mb ->
  rank10h_query_contract version before mb nb y floor ->
  rank9cf_finite floor -> (0 <= rank9cf_real floor <= 5000)%R ->
  Float32.cmp Cgt y (Float32.add floor ifh_100) = false ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    before (Internal (ifh_quarter_body version))
    [Vptr mb Ptrofs.zero;Vptr nb Ptrofs.zero] t after result ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle floor).
Proof.
  intros version before mb nb y floor t after result Hv Hquery Ff Bf Hlow Hcall.
  destruct (ifh_completed_quarter_call_reaches_queried_floor_cut _ _ _ _ _ _ _ _ _ Hcall)
    as (e & el & em & cl & cm & ll & lm & pre & rest & out &
      Htr & Hentry & Hprefix & Hm & Hnext & Hset & Hcopy & Htail & Hout & Hfree).
  destruct (rank10h_entry_storage _ _ _ _ _ _ _ _ Hv Hentry) as [Hangle Hfrees].
  pose proof (rank10h_queried_tail_aligns _ _ _ _ _ _ _ _ _ _ _ _
    Hset Hangle Hm Hnext (Hquery _ _ _ _ _ _ Hentry Hprefix) Ff Bf Hlow Htail) as Hbody.
  rewrite (ifc_free_list_frame _ _ _ _ _ _ Hfrees Hfree). exact Hbody.
Qed.

Lemma rank10h_small_descent_guard : forall older floor,
  0 <= older <= 5010 -> 0 <= floor <= 5000 -> floor <= older <= floor + 10 ->
  Float32.cmp Cgt (rank9cf_integer older)
    (Float32.add (rank9cf_integer floor) ifh_100) = false.
Proof.
  intros older floor Bo Bf Bstep.
  destruct (rank9cf_integer_exact older ltac:(lia)) as [Ro Fo].
  destruct (rank9cf_integer_exact floor ltac:(lia)) as [Rf Ff].
  assert (H100 : ifh_100 = rank9cf_integer 100)
    by (apply rank9cf_bits_injective; vm_compute; reflexivity).
  rewrite H100.
  destruct (rank9cf_integer_exact 100 ltac:(lia)) as [R100 F100].
  destruct (rank9cf_add_range (rank9cf_integer floor) (rank9cf_integer 100)
    (floor+100) (floor+100) Ff F100 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite Rf, R100, plus_IZR; lra)) as [Ft Bt].
  assert (Hlt : (rank9cf_real (rank9cf_integer older) <
    rank9cf_real (Float32.add (rank9cf_integer floor) (rank9cf_integer 100)))%R).
  { rewrite Ro. assert (IZR older < IZR (floor+100))%R by (apply IZR_lt; lia). lra. }
  unfold Float32.cmp, Float32.compare.
  rewrite Bcompare_correct by assumption. rewrite Rcompare_Lt by exact Hlt. reflexivity.
Qed.

Definition rank10h_ground_call version mb floor before after : Prop :=
  exists nb y t result,
    Mem.load Mfloat32 before mb 64 = Some (Vsingle y) /\
    rank10h_query_contract version before mb nb y (rank9cf_integer floor) /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      before (Internal (ifh_quarter_body version))
      [Vptr mb Ptrofs.zero;Vptr nb Ptrofs.zero] t after result.

Theorem rank10h_no_first_missed_alignment : forall version mb older floor before after,
  0 <= older <= 5010 -> 0 <= floor <= 5000 -> floor <= older <= floor+10 ->
  Mem.load Mfloat32 before mb 64 = Some (Vsingle (rank9cf_integer older)) ->
  rank10h_ground_call version mb floor before after ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle (rank9cf_integer floor)).
Proof.
  intros version mb older floor before after Bo Bf Bstep Hy
    (nb & y & t & result & Hread & Hquery & Hcall).
  assert (y = rank9cf_integer older) by congruence. subst y.
  destruct (rank9cf_integer_exact floor ltac:(lia)) as [Rf Ff].
  eapply rank10h_completed_quarter_aligns; [eapply ibcc_loaded_block_valid; exact Hy|
    exact Hquery|exact Ff| |eapply rank10h_small_descent_guard; eauto|exact Hcall].
  rewrite Rf. split; apply IZR_le; lia.
Qed.

(** Composition of actual calls under explicit boundary contracts, not a
    complete frame scheduler. Between calls, the world may change (including
    elevator descent and collision reload), while this scoped mechanism holds
    Mario's Y fixed. The proposed Y is that carried value. Alignment is NOT
    part of the interlude premise: it is derived by the next actual call. *)
Inductive Rank10HDescentCalls version mb origin : nat -> mem -> mem -> Prop :=
| rank10h_calls_zero : forall m, Rank10HDescentCalls version mb origin 0 m m
| rank10h_calls_next : forall n first middle ready last,
    Rank10HDescentCalls version mb origin n first middle ->
    128 <= origin - 10 * Z.of_nat (S n) ->
    Mem.load Mfloat32 ready mb 64 = Mem.load Mfloat32 middle mb 64 ->
    rank10h_ground_call version mb (origin - 10 * Z.of_nat (S n)) ready last ->
    Rank10HDescentCalls version mb origin (S n) first last.

Theorem rank10h_every_contracted_descent_realigns : forall version mb origin n first last,
  128 <= origin <= 4966 ->
  Mem.load Mfloat32 first mb 64 = Some (Vsingle (rank9cf_integer origin)) ->
  Rank10HDescentCalls version mb origin n first last ->
  Mem.load Mfloat32 last mb 64 =
    Some (Vsingle (rank9cf_integer (origin - 10 * Z.of_nat n))).
Proof.
  intros version mb origin n first last Bo Hy Hcalls.
  induction Hcalls.
  - replace (origin - 10 * Z.of_nat 0) with origin by lia. exact Hy.
  - eapply rank10h_no_first_missed_alignment with (older := origin - 10 * Z.of_nat n).
    + rewrite Nat2Z.inj_succ in H. lia.
    + rewrite Nat2Z.inj_succ in *. lia.
    + rewrite Nat2Z.inj_succ. lia.
    + rewrite H0. apply IHHcalls. exact Hy.
    + exact H1.
Qed.

Theorem rank10h_eleven_descent_hold_impossible : forall version mb origin first last,
  238 <= origin <= 4966 ->
  Mem.load Mfloat32 first mb 64 = Some (Vsingle (rank9cf_integer origin)) ->
  Rank10HDescentCalls version mb origin 11 first last ->
  Mem.load Mfloat32 last mb 64 <>
    Some (Vsingle (rank9cf_integer origin)).
Proof.
  intros version mb origin first last Bo Hy Hcalls Hheld.
  pose proof (rank10h_every_contracted_descent_realigns version mb origin 11 first last
    ltac:(lia) Hy Hcalls) as Hlast.
  change (Mem.load Mfloat32 last mb 64 = Some (Vsingle (rank9cf_integer (origin-110)))) in Hlast.
  assert (Heq : rank9cf_integer (origin-110) = rank9cf_integer origin) by congruence.
  pose proof (f_equal rank9cf_real Heq) as Hreal.
  rewrite (proj1 (rank9cf_integer_exact (origin-110) ltac:(lia))),
    (proj1 (rank9cf_integer_exact origin ltac:(lia))) in Hreal.
  apply eq_IZR in Hreal. lia.
Qed.

Definition Rank10AGroundHoldBoundary : Prop :=
  (forall version mb origin n first last,
    128 <= origin <= 4966 ->
    Mem.load Mfloat32 first mb 64 = Some (Vsingle (rank9cf_integer origin)) ->
    Rank10HDescentCalls version mb origin n first last ->
    Mem.load Mfloat32 last mb 64 =
      Some (Vsingle (rank9cf_integer (origin - 10 * Z.of_nat n)))) /\
  (forall version mb origin first last,
    238 <= origin <= 4966 ->
    Mem.load Mfloat32 first mb 64 = Some (Vsingle (rank9cf_integer origin)) ->
    Rank10HDescentCalls version mb origin 11 first last ->
    Mem.load Mfloat32 last mb 64 <> Some (Vsingle (rank9cf_integer origin))).
Theorem rank10h_ground_hold_boundary_checked : Rank10AGroundHoldBoundary.
Proof. split; [exact rank10h_every_contracted_descent_realigns|
  exact rank10h_eleven_descent_hold_impossible]. Qed.
