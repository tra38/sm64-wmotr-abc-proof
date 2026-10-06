(** Connect the REAL classifier call, its returned memory, the generated
    handler continuation and the first bounce snap. No equality of separated
    guard/bounce reads is assumed. The live height ceiling is still explicit;
    deriving it through all earlier actor histories is a different claim. *)
From Coq Require Import List Lia ZArith Reals.
From compcert Require Import AST Clight ClightBigstep Clightdefs Events Floats
  Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBounceDetermineEntry
  InkBounceReadContinuity InkBounceProducerEffect InkBounceApproachGap
  InkRawCopyStores EyerokRank15LiveMovement Area2Rank9ACoinFlight
  ObjectContactNecessity SelectedClightTarget OrdinaryArea1EntryMemory
  InkFloorResetExecution InkFlyGuyCycleHeight.
Local Open Scope Z_scope.

Definition InkBounceLiveReadBoundary : Prop :=
  forall version kind e le before mb ob slot movement_y actor_y height
    call_t call_le returned call_out continuation_t final_le after final_out,
  (slot < object_pool_capacity)%nat -> mb <> ob ->
  e ! BRC._determine_interaction = None -> e ! BRC._attack_object = None ->
  e ! BRC._bounce_back_from_attack = None -> e ! BRC._bounce_off_object = None ->
  le ! BRC._m = Some (Vptr mb Ptrofs.zero) ->
  le ! BRC._o = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le before
    ibrc_classifier_call call_t call_le returned call_out ->
  call_le ! BRC._t'1 = Some (Vint (Int.repr 64)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e call_le returned
    (ibrc_return_to_attack version kind) continuation_t final_le after final_out ->
  Mem.load Mfloat32 returned mb 64 = Some (Vsingle movement_y) ->
  Mem.load Mfloat32 returned ob (object_slot_offset slot + 164) = Some (Vsingle actor_y) ->
  Mem.load Mfloat32 returned ob (object_slot_offset slot + 508) = Some (Vsingle height) ->
  rank9cf_finite movement_y -> rank9cf_finite actor_y -> rank9cf_finite height ->
  rank9cf_finite (Float32.add actor_y height) ->
  (-32768 <= rank9cf_real movement_y <= 32768)%R ->
  (-32768 <= rank9cf_real actor_y)%R -> (rank9cf_real height <= 250)%R ->
  exists bounce_m snap_m,
    Mem.load Mfloat32 bounce_m mb 64 = Some (Vsingle movement_y) /\
    Mem.store Mfloat32 bounce_m mb 64 (Vsingle (Float32.add actor_y height)) = Some snap_m /\
    Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle (Float32.add actor_y height)) /\
    (rank9cf_real (Float32.add actor_y height) - rank9cf_real movement_y <= 251)%R /\
    (forall chunk b offset, b <> mb -> ibrc_outside_status ob slot chunk b offset ->
      Mem.load chunk snap_m b offset = Mem.load chunk returned b offset).

Theorem iblr_real_classifier_through_bounce_has_at_most_251_new_rise :
  InkBounceLiveReadBoundary.
Proof.
  intros version kind e le before mb ob slot movement_y actor_y height
    call_t call_le returned call_out continuation_t final_le after final_out
    Hslot Hsep Hname Hattack Hback Hbounce Hm Ho Hcall H64 Hcontinuation
    Hmovement Hactor Hheight Fmovement Factor Fheight Fsum Bmovement Bactor Bheight.
  destruct (ibrc_real_classifier_return64_connects_to_attacked_cut
    version kind e le before mb Ptrofs.zero ob (Ptrofs.repr (object_slot_offset slot))
    call_t call_le returned call_out continuation_t final_le after final_out
    Hname Hm Ho Hcall H64 Hcontinuation)
    as [Hreal (branch_t & branch_le & branch_m & branch_out & Hbranch)].
  assert (Float32.cmp Cgt movement_y actor_y = true) as Hcmp.
  { eapply ibde_completed_above_classifier_reads_actual_return_heights;
      [exact Hreal|exact Hmovement|].
    rewrite ibrc_slot_address by (auto; lia). exact Hactor. }
  assert (call_le ! BRC._m = Some (Vptr mb Ptrofs.zero)) as HcallM.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ BRC._m Hcall eq_refl). exact Hm. }
  assert (call_le ! BRC._o = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HcallO.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ BRC._o Hcall eq_refl). exact Ho. }
  destruct (ibrc_real_handler_reaches_exact_first_snap version kind e
    (PTree.set BRC._interaction (Vint (Int.repr 64)) call_le) returned mb ob slot
    movement_y actor_y height branch_t branch_le branch_m branch_out
    Hslot Hsep Hattack Hback Hbounce
    ltac:(rewrite PTree.gso by discriminate; exact HcallM)
    ltac:(rewrite PTree.gso by discriminate; exact HcallO)
    (PTree.gss _ _ _) Hmovement Hactor Hheight Hbranch)
    as (bounce_m & bits & bounce_t & bounced & result & start_le & snap_le & snap_m &
      final_locals & tail_out & Hbits & Hentry & HbounceCall & Hsnap & Hstore &
      Hload & Hframe & Htail).
  pose proof (ifch_signed_snap_rise_is_at_most_251 movement_y actor_y height
    Fmovement Factor Fheight Bmovement Bactor Bheight Fsum Hcmp) as Hbound.
  exists bounce_m, snap_m. repeat split; assumption.
Qed.
