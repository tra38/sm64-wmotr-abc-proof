From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight Clightdefs ClightBigstep Cop Ctypes
  Errors Events Globalenvs Integers Maps Memory Values.
From Pedro.Generated Require Import us_surface_load jp_surface_load.
From Pedro.Proofs Require Import GameTypes TTCCogExecution CogActionExecution
  CloneFloorExecution.
Import ListNotations.
Open Scope Z_scope.
Module CP := us_surface_load.

Definition clone_partition_function version : function :=
  match version with VersionUS => CP.f_clear_spatial_partition
                   | VersionJP => jp_surface_load.f_clear_spatial_partition end.

Definition clone_partition_writable memory partition : Prop :=
  forall index, 0 <= index < 768 ->
    Mem.valid_access memory Mptr partition (8 * index) Writable.
Definition clone_partition_heads_zero memory partition count : Prop :=
  forall index, 0 <= index < count ->
    Mem.load Mptr memory partition (8 * index) = Some (Vint Int.zero).

Definition clone_partition_layout_receipt : Prop :=
  forall version,
    let ce := prog_comp_env (match version with VersionUS => CP.prog
                            | VersionJP => jp_surface_load.prog end) in
    (match ce ! CP._SurfaceNode with
     | Some co => Some (co_sizeof co, field_offset ce CP._next (co_members co))
     | None => None end) = Some (8, OK (0, Full)) /\
    sizeof ce (tarray (tarray (tarray (Tstruct CP._SurfaceNode noattr) 3) 16) 16) = 6144.

Theorem clone_partition_layout_generated_us_jp : clone_partition_layout_receipt.
Proof. intros []; vm_compute; split; reflexivity. Qed.

Lemma clone_partition_store_access : forall before after partition index,
  Mem.store Mptr before partition (8 * index) (Vint Int.zero) = Some after ->
  clone_partition_writable before partition ->
  clone_partition_writable after partition.
Proof.
  intros before after partition index Hstore Haccess item Hbounds.
  eapply Mem.store_valid_access_1; [exact Hstore | apply Haccess; exact Hbounds].
Qed.

Lemma clone_partition_store_heads : forall before after partition index,
  Mem.store Mptr before partition (8 * index) (Vint Int.zero) = Some after ->
  clone_partition_heads_zero before partition index ->
  clone_partition_heads_zero after partition (index + 1).
Proof.
  intros before after partition index Hstore Hheads item Hbounds.
  destruct (Z.eq_dec item index) as [-> | Hdifferent].
  - rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore). reflexivity.
  - rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore).
    + apply Hheads. lia.
    + right. left. change (8 * item + 4 <= 8 * index). lia.
Qed.

Lemma clone_partition_decrement : forall remaining,
  (remaining < 256)%nat ->
  Int.sub (Int.repr (Z.of_nat (S remaining))) Int.one =
    Int.repr (Z.of_nat remaining).
Proof.
  intros remaining Hbound. unfold Int.sub.
  rewrite Int.unsigned_repr by (change (0 <= Z.of_nat (S remaining) <= 4294967295); lia).
  change (Int.repr (Z.of_nat (S remaining) - 1) = Int.repr (Z.of_nat remaining)).
  f_equal. lia.
Qed.

Lemma clone_partition_pointer_offset : forall index delta,
  0 <= index < 256 -> 0 <= delta <= 24 ->
  Ptrofs.unsigned (Ptrofs.add
    (Ptrofs.add (Ptrofs.repr (24 * index)) (Ptrofs.repr delta)) (Ptrofs.repr 0)) =
  24 * index + delta.
Proof.
  intros index delta Hindex Hdelta. rewrite Ptrofs.add_zero.
  unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (24 * index)) by (change (0 <= 24 * index <= 4294967295); lia).
  rewrite (Ptrofs.unsigned_repr delta) by (change (0 <= delta <= 4294967295); lia).
  rewrite Ptrofs.unsigned_repr by (change (0 <= 24 * index + delta <= 4294967295); lia).
  reflexivity.
Qed.

Lemma clone_partition_stride_words :
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 0)) = Ptrofs.repr 0 /\
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 1)) = Ptrofs.repr 8 /\
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 2)) = Ptrofs.repr 16 /\
  Ptrofs.mul (Ptrofs.repr 24) (Ptrofs.of_ints (Int.repr 1)) = Ptrofs.repr 24.
Proof. vm_compute; repeat split; reflexivity. Qed.

Ltac clone_partition_strides :=
  rewrite ?(proj1 clone_partition_stride_words),
    ?(proj1 (proj2 clone_partition_stride_words)),
    ?(proj1 (proj2 (proj2 clone_partition_stride_words))),
    ?(proj2 (proj2 (proj2 clone_partition_stride_words))).

Ltac clone_partition_store :=
  unfold Mem.storev;
  clone_partition_strides;
  lazymatch goal with
  | |- Mem.store _ _ _ (Ptrofs.unsigned
      (Ptrofs.add (Ptrofs.add (Ptrofs.repr (24 * ?index)) (Ptrofs.repr ?delta))
        (Ptrofs.repr 0))) _ = _ =>
      rewrite (clone_partition_pointer_offset index delta);
        [rewrite ?Z.add_0_r; clone_check ltac:(eassumption) | lia | lia]
  end.

Lemma clone_partition_next_pointer : forall index,
  0 <= index < 256 ->
  Ptrofs.add (Ptrofs.repr (24 * index)) (Ptrofs.repr 24) =
    Ptrofs.repr (24 * (index + 1)).
Proof.
  intros index Hindex. unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (24 * index)) by (change (0 <= 24 * index <= 4294967295); lia).
  change (Ptrofs.repr (24 * index + 24) = Ptrofs.repr (24 * (index + 1))).
  f_equal. lia.
Qed.

Lemma clone_partition_cell_size : forall ce co,
  ce ! CP._SurfaceNode = Some co -> co_sizeof co = 8 ->
  sizeof ce (tarray (Tstruct CP._SurfaceNode noattr) 3) = 24 /\
  sizeof ce (Tstruct CP._SurfaceNode noattr) = 8.
Proof.
  intros ce co Hnode Hsize.
  change ((match ce ! CP._SurfaceNode with Some c => co_sizeof c | None => 0 end) * 3 = 24 /\
    (match ce ! CP._SurfaceNode with Some c => co_sizeof c | None => 0 end) = 8).
  rewrite Hnode, Hsize. split; reflexivity.
Qed.

Ltac clone_partition_operation :=
  first [lazymatch goal with
    | |- sem_binary_operation _ Osub
        (Vint (Int.repr (Z.of_nat (S ?remaining)))) _ (Vint _) _ _ = ?result =>
        change (Some (Vint (Int.sub (Int.repr (Z.of_nat (S remaining))) Int.one)) = result);
        rewrite clone_partition_decrement by lia; reflexivity
    end |
  clone_check ltac:(
  cbn -[Int.sub Ptrofs.add Z.of_nat Z.mul Z.add Z.sub sizeof];
  repeat match goal with
    | H : sizeof _ _ = _ |- _ => progress rewrite H
    | H : (genv_cenv _) ! CP._SurfaceNode = Some _ |- _ => progress rewrite H
    | H : co_sizeof _ = 8 |- _ => progress rewrite H
  end; cbn -[Int.sub Ptrofs.add Z.of_nat Z.mul Z.add Z.sub sizeof];
  clone_partition_strides;
  repeat rewrite clone_partition_decrement by lia;
  try match goal with H : 0 <= ?index |- _ =>
    rewrite (clone_partition_next_pointer index) by lia end;
  first [reflexivity |
    unfold Ptrofs.add, Int.sub;
    repeat rewrite Ptrofs.unsigned_repr by (change (0 <= _ <= 4294967295); lia);
    repeat rewrite Int.unsigned_repr by (change (0 <= _ <= 4294967295); lia);
    cbn -[Z.mul Z.add Z.sub Z.of_nat];
    repeat f_equal; lia])].

Ltac clone_partition_expr :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ =>
      eapply eval_Etempvar;
      repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate];
      clone_check ltac:(first [eassumption | reflexivity])
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop;
        [clone_partition_expr | clone_partition_expr | clone_partition_operation]
  | |- eval_expr _ _ _ _ (Ecast _ _) _ =>
      eapply eval_Ecast; [clone_partition_expr | clone_partition_operation]
  | |- eval_expr _ _ _ _ _ _ =>
      eapply eval_Elvalue;
        [clone_partition_lvalue |
         first [eapply deref_loc_reference; reflexivity | eapply deref_loc_copy; reflexivity]]
  end
with clone_partition_lvalue :=
  lazymatch goal with
  | |- eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ =>
      eapply eval_Ederef; clone_partition_expr
  | |- eval_lvalue _ _ _ _ (Efield _ _ _) _ _ _ =>
      eapply eval_Efield_struct;
        [clone_partition_expr | reflexivity | eassumption | eassumption]
  end.

Ltac clone_partition_stmt :=
  lazymatch goal with |- exec_stmt ?entry ?ge ?e ?le ?m ?s ?t ?le' ?m' ?out =>
    let body := eval hnf in s in
    change (exec_stmt entry ge e le m body t le' m' out)
  end;
  lazymatch goal with
  | |- exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ Out_normal =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
        [clone_partition_stmt | clone_partition_stmt]
  | |- exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      first [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
               [clone_partition_stmt | clone_partition_stmt]
            |eapply exec_Sseq_2; [clone_partition_stmt | discriminate]]
  | |- exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse;
        [clone_partition_expr | clone_check ltac:(first [eassumption | cbn; reflexivity]) |
         cog_reduce_statement; clone_partition_stmt]
  | |- exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      eapply exec_Sset; clone_partition_expr
  | |- exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ =>
      eapply exec_Sassign;
        [clone_check clone_partition_lvalue | clone_partition_expr | reflexivity |
         eapply assign_loc_value; [reflexivity |
          clone_partition_store]]
  | |- exec_stmt _ _ _ _ _ Sskip _ _ _ _ => apply exec_Sskip
  | |- exec_stmt _ _ _ _ _ Sbreak _ _ _ _ => apply exec_Sbreak
  | _ => match goal with |- ?G => idtac "PARTITION STATEMENT" G end; fail 100
  end.

Definition clone_partition_loop : statement :=
  match fn_body CP.f_clear_spatial_partition with
  | Ssequence _ loop => loop | _ => Sskip end.

Lemma clone_partition_positive_bool : forall count memory,
  0 < count <= 256 ->
  bool_val (Vint (Int.repr count)) tint memory = Some true.
Proof.
  intros count memory Hbounds. cbn. rewrite Int.eq_false; [reflexivity |].
  intro Heq. apply (f_equal Int.unsigned) in Heq.
  rewrite Int.unsigned_repr in Heq by (change (0 <= count <= 4294967295); lia).
  change (count = 0) in Heq. lia.
Qed.

Definition clone_partition_step_locals locals partition index remaining :=
  PTree.set CP._cells (Vptr partition (Ptrofs.repr (24 * (index + 1))))
    (PTree.set CP._i (Vint (Int.repr remaining))
      (PTree.set CP._t'1 (Vint (Int.repr (remaining + 1))) locals)).

Lemma clone_partition_loop_exec : forall remaining (ge : Clight.genv) before
    partition node_co index locals,
  0 <= index -> index + Z.of_nat remaining <= 256 ->
  (genv_cenv ge) ! CP._SurfaceNode = Some node_co -> co_sizeof node_co = 8 ->
  field_offset (genv_cenv ge) CP._next (co_members node_co) = OK (0, Full) ->
  locals ! CP._i = Some (Vint (Int.repr (Z.of_nat remaining))) ->
  locals ! CP._cells = Some (Vptr partition (Ptrofs.repr (24 * index))) ->
  clone_partition_writable before partition ->
  clone_partition_heads_zero before partition (3 * index) ->
  exists after final_locals,
    exec_stmt function_entry2 ge (PTree.empty _) locals before
      clone_partition_loop E0 final_locals after Out_normal /\
    clone_partition_heads_zero after partition (3 * (index + Z.of_nat remaining)).
Proof.
  induction remaining as [|remaining IH]; intros ge before partition node_co index
    locals Hindex Hbound Hnode Hsize Hnext Hi Hcells Haccess Hheads.
  all: destruct (clone_partition_cell_size (genv_cenv ge) node_co Hnode Hsize)
    as [Hcell_size Hnode_size].
  - exists before. eexists. split.
    + unfold clone_partition_loop. eapply exec_Sloop_stop1 with (out' := Out_break).
      * clone_partition_stmt.
      * constructor.
    + replace (index + Z.of_nat 0) with index by lia. exact Hheads.
  - assert (Hpositive : bool_val (Vint (Int.repr (Z.of_nat (S remaining)))) tint before = Some true).
    { apply clone_partition_positive_bool. lia. }
    assert (Haccess0 : Mem.valid_access before Mptr partition (8 * (3 * index)) Writable).
    { apply Haccess. lia. }
    destruct (Mem.valid_access_store _ _ _ _ (Vint Int.zero) Haccess0) as [m1 Hstore0].
    pose proof (clone_partition_store_access _ _ _ _ Hstore0 Haccess) as Haccess1.
    pose proof (clone_partition_store_heads _ _ _ _ Hstore0 Hheads) as Hheads1.
    assert (Haccess2cell : Mem.valid_access m1 Mptr partition (8 * (3 * index + 1)) Writable).
    { apply Haccess1. lia. }
    destruct (Mem.valid_access_store _ _ _ _ (Vint Int.zero) Haccess2cell) as [m2 Hstore1].
    pose proof (clone_partition_store_access _ _ _ _ Hstore1 Haccess1) as Haccess2.
    pose proof (clone_partition_store_heads _ _ _ _ Hstore1 Hheads1) as Hheads2.
    assert (Haccess3cell : Mem.valid_access m2 Mptr partition (8 * (3 * index + 2)) Writable).
    { apply Haccess2. lia. }
    destruct (Mem.valid_access_store _ _ _ _ (Vint Int.zero) Haccess3cell) as [m3 Hstore2].
    pose proof (clone_partition_store_access _ _ _ _ Hstore2 Haccess2) as Haccess3.
    replace (3 * index + 1 + 1) with (3 * index + 2) in Hheads2 by lia.
    pose proof (clone_partition_store_heads _ _ _ _ Hstore2 Hheads2) as Hheads3.
    replace (3 * index + 2 + 1) with (3 * (index + 1)) in Hheads3 by lia.
    set (next_locals := clone_partition_step_locals locals partition index (Z.of_nat remaining)).
    assert (Hnexti : next_locals ! CP._i = Some (Vint (Int.repr (Z.of_nat remaining)))).
    { unfold next_locals, clone_partition_step_locals. rewrite PTree.gso by discriminate. apply PTree.gss. }
    assert (Hnextcells : next_locals ! CP._cells = Some (Vptr partition (Ptrofs.repr (24 * (index + 1))))).
    { apply PTree.gss. }
    destruct (IH ge m3 partition node_co (index + 1) next_locals)
      as [after [final_locals [Hexec Hfinal]]]; try eassumption; try lia.
    exists after, final_locals. split.
    + unfold clone_partition_loop in *.
      eapply exec_Sloop_loop with (out1 := Out_normal) (le1 := next_locals)
        (m1 := m3) (t1 := E0) (t2 := E0) (t3 := E0).
      * unfold next_locals, clone_partition_step_locals.
        replace (Z.of_nat remaining + 1) with (Z.of_nat (S remaining)) by lia.
        replace (8 * (3 * index)) with (24 * index) in Hstore0 by lia.
        replace (8 * (3 * index + 1)) with (24 * index + 8) in Hstore1 by lia.
        replace (8 * (3 * index + 2)) with (24 * index + 16) in Hstore2 by lia.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** eapply exec_Sset. clone_partition_expr.
              ** eapply exec_Sset with (v := Vint (Int.repr (Z.of_nat remaining))).
                 clone_partition_expr.
           ++ eapply exec_Sifthenelse with (b := true).
              ** clone_partition_expr.
              ** exact Hpositive.
              ** apply exec_Sskip.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ eapply exec_Sassign.
              ** clone_partition_lvalue.
              ** clone_partition_expr.
              ** reflexivity.
              ** eapply assign_loc_value; [reflexivity |].
                 unfold Mem.storev. clone_partition_strides.
                 rewrite (clone_partition_pointer_offset index 0).
                 --- rewrite Z.add_0_r. exact Hstore0.
                 --- lia.
                 --- lia.
           ++ timeout 20 clone_partition_stmt.
      * constructor.
      * constructor.
      * exact Hexec.
    + replace (index + Z.of_nat (S remaining)) with (index + 1 + Z.of_nat remaining) by lia.
      exact Hfinal.
Qed.

Definition clone_partition_clear_execution_claim version : Prop :=
  forall (ge : Clight.genv) before partition node_co,
    (genv_cenv ge) ! CP._SurfaceNode = Some node_co ->
    co_sizeof node_co = 8 ->
    field_offset (genv_cenv ge) CP._next (co_members node_co) = OK (0, Full) ->
    clone_partition_writable before partition ->
    exists after,
      eval_funcall function_entry2 ge before
        (Internal (clone_partition_function version)) [Vptr partition Ptrofs.zero]
        E0 after Vundef /\
      clone_partition_heads_zero after partition 768.

Theorem generated_clear_entire_partition_us_jp :
  forall version, clone_partition_clear_execution_claim version.
Proof.
  intros version ge before partition node_co Hnode Hsize Hnext Haccess.
  assert (Hheads : clone_partition_heads_zero before partition 0).
  { intros index Hbounds. lia. }
  set (locals := PTree.set CP._i (Vint (Int.repr 256))
    (PTree.set CP._cells (Vptr partition Ptrofs.zero)
      (PTree.set CP._i Vundef (PTree.set CP._t'1 Vundef (PTree.empty val))))).
  destruct (clone_partition_loop_exec 256 ge before partition node_co 0 locals)
    as [after [final_locals [Hexec Hfinal]]]; try assumption;
    try (unfold locals; cbn; reflexivity); try lia.
  exists after. split; [|exact Hfinal].
  assert (Hfunction : clone_partition_function version = CP.f_clear_spatial_partition)
    by (destruct version; reflexivity).
  rewrite Hfunction. eapply eval_funcall_internal.
  - action_entry.
  - simpl fn_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset with (v := Vint (Int.repr 256)). cog_expr.
    + exact Hexec.
  - cbn. reflexivity.
  - cbn. reflexivity.
Qed.

(** Compose the full clear with the actual list-search function. The null
    search head is derived from the clear's stores, not assumed. This is one
    partition before any new surfaces are published; it is not an exclusion
    of floors supplied by other lists or by subsequent terrain updates. *)
Definition clone_cleared_partition_query_claim version : Prop :=
  forall (ge : Clight.genv) before partition node_co,
    (genv_cenv ge) ! CP._SurfaceNode = Some node_co ->
    co_sizeof node_co = 8 ->
    field_offset (genv_cenv ge) CP._next (co_members node_co) = OK (0, Full) ->
    clone_partition_writable before partition ->
    exists after,
      eval_funcall function_entry2 ge before
        (Internal (clone_partition_function version)) [Vptr partition Ptrofs.zero]
        E0 after Vundef /\
      clone_partition_heads_zero after partition 768 /\
      (forall index head x y z height_pointer,
        0 <= index < 768 ->
        Mem.load Mptr after partition (8 * index) = Some head ->
        eval_funcall function_entry2 ge after
          (Internal (clone_floor_search_function version))
          [head; Vint x; Vint y; Vint z; height_pointer]
          E0 after (Vint Int.zero)).

Theorem generated_cleared_partition_has_no_floor_us_jp :
  forall version, clone_cleared_partition_query_claim version.
Proof.
  intros version ge before partition node_co Hnode Hsize Hnext Haccess.
  destruct (generated_clear_entire_partition_us_jp version ge before partition node_co
    Hnode Hsize Hnext Haccess) as [after [Hexec Hheads]].
  exists after. split; [exact Hexec |]. split; [exact Hheads |].
  intros index head x y z height_pointer Hindex Hload.
  rewrite (Hheads index Hindex) in Hload. inversion Hload; subst head.
  apply generated_empty_floor_list_returns_null_us_jp.
Qed.
