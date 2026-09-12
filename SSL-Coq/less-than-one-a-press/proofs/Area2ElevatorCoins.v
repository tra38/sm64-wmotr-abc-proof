(** Coins at the elevator, rather than at the second-pole shaft.
    The fixed-layout exclusion and the conditional mobile-coin floor write
    are deliberately separate. No Goomba transport, live floor-list answer,
    full coin update, tangibility, or controller installation is assumed proved. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area1FirstNull
  Area2Rank9AStarGeometry Area2Rank9ACoinProducers Area2Rank9ACoinLaunch
  Area2Rank10ASupportChange InkVerticalRetryGeometry EyerokRank15LiveMovement
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

(** The full base footprint, enlarged by 150 on every side. This even
    exceeds the ordinary 100+37 coin/Mario contact radii. The theorem below
    is about coordinates, not preservation of the live objects' positions. *)
Definition ec_near_base x z := -661 <= x <= 662 /\ -405 <= z <= 918.
Definition ec_outside record := match record with
| [_; x; _; z; _] =>
    negb ((-661 <=? x) && (x <=? 662) && (-405 <=? z) && (z <=? 918))
| _ => false end.
Definition ec_fixed_records version := rank9a_individual_coin_records version ++
  rank9ac_records_for version R9CP._bhvHiddenBlueCoin.

Theorem ec_fixed_layout_checked : forall version,
  length (ec_fixed_records version) = 18%nat /\
  forallb ec_outside (ec_fixed_records version) = true.
Proof. intros []; vm_compute; split; reflexivity. Qed.

Theorem ec_fixed_record_excludes_base : forall version tag x y z parameter,
  In [tag;x;y;z;parameter] (ec_fixed_records version) -> ~ ec_near_base x z.
Proof.
  intros version tag x y z parameter Hin Hnear.
  pose proof (proj2 (ec_fixed_layout_checked version)) as H.
  rewrite forallb_forall in H. specialize (H _ Hin).
  unfold ec_outside in H. unfold ec_near_base in Hnear.
  apply negb_true_iff in H. repeat rewrite andb_false_iff in H.
  repeat destruct H as [H|H]; apply Z.leb_gt in H; lia.
Qed.

(** All stock row/ring offsets fit 320 per horizontal axis. The concrete
    formation diagnostic checks their generated recipes/trig values. This
    implication exposes the bound; it is not a live transform/frame theorem. *)
Theorem ec_formation_offsets_exclude_base :
  forall tag x y z parameter dx dz,
  In [tag;x;y;z;parameter] rank9ac_formation_records ->
  -320 <= dx <= 320 -> -320 <= dz <= 320 ->
  ~ ec_near_base (x+dx) (z+dz).
Proof.
  intros tag x y z parameter dx dz Hin Hx Hz Hnear.
  unfold ec_near_base in Hnear. cbn in Hin.
  repeat destruct Hin as [H|Hin]; try contradiction;
    inversion H; subst; lia.
Qed.

(** A bottom-position geometric candidate. Translation is explicit, not a
    theorem that the live elevator has loaded these vertices this frame. *)
Definition ec_bottom_vertices version := map
  (fun '(x,y,z) => (x,y+128,z+256)) (rank10s_elevator_vertices version).
Definition ec_base_faces := [(0,1,2);(0,2,3)].
Definition ec_query y : Area1IntegerQuery :=
  {| area1_query_x := 0; area1_query_y := y; area1_query_z := 256 |}.
Definition ec_base_hits version y :=
  filter (ivr_accepts (ec_bottom_vertices version) (ec_query y)) ec_base_faces.

Theorem ec_below_base_query_checked : forall version,
  firstn 2 (skipn 10 (rank10s_elevator_indices version)) = ec_base_faces /\
  ec_base_hits version 49 = [] /\
  ec_base_hits version 50 = [(0,2,3)] /\
  ec_base_hits version 64 = [(0,2,3)] /\
  option_map (fun h => Int.unsigned (Float32.to_bits h))
    (area1_loaded_floor_height (ec_bottom_vertices version) (0,2,3) 0 256) =
    Some 1124073472.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

(** Extract the actual copy inside the TRUE posY < floorHeight arm, after
    its landed/on-ground flag handling. Those preceding calls and the list
    query are outside this local execution, not blanket-framed away. *)
Definition ec_ground_air_body version := match version with
| VersionUS => us_object_helpers.f_cur_obj_move_update_ground_air_flags
| VersionJP => jp_object_helpers.f_cur_obj_move_update_ground_air_flags end.
Definition ec_snap_from_body version := match fn_body (ec_ground_air_body version) with
| Ssequence _ (Ssequence
    (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
      (Sifthenelse _ (Ssequence _ (Ssequence snap _)) _))))) _) => snap
| _ => Sskip end.
Definition ec_snap version :=
  Ssequence (Sset R9CH._t'27 rank15_current_object_expression)
  (Ssequence (Sset R9CH._t'28 rank15_current_object_expression)
  (Ssequence (Sset R9CH._t'29
    (rank15_raw_float_expression version R9CH._t'28
      (Econst_int (Int.repr 24) tint)))
    (Sassign (rank15_raw_float_expression version R9CH._t'27 rank15_y_index)
      (Etempvar R9CH._t'29 tfloat)))).
Theorem ec_snap_is_generated : forall version,
  ec_snap_from_body version = ec_snap version.
Proof. intros []; reflexivity. Qed.
Definition ec_snap_locals le object height :=
  PTree.set R9CH._t'29 (Vsingle height)
    (PTree.set R9CH._t'28 object (PTree.set R9CH._t'27 object le)).

Definition ElevatorCoinSnapExecution : Prop :=
  forall version e le m cb ob oo height,
  e ! R9CH._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    R9CH._gCurrentObject = Some cb ->
  Mem.load Mptr m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 24))) =
    Some (Vsingle height) ->
  Mem.valid_access m Mfloat32 ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 7))) Writable ->
  exists after,
    ClightBigstep.Clight2.exec_stmt
      (Clight.globalenv (selected_clight_target version)) e le m
      (ec_snap_from_body version) E0 (ec_snap_locals le (Vptr ob oo) height)
      after Out_normal /\
    Mem.load Mfloat32 after ob
      (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 7))) = Some (Vsingle height) /\
    (forall chunk rb ro,
      rb <> ob \/ ro + size_chunk chunk <=
        Ptrofs.unsigned (rank15_raw_address oo (Int.repr 7)) \/
      Ptrofs.unsigned (rank15_raw_address oo (Int.repr 7)) + 4 <= ro ->
      Mem.load chunk after rb ro = Mem.load chunk m rb ro).

Theorem ec_real_snap_writes_selected_height : ElevatorCoinSnapExecution.
Proof.
  intros version e le m cb ob oo height Hlocal Hsymbol Hcurrent Hheight Haccess.
  destruct (Mem.valid_access_store m Mfloat32 ob
    (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 7))) (Vsingle height) Haccess)
    as [after Hstore].
  exists after. split.
  - rewrite ec_snap_is_generated. unfold ec_snap, ec_snap_locals.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply rank15_current_object_read; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply rank15_current_object_read; eauto.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_Sset. eapply rank15_raw_float_read.
           ++ apply PTree.gss.
           ++ constructor.
           ++ reflexivity.
           ++ exact Hheight.
        -- eapply exec_Sassign with (loc := ob)
             (ofs := rank15_raw_address oo (Int.repr 7)) (bf := Full)
             (v := Vsingle height) (v2 := Vsingle height).
           ++ eapply rank15_raw_float_lvalue.
              ** repeat rewrite PTree.gso by discriminate. apply PTree.gss.
              ** apply rank15_y_index_evaluates.
              ** reflexivity.
           ++ apply eval_Etempvar. apply PTree.gss.
           ++ reflexivity.
           ++ eapply assign_loc_value with (chunk := Mfloat32);
                [reflexivity|exact Hstore].
  - split.
    + exact (Mem.load_store_same _ _ _ _ _ _ Hstore).
    + intros chunk rb ro Hsep. eapply Mem.load_store_other; [exact Hstore|].
      destruct Hsep as [H|[H|H]]; auto.
Qed.

(** Unlike Mario's find_floor alone, the later object movement has an actual
    Y write. In this arithmetic example gravity changes 24 to 20, and 64+20
    is still below a selected base at 128, so that branch's comparison is true.
    This is not a claim that an ordinary RNG history installs this pose. *)
Theorem ec_upward_snap_arithmetic_checked :
  Float32.to_bits (Float32.add (area1_f32_of_Z 24) (area1_f32_of_Z (-4))) =
    Float32.to_bits (area1_f32_of_Z 20) /\
  Float32.cmp Clt
    (Float32.add (area1_f32_of_Z 64) (area1_f32_of_Z 20))
    (area1_f32_of_Z 128) = true.
Proof. vm_compute; split; reflexivity. Qed.

Definition Area2ElevatorCoinBoundary : Prop :=
  (forall version, length (ec_fixed_records version) = 18%nat /\
    forallb ec_outside (ec_fixed_records version) = true) /\
  (forall tag x y z parameter dx dz,
    In [tag;x;y;z;parameter] rank9ac_formation_records ->
    -320 <= dx <= 320 -> -320 <= dz <= 320 ->
    ~ ec_near_base (x+dx) (z+dz)) /\
  (forall version,
    ec_base_hits version 49 = [] /\ ec_base_hits version 50 = [(0,2,3)] /\
    ec_base_hits version 64 = [(0,2,3)]) /\
  ElevatorCoinSnapExecution.
Theorem ec_elevator_coin_boundary_checked : Area2ElevatorCoinBoundary.
Proof.
  split; [exact ec_fixed_layout_checked|].
  split; [exact ec_formation_offsets_exclude_base|].
  split; [|exact ec_real_snap_writes_selected_height].
  intro version. pose proof (ec_below_base_query_checked version) as (_ & H & H1 & H2 & _).
  auto.
Qed.
