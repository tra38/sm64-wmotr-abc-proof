(** Finite certificate for the ordered floor snapshot from the conditional JP
    vertical-retry fixture. The scalar expressions below are EXTRACTED from
    the actual generated US/JP floor bodies and evaluated with CompCert's
    operators. This is not a replacement program or a proof that arbitrary
    gameplay has this memory. check.py ties the data block to the recorded
    linked lists; the runtime receipt separately observes the actual calls,
    capture, retention and first Area-2 apply. *)
From Coq Require Import Bool List PeanoNat ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Floats Integers
  Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes UpperElevatorQueryResolution
  InkVerticalRetryGeometry Area1FirstNull Timer131Surface CollisionMeshFacts.
Import ListNotations.
Local Open Scope Z_scope.
Module IVL := UEQR_UC.

(** A small evaluator for scalar expression cuts, with a semantic soundness
    proof. Memory loads, calls and control flow are deliberately unsupported. *)
Fixpoint ivl_scalar (ce : composite_env) (le : temp_env) (m : mem)
    (a : expr) : option val :=
  match a with
  | Econst_int i _ => Some (Vint i)
  | Econst_single f _ => Some (Vsingle f)
  | Etempvar id _ => le ! id
  | Eunop op a _ =>
      match ivl_scalar ce le m a with
      | Some v => sem_unary_operation op v (typeof a) m | None => None end
  | Ebinop op a b _ =>
      match ivl_scalar ce le m a, ivl_scalar ce le m b with
      | Some va, Some vb => sem_binary_operation ce op va (typeof a) vb (typeof b) m
      | _, _ => None end
  | Ecast a ty =>
      match ivl_scalar ce le m a with
      | Some v => sem_cast v (typeof a) ty m | None => None end
  | _ => None
  end.

Lemma ivl_scalar_sound : forall ge e le m a v,
  ivl_scalar (genv_cenv ge) le m a = Some v -> eval_expr ge e le m a v.
Proof.
  intros ge e le m a. induction a; intros v H; cbn [ivl_scalar] in H;
    try discriminate; try solve [inversion H; constructor];
    try solve [constructor; exact H].
  - destruct (ivl_scalar (genv_cenv ge) le m a) eqn:Ha; try discriminate.
    eapply eval_Eunop; eauto.
  - destruct (ivl_scalar (genv_cenv ge) le m a1) eqn:Ha; try discriminate.
    destruct (ivl_scalar (genv_cenv ge) le m a2) eqn:Hb; try discriminate.
    eapply eval_Ebinop; eauto.
  - destruct (ivl_scalar (genv_cenv ge) le m a) eqn:Ha; try discriminate.
    eapply eval_Ecast; eauto.
Qed.

Fixpoint ivl_flat (s : statement) : list statement :=
  match s with Ssequence a b => ivl_flat a ++ ivl_flat b | _ => [s] end.
Definition ivl_iteration version :=
  match fn_body (ueqr_native_body version UEQRFindFloorFromList) with
  | Ssequence _ (Ssequence (Sloop (Ssequence _ body) _) _) => ivl_flat body
  | _ => [] end.
Definition ivl_stmt version n := nth n (ivl_iteration version) Sskip.
Definition ivl_guard s := match s with
  | Sifthenelse a _ _ => a | _ => Econst_int Int.one tint end.
Definition ivl_rhs s := match s with
  | Sset _ a => a | _ => Econst_int Int.one tint end.
Definition ivl_camera_branch version := match ivl_stmt version 12 with
  | Sifthenelse _ yes _ => ivl_guard (nth 1 (ivl_flat yes) Sskip)
  | _ => Econst_int Int.one tint end.
Definition ivl_mario_branch version := match ivl_stmt version 12 with
  | Sifthenelse _ _ no => ivl_guard (nth 1 (ivl_flat no) Sskip)
  | _ => Econst_int Int.one tint end.

(** Validate the exact expression cuts and acceptance tail in both bodies.
    Early rejection precedes the height calculation; the first acceptance
    stores height, selects that surface, and breaks the traversal. *)
Definition InkVerticalFloorCuts : Prop := forall version,
  length (ivl_iteration version) = 23%nat /\
  map (ivl_stmt version) [6%nat; 9%nat; 10%nat; 17%nat; 19%nat] =
    map (fun n => Sifthenelse (ivl_guard (ivl_stmt version n)) Scontinue Sskip)
      [6%nat; 9%nat; 10%nat; 17%nat; 19%nat] /\
  ivl_stmt version 18 = Sset IVL._height (ivl_rhs (ivl_stmt version 18)) /\
  skipn 20 (ivl_iteration version) =
    [Sassign (Ederef (Etempvar IVL._pheight (tptr tfloat)) tfloat)
       (Etempvar IVL._height tfloat);
     Sset IVL._floor (Etempvar IVL._surf (tptr (Tstruct IVL._Surface noattr)));
     Sbreak].
Lemma ivl_source_cuts : InkVerticalFloorCuts.
Proof. intros []; repeat split; reflexivity. Qed.

Record IVLSurface := {
  ivl_pointer : Z; ivl_type : Z; ivl_flags : Z;
  ivl_a : Area1SourceVertex; ivl_b : Area1SourceVertex; ivl_c : Area1SourceVertex;
  ivl_plane : Z * Z * Z * Z; ivl_owner : Z
}.
Definition ivl_row := Build_IVLSurface.

(* BEGIN CHECKED SNAPSHOT DATA *)
Definition ivl_dynamic : list IVLSurface := [
  ivl_row 2149169792 53 1
    (-2297, 1528, -1715) (-2779, 1528, -812) (-2087, 2039, -1023)
    (3206524120, 1060440647, 3198842415, 3309356130) 2150912504;
  ivl_row 2149169840 53 1
    (-2779, 1528, -812) (-1877, 1528, -330) (-2087, 2039, -1023)
    (3198839832, 1060453594, 1059026467, 3300630343) 2150912504;
  ivl_row 2149169936 53 1
    (-1877, 1528, -330) (-1395, 1528, -1232) (-2087, 2039, -1023)
    (1059030667, 1060448841, 1051360672, 1128674320) 2150912504;
  ivl_row 2149169984 53 1
    (-1395, 1528, -1232) (-2297, 1528, -1715) (-2087, 2039, -1023)
    (1051388686, 1060438263, 3206518827, 3299661652) 2150912504
].

Definition ivl_static : list IVLSurface := [
  ivl_row 2149152080 48 0
    (-1945, 1280, -921) (-2149, 1280, -921) (-2176, 1280, -639)
    (0, 1065353216, 0, 3298820096) 0;
  ivl_row 2149152128 48 0
    (-1945, 1280, -921) (-2176, 1280, -639) (-1920, 1280, -639)
    (0, 1065353215, 0, 3298820095) 0;
  ivl_row 2149152320 48 0
    (-2559, 1280, -511) (-2149, 1280, -1125) (-2559, 1280, -1535)
    (0, 1065353216, 0, 3298820096) 0;
  ivl_row 2149152368 48 0
    (-2559, 1280, -511) (-2149, 1280, -921) (-2149, 1280, -1125)
    (0, 1065353216, 0, 3298820096) 0;
  ivl_row 2149152416 48 0
    (-2149, 1280, -921) (-2559, 1280, -511) (-2176, 1280, -511)
    (0, 1065353216, 0, 3298820096) 0;
  ivl_row 2149164560 53 0
    (-2176, 1280, -511) (-2559, 1280, -511) (-2736, 1103, -334)
    (0, 1060439283, 1060439283, 3288854776) 0;
  ivl_row 2149164848 53 0
    (-2176, 1280, -511) (-2736, 1103, -334) (-2176, 1103, -334)
    (0, 1060439284, 1060439284, 3288854776) 0;
  ivl_row 2149151456 48 0
    (-1920, 1103, -639) (-2176, 1103, -639) (-2176, 1103, -334)
    (0, 1065353216, 0, 3297370112) 0;
  ivl_row 2149151504 48 0
    (-1920, 1103, -639) (-2176, 1103, -334) (-1920, 1103, -334)
    (0, 1065353216, 0, 3297370112) 0;
  ivl_row 2149151600 48 0
    (-2736, 1103, -334) (-1919, 1103, -255) (-1920, 1103, -334)
    (0, 1065353216, 0, 3297370112) 0;
  ivl_row 2149151792 48 0
    (-2736, 1103, -334) (-2736, 1103, -255) (-1919, 1103, -255)
    (0, 1065353216, 0, 3297370112) 0;
  ivl_row 2149150160 48 0
    (-2815, 1024, -255) (-2815, 1024, -1791) (-2943, 1024, -1791)
    (0, 1065353216, 0, 3296722944) 0;
  ivl_row 2149150304 48 0
    (-2815, 1024, -255) (-2943, 1024, -1791) (-2943, 1024, -255)
    (0, 1065353216, 0, 3296722944) 0;
  ivl_row 2149163984 53 0
    (-2815, 1024, -255) (-2736, 1103, -255) (-2736, 1103, -334)
    (3207922932, 1060439284, 0, 3307841876) 0;
  ivl_row 2149164176 53 0
    (-2815, 1024, -255) (-2559, 1280, -1535) (-2815, 1024, -1791)
    (3207922932, 1060439284, 0, 3307841876) 0;
  ivl_row 2149164224 53 0
    (-2815, 1024, -255) (-2559, 1280, -511) (-2559, 1280, -1535)
    (3207922931, 1060439283, 0, 3307841876) 0;
  ivl_row 2149163936 53 0
    (-2943, 896, -127) (-2815, 1024, -255) (-2943, 1024, -255)
    (0, 1060439283, 1060439283, 3288854776) 0;
  ivl_row 2149146032 40 0
    (-1945, 768, -921) (-1945, 768, -1125) (-2149, 768, -1125)
    (0, 1065353216, 0, 3292528640) 0;
  ivl_row 2149146272 40 0
    (-1945, 768, -921) (-2149, 768, -1125) (-2149, 768, -921)
    (0, 1065353216, 0, 3292528640) 0;
  ivl_row 2149164896 53 0
    (-2175, 437, 331) (-1279, 1024, -255) (-2815, 1024, -255)
    (0, 1060429166, 1060449393, 3288842140) 0;
  ivl_row 2149164944 53 0
    (-2175, 437, 331) (-1919, 437, 331) (-1279, 1024, -255)
    (0, 1060429165, 1060449392, 3288842140) 0;
  ivl_row 2149165136 53 0
    (-3583, 256, 512) (-2175, 437, 331) (-2815, 1024, -255)
    (957253031, 1060430410, 1060448149, 3288837426) 0;
  ivl_row 2149150832 48 0
    (-1919, 0, 165) (-1919, 0, -52) (-2175, 0, -52)
    (0, 1065353216, 0, 2147483648) 0;
  ivl_row 2149150880 48 0
    (-1919, 0, 165) (-2175, 0, -52) (-2175, 0, 165)
    (0, 1065353216, 0, 2147483648) 0;
  ivl_row 2149164464 53 0
    (-4095, -255, -3071) (-2943, 896, -127) (-2943, 896, -1919)
    (3207917779, 1060444433, 0, 3307839300) 0;
  ivl_row 2149164512 53 0
    (-4095, -255, -3071) (-4095, -255, 1024) (-2943, 896, -127)
    (3207917778, 1060444432, 0, 3307839300) 0
].
(* END CHECKED SNAPSHOT DATA *)

Definition ivl_single bits := Vsingle (Float32.of_bits (Int.repr bits)).
Definition ivl_temps y s : temp_env :=
  let '(ax, _, az) := ivl_a s in
  let '(bx, _, bz) := ivl_b s in
  let '(cx, _, cz) := ivl_c s in
  let '(nx, ny, nz, oo) := ivl_plane s in
  fold_right (fun pair le => PTree.set (fst pair) (snd pair) le) (PTree.empty val)
    [(IVL._x, Vint (Int.repr (-2200))); (IVL._y, Vint (Int.repr y));
     (IVL._z, Vint (Int.repr (-1024)));
     (IVL._x1, Vint (Int.repr ax)); (IVL._z1, Vint (Int.repr az));
     (IVL._x2, Vint (Int.repr bx)); (IVL._z2, Vint (Int.repr bz));
     (IVL._x3, Vint (Int.repr cx)); (IVL._z3, Vint (Int.repr cz));
     (IVL._nx, ivl_single nx); (IVL._ny, ivl_single ny);
     (IVL._nz, ivl_single nz); (IVL._oo, ivl_single oo);
     (IVL._t'2, Vint (Int.repr (ivl_type s)));
     (IVL._t'3, Vint (Int.repr (ivl_flags s)))].
Definition ivl_eval le a := ivl_scalar (PTree.empty composite) le Mem.empty a.
Definition ivl_false le a := match ivl_eval le a with
  | Some (Vint i) => Int.eq i Int.zero | _ => false end.

Definition ivl_hit version y s : option (Z * Z * Z) :=
  let le := ivl_temps y s in
  if forallb (fun n => ivl_false le (ivl_guard (ivl_stmt version n)))
       [6%nat; 9%nat; 10%nat; 17%nat] &&
     ivl_false le (ivl_camera_branch version) && ivl_false le (ivl_mario_branch version)
  then match ivl_eval le (ivl_rhs (ivl_stmt version 18)) with
       | Some (Vsingle height) =>
           if ivl_false (PTree.set IVL._height (Vsingle height) le)
                (ivl_guard (ivl_stmt version 19))
           then Some (ivl_pointer s, Int.unsigned (Float32.to_bits height), ivl_owner s)
           else None
       | _ => None end
  else None.

(** Ordered finite scan of the receipt. All tests are the extracted scalar
    cuts above. Requiring both camera filters to pass avoids granting a
    camera-mode value; every potentially accepted recorded face passes both. *)
Fixpoint ivl_first version y floors := match floors with
  | [] => None
  | s :: rest => match ivl_hit version y s with
      | Some result => Some result | None => ivl_first version y rest end
  end.

Definition ivl_vertices s := (ivl_a s, ivl_b s, ivl_c s).

(** The live triangle order matches the already checked generated meshes.
    The selected top plane is also exactly the checked timer-131 plane. *)
Definition InkVerticalSnapshotMeshes : Prop :=
  map (fun s => Some (ivl_vertices s)) ivl_dynamic =
    map (area1_source_triangle_vertices timer131_vertices_s16) ivr_top_floors /\
  map (fun s => Some (ivl_vertices s)) ivl_static =
    map (area1_source_triangle_vertices area1_collision_vertices_jp)
      area1_q_static_floor_candidates_computed_jp /\
  Some (ivl_plane (hd (ivl_row 0 0 0 (0,0,0) (0,0,0) (0,0,0) (0,0,0,0) 0)
    ivl_dynamic)) = area1_loaded_plane_bits timer131_vertices_s16 timer131_state_face.
Theorem ivl_snapshot_matches_checked_meshes : InkVerticalSnapshotMeshes.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition InkVerticalSnapshotSelection : Prop := forall version,
  ivl_first version 768 ivl_dynamic = None /\
  ivl_first version 768 ivl_static = None /\
  ivl_first version 1938 ivl_dynamic = Some (2149169792, 1156733869, 2150912504) /\
  ivl_first version 1938 ivl_static = Some (2149152368, 1151336448, 0).

Theorem ivl_snapshot_queries_checked : InkVerticalSnapshotSelection.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Definition ivl_gt_statement s := match s with
  | Sifthenelse (Ebinop Ogt _ _ _) _ _ => true | _ => false end.
Definition ivl_comparison_statement version := hd Sskip (filter ivl_gt_statement
  (ivl_flat (fn_body (ueqr_native_body version UEQRFindFloor)))).
Definition ivl_comparison version := ivl_guard (ivl_comparison_statement version).
Definition ivl_comparison_temps le :=
  PTree.set IVL._t'9 (ivl_single 1156733869)
    (PTree.set IVL._t'10 (ivl_single 1151336448) le).

Lemma ivl_comparison_source : forall version,
  ivl_comparison_statement version =
  Sifthenelse (Ebinop Ogt (Etempvar IVL._t'9 tfloat) (Etempvar IVL._t'10 tfloat) tint)
    (Ssequence
      (Sset IVL._floor (Etempvar IVL._dynamicFloor (tptr (Tstruct IVL._Surface noattr))))
      (Ssequence (Sset IVL._t'11 (Evar IVL._dynamicHeight tfloat))
        (Sassign (Evar IVL._height tfloat) (Etempvar IVL._t'11 tfloat)))) Sskip.
Proof. intros []; reflexivity. Qed.

(** Once the two recorded list heights have been read, the real Clight
    comparison takes the branch selecting the dynamic floor. This semantic
    expression result does not assume that the whole callee has executed. *)
Definition InkVerticalComparisonTaken : Prop := forall version ge e le m,
  eval_expr ge e (ivl_comparison_temps le) m (ivl_comparison version) (Vint Int.one).
Theorem ivl_top_wins_real_comparison : InkVerticalComparisonTaken.
Proof.
  intros version ge e le m. unfold ivl_comparison.
  rewrite ivl_comparison_source. cbn [ivl_guard].
  eapply eval_Ebinop with (v1 := ivl_single 1156733869) (v2 := ivl_single 1151336448).
  - apply eval_Etempvar. apply PTree.gss.
  - apply eval_Etempvar. unfold ivl_comparison_temps.
    rewrite PTree.gso by discriminate. apply PTree.gss.
  - reflexivity.
Qed.

(** A backward arithmetic target, NOT a constructed dialog history. At this
    X/Z the supported static height is 1280, rather than the floorless 768.
    With depth -0.5, 1318 uninterrupted applications of the already-proved
    sink subtraction raise display from 1280 to 1939. That nearby height
    still selects the same top and is within four units of it. This supplies
    neither the negative seed nor the missing 512-unit actual-position drop. *)
Definition ivl_supported_wait_height := Nat.iter 1318
  (fun height => Float32.sub height (Float32.of_bits (Int.repr 3204448256)))
  (area1_f32_of_Z 1280).
Definition InkVerticalBackwardNumbers : Prop :=
  Int.unsigned (Float32.to_bits ivl_supported_wait_height) = 1156734976 /\
  Float32.cmp Clt
    (Float32.sub (area1_f32_of_Z 1939) ivr_contact_height) (area1_f32_of_Z 4) = true /\
  Float32.cmp Cge (area1_f32_of_Z 1939) ivr_contact_height = true /\
  1280 - 768 = 512 /\
  (forall version,
    ivl_first version 1280 ivl_dynamic = None /\
    ivl_first version 1280 ivl_static = Some (2149152368, 1151336448, 0) /\
    ivl_first version 1939 ivl_dynamic = Some (2149169792, 1156733869, 2150912504)).

Theorem ivl_backward_numbers_checked : InkVerticalBackwardNumbers.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [reflexivity|]. intros []; vm_compute; repeat split; reflexivity.
Qed.

Definition InkVerticalLiveSelectionBoundary : Prop :=
  InkVerticalFloorCuts /\ InkVerticalSnapshotMeshes /\
  InkVerticalSnapshotSelection /\ InkVerticalComparisonTaken /\ InkVerticalBackwardNumbers /\
  (forall ge e le m a v,
    ivl_scalar (genv_cenv ge) le m a = Some v -> eval_expr ge e le m a v).

Theorem ivl_vertical_live_selection_checked : InkVerticalLiveSelectionBoundary.
Proof.
  split; [exact ivl_source_cuts|].
  split; [exact ivl_snapshot_matches_checked_meshes|].
  split; [exact ivl_snapshot_queries_checked|].
  split; [exact ivl_top_wins_real_comparison|].
  split; [exact ivl_backward_numbers_checked|].
  exact ivl_scalar_sound.
Qed.
