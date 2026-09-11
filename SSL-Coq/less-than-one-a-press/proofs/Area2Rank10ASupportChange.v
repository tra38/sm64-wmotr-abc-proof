(** Backward Rank-10A support search. The complete generated static mesh has
    no high floor inside the bucket; the base covers its interior and the rim
    does not. The actual find_floor arbitration reads both heights and writes
    the selected dynamic floor when its height dominates. These are separate
    geometric and execution facts: live loading, transforms, list membership,
    query acceptance and the rounded static-height bound remain obligations. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From Flocq Require Import Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area1FirstNull
  CollisionMeshFacts Area2ElevatorCut Area2DownstreamGeometry
  Area2Rank12BContact Area2Rank9ACoinFlight Area2Rank10AEntryChecks
  InkVerticalLiveSelection UpperElevatorQueryResolution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Float32.cmp Float32.compare.
Module RS := UEQR_UC.
Module SD := Area2DownstreamGeometry.

(** Integer query coordinates strictly between the four inner wall planes.
    This does not assert that gameplay preserves these bounds. *)
Definition rank10s_inside x z := -459 <= x <= 460 /\ -203 <= z <= 716.
Definition rank10s_meets vertices :=
  let '(a,b,c) := vertices in
  (0 <? SD.y_of (area1_source_normal_components vertices)) &&
  rank12b_axis_meets (SD.x_of a) (SD.x_of b) (SD.x_of c) (-459) 460 &&
  rank12b_axis_meets (SD.z_of a) (SD.z_of b) (SD.z_of c) (-203) 716.
Definition rank10s_candidates version := filter (fun face =>
  match snd face with Some vertices => rank10s_meets vertices | None => false end)
  (rank12b_faces version).
Definition rank10s_expected : list nat :=
  [1267;1268;1269;1270;1271;1274;1275;1276;1277;1278;
   1303;1304;1305;1306;1307;1311;1312;1314;
   1339;1340;1341;1342;1343;1346;1347;1348;1349;1350;
   1381;1382;1383;1384;1385;1387]%nat.
Definition rank10s_low vertices := let '(a,b,c) := vertices in
  (rank12b_max3 (SD.y_of a) (SD.y_of b) (SD.y_of c) <=? -101).

Definition Rank10SStaticCertificate : Prop := forall version,
  map fst (rank10s_candidates version) = rank10s_expected /\
  forallb (fun face => match snd face with
    | Some vertices => rank10s_low vertices | None => false end)
    (rank10s_candidates version) = true.
Theorem rank10s_static_certificate_checked : Rank10SStaticCertificate.
Proof. intros []; vm_compute; split; reflexivity. Qed.

(** This is a vertex-box result for EVERY point on EVERY candidate, not a
    sampled query result. It does not equate a rounded live plane height with
    ideal geometry. *)
Theorem rank10s_every_static_support_is_low : forall version ordinal vertices x y z,
  In (ordinal, Some vertices) (rank12b_faces version) ->
  0 < SD.y_of (area1_source_normal_components vertices) ->
  rank12b_point_in_vertex_box (x,y,z) vertices ->
  (-459 <= x <= 460)%R -> (-203 <= z <= 716)%R -> (y <= -101)%R.
Proof.
  intros version ordinal vertices x y z Hin Hup Hbox Hx Hz.
  assert (Hcandidate : In (ordinal, Some vertices) (rank10s_candidates version)).
  { apply filter_In. split; [exact Hin|]. cbn [snd].
    unfold rank10s_meets. destruct vertices as [[a b] c].
    unfold rank12b_point_in_vertex_box in Hbox.
    destruct Hbox as [Bx [By Bz]]. repeat rewrite andb_true_iff.
    split; [split; [apply Z.ltb_lt; exact Hup|]|];
      eapply rank12b_axis_meets_sound; eauto. }
  pose proof (proj2 (rank10s_static_certificate_checked version)) as Hlow.
  rewrite forallb_forall in Hlow. specialize (Hlow _ Hcandidate).
  destruct vertices as [[a b] c]. cbn [snd rank10s_low] in Hlow.
  apply Z.leb_le in Hlow. apply IZR_le in Hlow.
  unfold rank12b_point_in_vertex_box in Hbox. lra.
Qed.

Definition rank10s_elevator_words version := match version with
| VersionUS => elevator_collision_words_us | VersionJP => elevator_collision_words_jp end.
Definition rank10s_elevator_vertices version :=
  collision_vertices_from_words 20 (rank10s_elevator_words version).
Definition rank10s_elevator_indices version :=
  area1_parse_surface_groups 32 (skipn 62 (rank10s_elevator_words version)).
Definition rank10s_elevator_faces version := map
  (area1_source_triangle_vertices (rank10s_elevator_vertices version))
  (rank10s_elevator_indices version).
Definition rank10s_local_meets vertices := let '(a,b,c) := vertices in
  (0 <? SD.y_of (area1_source_normal_components vertices)) &&
  rank12b_axis_meets (SD.x_of a) (SD.x_of b) (SD.x_of c) (-459) 460 &&
  rank12b_axis_meets (SD.z_of a) (SD.z_of b) (SD.z_of c) (-459) 460.
Definition rank10s_base_a : Area1SourceVertex := (-511,0,512).
Definition rank10s_base_b : Area1SourceVertex := (512,0,512).
Definition rank10s_base_c : Area1SourceVertex := (512,0,-511).
Definition rank10s_base_d : Area1SourceVertex := (-511,0,-511).
Definition Rank10SElevatorCertificate : Prop := forall version,
  length (rank10s_elevator_faces version) = 36%nat /\
  filter (fun face => match face with
    | Some vertices => rank10s_local_meets vertices | None => false end)
    (rank10s_elevator_faces version) =
    [Some (rank10s_base_a,rank10s_base_b,rank10s_base_c);
     Some (rank10s_base_a,rank10s_base_c,rank10s_base_d)] /\
  nth_error (rank10s_elevator_faces version) 10 =
    Some (Some (rank10s_base_a,rank10s_base_b,rank10s_base_c)) /\
  nth_error (rank10s_elevator_faces version) 11 =
    Some (Some (rank10s_base_a,rank10s_base_c,rank10s_base_d)).
Theorem rank10s_elevator_certificate_checked : Rank10SElevatorCertificate.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Theorem rank10s_base_covers_interior : forall x z,
  rank10s_inside x z ->
  SD.point_in_closed_triangle_xz (x,0,z-256)
    rank10s_base_a rank10s_base_b rank10s_base_c \/
  SD.point_in_closed_triangle_xz (x,0,z-256)
    rank10s_base_a rank10s_base_c rank10s_base_d.
Proof.
  intros x z H. unfold rank10s_inside in H.
  unfold SD.point_in_closed_triangle_xz, SD.edge_cross_xz,
    rank10s_base_a, rank10s_base_b, rank10s_base_c, rank10s_base_d,
    SD.x_of, SD.z_of. nia.
Qed.

(** Extract the real post-list selection and its output store, leaving the
    subsequent debug-counter update and return outside this checkpoint. *)
Fixpoint rank10s_find_choice (s : statement) : option (statement * statement) :=
  match s with
  | Ssequence first rest => match first with
    | Ssequence (Sset id _) _ =>
        if Pos.eqb id RS._t'9 then Some (first,rest) else rank10s_find_choice rest
    | _ => rank10s_find_choice rest end
  | _ => None end.
Definition rank10s_cut version := match rank10s_find_choice
  (fn_body (ueqr_native_body version UEQRFindFloor)) with
  | Some (choice, Ssequence output _) => Ssequence choice output
  | _ => Sskip end.
Definition rank10s_surface := tptr (Tstruct RS._Surface noattr).
Definition rank10s_choice := Ssequence
  (Sset RS._t'9 (Evar RS._dynamicHeight tfloat))
  (Ssequence (Sset RS._t'10 (Evar RS._height tfloat))
    (Sifthenelse
      (Ebinop Ogt (Etempvar RS._t'9 tfloat) (Etempvar RS._t'10 tfloat) tint)
      (Ssequence (Sset RS._floor (Etempvar RS._dynamicFloor rank10s_surface))
        (Ssequence (Sset RS._t'11 (Evar RS._dynamicHeight tfloat))
          (Sassign (Evar RS._height tfloat) (Etempvar RS._t'11 tfloat)))) Sskip)).
Definition rank10s_output := Sassign
  (Ederef (Etempvar RS._pfloor (tptr rank10s_surface)) rank10s_surface)
  (Etempvar RS._floor rank10s_surface).
Theorem rank10s_selection_is_generated : forall version,
  rank10s_cut version = Ssequence rank10s_choice rank10s_output /\
  exists tail, rank10s_find_choice (fn_body (ueqr_native_body version UEQRFindFloor)) =
    Some (rank10s_choice, Ssequence rank10s_output tail).
Proof. intros []; split; try reflexivity; eexists; reflexivity. Qed.

Definition rank10s_temps le dynamic static floor :=
  PTree.set RS._t'11 (Vsingle dynamic)
    (PTree.set RS._floor floor
      (PTree.set RS._t'10 (Vsingle static) (PTree.set RS._t'9 (Vsingle dynamic) le))).

Lemma rank10s_local_float_read : forall ge e le m id b value,
  e ! id = Some (b,tfloat) -> Mem.load Mfloat32 m b 0 = Some (Vsingle value) ->
  eval_expr ge e le m (Evar id tfloat) (Vsingle value).
Proof.
  intros. eapply eval_Elvalue; [apply eval_Evar_local; eauto|].
  eapply deref_loc_value; [reflexivity|exact H0].
Qed.

(** No intact-list premise is smuggled into this result. The two list answers
    are explicit inputs. In particular, proving the dynamic answer is still
    the base, rather than NULL, is the remaining backward connection. *)
Definition Rank10SSelectionExecution : Prop :=
  forall version e le m hb db output_block output_offset floor_block floor_offset
    dynamic static after_height after_output,
  e ! RS._height = Some (hb,tfloat) ->
  e ! RS._dynamicHeight = Some (db,tfloat) ->
  le ! RS._dynamicFloor = Some (Vptr floor_block floor_offset) ->
  le ! RS._pfloor = Some (Vptr output_block output_offset) ->
  Mem.load Mfloat32 m hb 0 = Some (Vsingle static) ->
  Mem.load Mfloat32 m db 0 = Some (Vsingle dynamic) ->
  rank9cf_finite dynamic -> rank9cf_finite static ->
  (128 <= rank9cf_real dynamic)%R -> (rank9cf_real static <= 0)%R ->
  Mem.store Mfloat32 m hb 0 (Vsingle dynamic) = Some after_height ->
  Mem.store Mint32 after_height output_block (Ptrofs.unsigned output_offset)
    (Vptr floor_block floor_offset) = Some after_output ->
  ClightBigstep.Clight2.exec_stmt
    (Clight.globalenv (selected_clight_target version)) e le m (rank10s_cut version)
    E0 (rank10s_temps le dynamic static (Vptr floor_block floor_offset))
    after_output Out_normal /\
  Mem.load Mint32 after_output output_block (Ptrofs.unsigned output_offset) =
    Some (Vptr floor_block floor_offset).
Theorem rank10s_real_selection_keeps_dynamic_floor : Rank10SSelectionExecution.
Proof.
  unfold Rank10SSelectionExecution.
  intros version e le m hb db ob oo fb fo dynamic static mh mo
    Hh Hd Hfloor Houtput Hstatic Hdynamic Fd Fs Bd Bs Hstore Hout.
  assert (Hgt : Float32.cmp Cgt dynamic static = true).
  { unfold Float32.cmp, Float32.compare. rewrite Bcompare_correct by assumption.
    unfold rank9cf_real in Bd, Bs. rewrite Rcompare_Gt by lra. reflexivity. }
  split.
  2: { erewrite Mem.load_store_same by exact Hout. reflexivity. }
  rewrite (proj1 (rank10s_selection_is_generated version)).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - unfold rank10s_choice. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply rank10s_local_float_read; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. eapply rank10s_local_float_read; eauto.
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        -- eapply eval_Ebinop.
           ++ apply eval_Etempvar. rewrite PTree.gso by discriminate. apply PTree.gss.
           ++ apply eval_Etempvar. apply PTree.gss.
           ++ change (Some (Val.of_bool (Float32.cmp Cgt dynamic static)) = Some (Vint Int.one)).
              rewrite Hgt. reflexivity.
        -- reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_Sset. apply eval_Etempvar.
              repeat rewrite PTree.gso by discriminate. exact Hfloor.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** apply exec_Sset. eapply rank10s_local_float_read; eauto.
              ** eapply exec_Sassign with (v := Vsingle dynamic) (v2 := Vsingle dynamic)
                   (loc := hb) (ofs := Ptrofs.zero) (bf := Full).
                 --- apply eval_Evar_local. exact Hh.
                 --- apply eval_Etempvar. apply PTree.gss.
                 --- reflexivity.
                 --- eapply assign_loc_value with (chunk := Mfloat32); try reflexivity; exact Hstore.
  - unfold rank10s_output, rank10s_temps.
    eapply exec_Sassign with (v := Vptr fb fo) (v2 := Vptr fb fo)
      (loc := ob) (ofs := oo) (bf := Full).
    + apply eval_Ederef. apply eval_Etempvar.
      repeat rewrite PTree.gso by discriminate. exact Houtput.
    + apply eval_Etempvar. rewrite PTree.gso by discriminate. apply PTree.gss.
    + reflexivity.
    + eapply assign_loc_value with (chunk := Mint32); try reflexivity; exact Hout.
Qed.

Definition Rank10ASupportChangeBoundary : Prop :=
  Rank10SStaticCertificate /\ Rank10SElevatorCertificate /\ Rank10SSelectionExecution /\
  (forall version ordinal vertices x y z,
    In (ordinal, Some vertices) (rank12b_faces version) ->
    0 < SD.y_of (area1_source_normal_components vertices) ->
    rank12b_point_in_vertex_box (x,y,z) vertices ->
    (-459 <= x <= 460)%R -> (-203 <= z <= 716)%R -> (y <= -101)%R) /\
  (forall x z, rank10s_inside x z ->
    SD.point_in_closed_triangle_xz (x,0,z-256)
      rank10s_base_a rank10s_base_b rank10s_base_c \/
    SD.point_in_closed_triangle_xz (x,0,z-256)
      rank10s_base_a rank10s_base_c rank10s_base_d).
Theorem rank10s_support_boundary_checked : Rank10ASupportChangeBoundary.
Proof.
  split; [exact rank10s_static_certificate_checked|].
  split; [exact rank10s_elevator_certificate_checked|].
  split; [exact rank10s_real_selection_keeps_dynamic_floor|].
  split; [exact rank10s_every_static_support_is_low|exact rank10s_base_covers_interior].
Qed.
