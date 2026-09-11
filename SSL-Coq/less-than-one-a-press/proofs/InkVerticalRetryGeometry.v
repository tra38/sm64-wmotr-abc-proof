(** A same-X/Z candidate for the pre-action graphical retry.

    This is a finite certificate over the generated SSL mesh and the already
    checked timer-131 transform, NOT an execution of the live surface lists.
    In particular it does not install a negative depth, move Mario to this
    point, or establish that the top is loaded there in a clean run.

    Separating ANY successful retry from a TOP-owned retry matters: the
    static floor can become eligible before the moving top does. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import Clightdefs Cop Ctypes Floats Integers Memory Values.
From LessThanOneAPress.Proofs Require Import Area1FirstNull CollisionMeshFacts
  Timer131Surface.
Import ListNotations.
Local Open Scope Z_scope.

Definition ivr_query (height : Z) : Area1IntegerQuery :=
  {| area1_query_x := -2200; area1_query_y := height; area1_query_z := -1024 |}.

Definition ivr_xz_accepts vertices query face : bool :=
  match area1_source_triangle_vertices vertices face with
  | Some (a, b, c) =>
      forallb (fun edge => negb (Int.lt edge Int.zero))
        [area1_floor_edge_i32 (area1_query_x query) (area1_query_z query) a b;
         area1_floor_edge_i32 (area1_query_x query) (area1_query_z query) b c;
         area1_floor_edge_i32 (area1_query_x query) (area1_query_z query) c a]
  | None => false
  end.

Definition ivr_accepts vertices query face : bool :=
  if ivr_xz_accepts vertices query face then
    match area1_loaded_floor_buffer_difference vertices face query with
    | Some difference => negb (Float32.cmp Clt difference (area1_f32_of_Z 0))
    | None => false
    end
  else false.

Definition ivr_hits vertices faces height :=
  filter (ivr_accepts vertices (ivr_query height)) faces.

Definition ivr_top_floors :=
  area1_source_floor_inventory timer131_vertices_s16 pyramid_top_triangles 5 7.

Definition ivr_static_hits_us height :=
  ivr_hits area1_collision_vertices_us area1_q_static_floor_candidates_computed_us height.
Definition ivr_static_hits_jp height :=
  ivr_hits area1_collision_vertices_jp area1_q_static_floor_candidates_computed_jp height.
Definition ivr_top_hits height := ivr_hits timer131_vertices_s16 ivr_top_floors height.

(** The checked cell inventory has only one X/Z-eligible face from each of
    the static mesh and the timer-131 top. Hence these samples do not depend
    on choosing a favorable order between several eligible faces in either
    of those two lists. Other live dynamic objects remain a separate issue. *)
Theorem ivr_xz_candidates_checked :
  ivr_top_floors = [(0, 2, 3); (2, 1, 3); (1, 4, 3); (4, 0, 3)] /\
  (forall y,
    filter (ivr_xz_accepts area1_collision_vertices_us (ivr_query y))
      area1_q_static_floor_candidates_computed_us = [area1_q_only_xz_accepted_face] /\
    filter (ivr_xz_accepts area1_collision_vertices_jp (ivr_query y))
      area1_q_static_floor_candidates_computed_jp = [area1_q_only_xz_accepted_face] /\
    filter (ivr_xz_accepts timer131_vertices_s16 (ivr_query y)) ivr_top_floors =
      [timer131_state_face]).
Proof.
  split; [vm_compute; reflexivity|].
  intro y. vm_compute. repeat split; reflexivity.
Qed.

Lemma ivr_static_versions_agree : forall y, ivr_static_hits_us y = ivr_static_hits_jp y.
Proof.
  intros y. unfold ivr_static_hits_us, ivr_static_hits_jp.
  destruct area1_generated_initializer_inventory_certificate as (_ & _ & _ & Hus & _ & Hjp).
  rewrite Hus, Hjp, (proj1 selected_ink_area1_mesh_is_version_identical). reflexivity.
Qed.

Definition ivr_test_heights : list Z := [768; 1201; 1202; 1860; 1861; 1950].
Definition ivr_expected_hits : list (Z * list Area1TriangleIndex * list Area1TriangleIndex) :=
  [(768, [], []); (1201, [], []);
   (1202, [area1_q_only_xz_accepted_face], []);
   (1860, [area1_q_only_xz_accepted_face], []);
   (1861, [area1_q_only_xz_accepted_face], [timer131_state_face]);
   (1950, [area1_q_only_xz_accepted_face], [timer131_state_face])].

Theorem ivr_paired_queries_checked :
  map (fun y => (y, ivr_static_hits_us y, ivr_top_hits y)) ivr_test_heights = ivr_expected_hits /\
  map (fun y => (y, ivr_static_hits_jp y, ivr_top_hits y)) ivr_test_heights = ivr_expected_hits.
Proof.
  assert (map (fun y => (y, ivr_static_hits_us y, ivr_top_hits y))
    ivr_test_heights = ivr_expected_hits) as Hus by (vm_compute; reflexivity).
  split; [exact Hus|]. rewrite <- Hus. apply map_ext.
  intro y. exact (f_equal (fun hits => (y, hits, ivr_top_hits y))
    (eq_sym (ivr_static_versions_agree y))).
Qed.

(** These are neighboring INTEGER query samples, not an asserted exhaustive
    theorem over all floating-point heights or all controller histories. *)
Theorem ivr_adjacent_top_buffer_samples_checked :
  timer131_buffer_observation (ivr_query 1860) timer131_state_face =
    Some (1156733869, 3210569728, true) /\
  timer131_buffer_observation (ivr_query 1861) timer131_state_face =
    Some (1156733869, 1040867328, false) /\
  Float32.cmp Cgt (Float32.of_bits (Int.repr 1156733869)) (area1_f32_of_Z 1280) = true /\
  area1_loaded_plane_bits area1_collision_vertices_us area1_q_only_xz_accepted_face =
    Some (0, 1065353216, 0, 3298820096).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** All tested positions have ordinary, exact signed-16 conversions; this
    witness does not rely on a parallel-universe coordinate conversion. *)
Theorem ivr_samples_have_exact_coordinate_casts : forall m,
  map (fun c => sem_cast (Vsingle (area1_f32_of_Z c)) tfloat
      (Tint I16 Signed noattr) m) (-2200 :: -1024 :: ivr_test_heights) =
  map (fun c => Some (Vint (Int.repr c))) (-2200 :: -1024 :: ivr_test_heights).
Proof. intro m. vm_compute. reflexivity. Qed.

(** The low successful sample is NOT an Ink top installation. At the high
    sample, the unique eligible top face is higher than the eligible static
    floor, so the source's dynamic-vs-static comparison favors the top if
    these are the actual live query results. The retry copies query Y, not
    floor height; there is no automatic snap to the computed top height. *)
Theorem ivr_low_success_and_top_success_are_distinct :
  ivr_static_hits_us 768 = [] /\ ivr_top_hits 768 = [] /\
  ivr_static_hits_us 1202 = [area1_q_only_xz_accepted_face] /\ ivr_top_hits 1202 = [] /\
  ivr_static_hits_us 1861 = [area1_q_only_xz_accepted_face] /\
  ivr_top_hits 1861 = [timer131_state_face] /\
  1202 - 768 = 434 /\ 1861 - 768 = 1093.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A stronger conditional target than merely passing the 78-unit buffer:
    the copied Y is exactly the computed top height, 1938.8648681640625.
    find_floor truncates that input to 1938, still accepts this face, and
    returns the same binary32 height. Thus this candidate needs no later
    Y snap to attain contact. It still supplies no clean arrival or lifecycle. *)
Definition ivr_contact_height := Float32.of_bits (Int.repr 1156733869).

(** Compare computed float bits first. Reducing equality between the two
    complete Flocq float values unnecessarily expands large proof terms. *)
Lemma ivr_contact_plane_exact :
  area1_loaded_floor_height timer131_vertices_s16 timer131_state_face (-2200) (-1024) =
    Some ivr_contact_height.
Proof.
  assert (option_map (fun h => Int.unsigned (Float32.to_bits h))
    (area1_loaded_floor_height timer131_vertices_s16 timer131_state_face (-2200) (-1024)) =
    Some 1156733869) as Hbits by (vm_compute; reflexivity).
  destruct (area1_loaded_floor_height timer131_vertices_s16 timer131_state_face (-2200) (-1024))
    as [height|]; cbn in Hbits; try discriminate.
  injection Hbits as Hbits. apply (f_equal Int.repr) in Hbits.
  rewrite Int.repr_unsigned in Hbits.
  f_equal. rewrite <- (Float32.of_to_bits height), Hbits. reflexivity.
Qed.

Definition InkExactHeightRetryGeometry : Prop :=
  (forall m, sem_cast (Vsingle ivr_contact_height) tfloat (Tint I16 Signed noattr) m =
    Some (Vint (Int.repr 1938))) /\
  ivr_top_hits 1938 = [timer131_state_face] /\
  ivr_static_hits_us 1938 = [area1_q_only_xz_accepted_face] /\
  ivr_static_hits_jp 1938 = [area1_q_only_xz_accepted_face] /\
  area1_loaded_floor_height timer131_vertices_s16 timer131_state_face (-2200) (-1024) =
    Some ivr_contact_height /\
  Float32.sub ivr_contact_height ivr_contact_height = area1_f32_of_Z 0 /\
  Int.unsigned (Float32.to_bits (Float32.sub ivr_contact_height (area1_f32_of_Z 768))) =
    1150442413.

Theorem ivr_exact_height_retry_checked : InkExactHeightRetryGeometry.
Proof.
  split; [intro m; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [exact ivr_contact_plane_exact|].
  vm_compute. split; reflexivity.
Qed.

Definition InkVerticalRetryGeometryBoundary : Prop :=
  (map (fun y => (y, ivr_static_hits_us y, ivr_top_hits y)) ivr_test_heights = ivr_expected_hits /\
   map (fun y => (y, ivr_static_hits_jp y, ivr_top_hits y)) ivr_test_heights = ivr_expected_hits) /\
  (timer131_buffer_observation (ivr_query 1860) timer131_state_face =
     Some (1156733869, 3210569728, true) /\
   timer131_buffer_observation (ivr_query 1861) timer131_state_face =
     Some (1156733869, 1040867328, false) /\
   Float32.cmp Cgt (Float32.of_bits (Int.repr 1156733869)) (area1_f32_of_Z 1280) = true /\
   area1_loaded_plane_bits area1_collision_vertices_us area1_q_only_xz_accepted_face =
     Some (0, 1065353216, 0, 3298820096)) /\
  (forall m,
    map (fun c => sem_cast (Vsingle (area1_f32_of_Z c)) tfloat (Tint I16 Signed noattr) m)
      (-2200 :: -1024 :: ivr_test_heights) =
    map (fun c => Some (Vint (Int.repr c))) (-2200 :: -1024 :: ivr_test_heights)) /\
  InkExactHeightRetryGeometry.

Theorem ivr_vertical_retry_geometry_checked : InkVerticalRetryGeometryBoundary.
Proof.
  split; [exact ivr_paired_queries_checked|].
  split; [exact ivr_adjacent_top_buffer_samples_checked|].
  split; [exact ivr_samples_have_exact_coordinate_casts|].
  exact ivr_exact_height_retry_checked.
Qed.
