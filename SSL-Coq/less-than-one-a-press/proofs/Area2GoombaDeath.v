(** Passive Goomba death as an elevator-coin supplier.
    Execute the COMPLETE generated environmental-death helper in ordinary dry
    state: it returns false, with no calls, trace or memory changes. Separately
    census the generated Area-2 collision types and exact terrain footer.
    Neither fact assumes that an arbitrary live history has these flags or
    lists. Attack contact, unusual support histories and coin delivery remain
    separate gameplay questions. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_obj_behaviors_2 jp_obj_behaviors_2.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts Area1FirstNull
  CollisionMeshFacts EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module GD := us_obj_behaviors_2.

Definition gd_body version := match version with
| VersionUS => us_obj_behaviors_2.f_obj_die_if_above_lava_and_health_non_positive
| VersionJP => jp_obj_behaviors_2.f_obj_die_if_above_lava_and_health_non_positive end.

Definition gd_flags version temporary :=
  Ederef (Ebinop Oadd
    (Efield (Efield
      (Ederef (Etempvar temporary (tptr (Tstruct GD._Object noattr)))
        (Tstruct GD._Object noattr))
      GD._rawData (Tunion (rank15_raw_union_tag version) noattr))
      GD._asU32 (tarray tuint 80))
    (Econst_int (Int.repr 25) tint) (tptr tuint)) tuint.
Definition gd_bit temporary bit :=
  Ebinop Oand (Etempvar temporary tuint)
    (Ebinop Oshl (Econst_int (Int.repr 1) tint)
      (Econst_int (Int.repr bit) tint) tint) tuint.
Definition gd_zero := Sreturn (Some (Econst_int Int.zero tint)).

(** Unexecuted water/sound arms are taken from the actual body, not replaced
    by assumed harmless calls. This checked decomposition covers the full body. *)
Theorem gd_generated_body : forall version, exists water sound,
  fn_body (gd_body version) =
  Ssequence
    (Ssequence (Sset GD._t'3 rank15_current_object_expression)
      (Ssequence (Sset GD._t'4 (gd_flags version GD._t'3))
        (Sifthenelse (gd_bit GD._t'4 6) water
          (Ssequence (Sset GD._t'5 rank15_current_object_expression)
            (Ssequence (Sset GD._t'6 (gd_flags version GD._t'5))
              (Sifthenelse (Eunop Onotbool (gd_bit GD._t'6 11) tint)
                (Ssequence
                  (Ssequence (Sset GD._t'7 rank15_current_object_expression)
                    (Ssequence (Sset GD._t'8 (gd_flags version GD._t'7))
                      (Sifthenelse (gd_bit GD._t'8 3) sound Sskip)))
                  gd_zero)
                Sskip))))))
    (Ssequence (Scall None
      (Evar GD._obj_die_if_health_non_positive (Tfunction [] tvoid cc_default)) [])
      (Sreturn (Some (Econst_int Int.one tint)))).
Proof. intros []; do 2 eexists; reflexivity. Qed.

Definition gd_layout_check environment union_tag :=
  match environment ! GD._Object, environment ! union_tag with
  | Some obj, Some raw =>
    match field_offset environment GD._rawData (co_members obj),
      union_field_offset environment GD._asU32 (co_members raw) with
    | OK (a, Full), OK (b, Full) => Z.eqb a 136 && Z.eqb b 0
    | _, _ => false end
  | _, _ => false end.
Lemma gd_layout_checked : forall version,
  gd_layout_check (rank15_selected_header_environment version)
    (rank15_raw_union_tag version) = true.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma gd_layout : forall version,
  let ge := Clight.globalenv (selected_clight_target version) in
  exists obj raw,
    (genv_cenv ge) ! GD._Object = Some obj /\
    (genv_cenv ge) ! (rank15_raw_union_tag version) = Some raw /\
    field_offset ge GD._rawData (co_members obj) = OK (136, Full) /\
    union_field_offset ge GD._asU32 (co_members raw) = OK (0, Full).
Proof.
  intros version ge.
  pose proof (gd_layout_checked version) as H.
  rewrite rank15_selected_header_environment_exact in H.
  change (gd_layout_check (genv_cenv ge) (rank15_raw_union_tag version) = true) in H.
  unfold gd_layout_check in H.
  destruct ((genv_cenv ge) ! GD._Object) as [obj|] eqn:Ho; try discriminate.
  destruct ((genv_cenv ge) ! (rank15_raw_union_tag version)) as [raw|] eqn:Hr;
    try discriminate.
  destruct (field_offset ge GD._rawData (co_members obj)) as [[a af]|] eqn:Ha;
    try discriminate.
  destruct (union_field_offset ge GD._asU32 (co_members raw)) as [[b bf]|] eqn:Hb;
    [|destruct af; discriminate].
  destruct af, bf; cbn in H; try discriminate.
  apply andb_true_iff in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst a b.
  exists obj, raw. repeat split; assumption.
Qed.

Lemma gd_flags_read : forall version e le m temporary ob oo flags,
  le ! temporary = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 25))) =
    Some (Vint flags) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (gd_flags version temporary) (Vint flags).
Proof.
  intros version e le m temporary ob oo flags Htemp Hload.
  destruct (gd_layout version) as (obj & raw & Ho & Hr & Ha & Hb).
  eapply eval_Elvalue.
  - unfold gd_flags, rank15_raw_address. apply eval_Ederef.
    eapply eval_Ebinop.
    + eapply eval_Elvalue.
      * eapply eval_Efield_union with (co := raw).
        -- eapply eval_Elvalue.
           ++ eapply eval_Efield_struct with (co := obj).
              ** eapply eval_Elvalue.
                 --- apply eval_Ederef. apply eval_Etempvar. exact Htemp.
                 --- apply deref_loc_copy. reflexivity.
              ** reflexivity.
              ** exact Ho.
              ** exact Ha.
           ++ apply deref_loc_copy. reflexivity.
        -- reflexivity.
        -- exact Hr.
        -- exact Hb.
      * apply deref_loc_reference. reflexivity.
    + constructor.
    + cbn. rewrite Ptrofs.add_zero. reflexivity.
  - eapply deref_loc_value with (chunk := Mint32); [reflexivity|exact Hload].
Qed.

Lemma gd_clear_bit_evaluates : forall version e le m temporary bit flags,
  le ! temporary = Some (Vint flags) ->
  0 <= bit < 32 ->
  Int.and flags (Int.shl Int.one (Int.repr bit)) = Int.zero ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (gd_bit temporary bit) (Vint Int.zero).
Proof.
  intros version e le m temporary bit flags Htemp Hrange Hclear.
  unfold gd_bit. eapply eval_Ebinop.
  - apply eval_Etempvar. exact Htemp.
  - eapply eval_Ebinop; [constructor|constructor|].
    cbn. unfold Int.ltu. rewrite Int.unsigned_repr by (change (0 <= bit <= 4294967295); lia).
    change (Int.unsigned Int.iwordsize) with 32.
    destruct (Coqlib.zlt bit 32); [reflexivity|lia].
  - change (Some (Vint (Int.and flags (Int.shl Int.one (Int.repr bit)))) =
      Some (Vint Int.zero)).
    rewrite Hclear. reflexivity.
Qed.

Definition GoombaDryDeathCheckExecution : Prop :=
  forall version e le m cb ob oo flags,
  e ! GD._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    GD._gCurrentObject = Some cb ->
  Mem.load Mptr m cb 0 = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (rank15_raw_address oo (Int.repr 25))) =
    Some (Vint flags) ->
  Int.and flags (Int.repr 64) = Int.zero ->
  Int.and flags (Int.repr 2048) = Int.zero ->
  Int.and flags (Int.repr 8) = Int.zero ->
  exists after_locals,
    ClightBigstep.Clight2.exec_stmt
      (Clight.globalenv (selected_clight_target version)) e le m
      (fn_body (gd_body version)) E0 after_locals m
      (Out_return (Some (Vint Int.zero, tint))).

Theorem gd_dry_check_returns_without_death : GoombaDryDeathCheckExecution.
Proof.
  intros version e le m cb ob oo flags Hlocal Hsymbol Hcurrent Hflags H6 H11 H3.
  destruct (gd_generated_body version) as (water & sound & Hbody).
  rewrite Hbody. eexists.
  eapply exec_Sseq_2; [|discriminate].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_Sset. eapply rank15_current_object_read; eauto.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_Sset. eapply gd_flags_read; [apply PTree.gss|exact Hflags].
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      * eapply gd_clear_bit_evaluates; [apply PTree.gss|lia|exact H6].
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_Sset. eapply rank15_current_object_read; eauto.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_Sset. eapply gd_flags_read; [apply PTree.gss|exact Hflags].
           ++ eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
              ** eapply eval_Eunop.
                 --- eapply gd_clear_bit_evaluates; [apply PTree.gss|lia|exact H11].
                 --- reflexivity.
              ** reflexivity.
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                     +++ apply exec_Sset. eapply rank15_current_object_read; eauto.
                     +++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                         *** apply exec_Sset. eapply gd_flags_read;
                               [apply PTree.gss|exact Hflags].
                         *** eapply exec_Sifthenelse with
                               (v1 := Vint Int.zero) (b := false).
                             ---- eapply gd_clear_bit_evaluates;
                                    [apply PTree.gss|lia|exact H3].
                             ---- reflexivity.
                             ---- constructor.
                 --- apply exec_Sreturn_some. constructor.
Qed.

(** Deletion is not the loot-spawning death operation. This exact body
    receipt does not assert that a caller stops after marking an object. *)
Theorem gd_mark_for_deletion_is_only_flag_write : forall version,
  fn_body (match version with
    | VersionUS => us_object_helpers.f_obj_mark_for_deletion
    | VersionJP => jp_object_helpers.f_obj_mark_for_deletion end) =
  Sassign (Efield
    (Ederef (Etempvar GD._obj (tptr (Tstruct GD._Object noattr)))
      (Tstruct GD._Object noattr)) GD._activeFlags tshort)
    (Econst_int Int.zero tint).
Proof. intros []; reflexivity. Qed.

(** Preserve surface types and the unconsumed footer while reusing the
    existing triangle-record parser. The successful finite receipt below
    checks all group counts and reaches the actual end marker. *)
Fixpoint gd_surface_groups fuel words : list (Z * Z) * list Z :=
  match fuel with
  | O => ([], words)
  | S fuel' => match words with
    | kind :: count :: rest =>
      if area1_source_is_surface_type kind then
        let stride := if area1_source_surface_has_force kind then 4%nat else 3%nat in
        let '(triangles, suffix) := area1_parse_triangle_records (Z.to_nat count) stride rest in
        let '(groups, tail) := gd_surface_groups fuel' suffix in
        ((kind, Z.of_nat (length triangles)) :: groups, tail)
      else ([], words)
    | _ => ([], words) end
  end.
Definition gd_mesh_groups words :=
  gd_surface_groups 32 (skipn (2 + 3 * Z.to_nat (nth 1 words 0)) words).
Definition gd_static_words version := init_int16_values (gvar_init
  (match version with
  | VersionUS => us_ssl_collision.v_ssl_seg7_area_2_collision
  | VersionJP => jp_ssl_collision.v_ssl_seg7_area_2_collision end)).
Definition gd_static_groups : list (Z * Z) :=
  [(0,1068);(5,6);(11,17);(19,32);(21,12);(29,2);(30,2);
   (34,128);(36,36);(39,78);(45,18);(102,27);(118,132)].
Definition gd_static_footer :=
  [65;67;4;0;0;0;6451;128;
   102;1741;-101;1843;0;102;0;-101;528;0;102;-1740;-101;1843;0;66].
Definition gd_dynamic_words version := map (fun v => init_int16_values (gvar_init v))
  (match version with
  | VersionUS =>
    [us_ssl_collision.v_ssl_seg7_collision_grindel;
     us_ssl_collision.v_ssl_seg7_collision_spindel;
     us_ssl_collision.v_ssl_seg7_collision_0702808C;
     us_ssl_collision.v_ssl_seg7_collision_pyramid_elevator;
     us_ssl_collision.v_ssl_seg7_collision_07028274;
     us_ssl_collision.v_ssl_seg7_collision_070282F8;
     us_ssl_collision.v_ssl_seg7_collision_07028370;
     us_ssl_collision.v_ssl_seg7_collision_070284B0]
  | VersionJP =>
    [jp_ssl_collision.v_ssl_seg7_collision_grindel;
     jp_ssl_collision.v_ssl_seg7_collision_spindel;
     jp_ssl_collision.v_ssl_seg7_collision_0702808C;
     jp_ssl_collision.v_ssl_seg7_collision_pyramid_elevator;
     jp_ssl_collision.v_ssl_seg7_collision_07028274;
     jp_ssl_collision.v_ssl_seg7_collision_070282F8;
     jp_ssl_collision.v_ssl_seg7_collision_07028370;
     jp_ssl_collision.v_ssl_seg7_collision_070284B0] end).
Definition gd_nonburning (groups : list (Z * Z)) :=
  forallb (fun group => negb (Z.eqb (fst group) 1)) groups.
Definition GoombaArea2TerrainCertificate : Prop := forall version,
  gd_mesh_groups (gd_static_words version) = (gd_static_groups, gd_static_footer) /\
  gd_nonburning (fst (gd_mesh_groups (gd_static_words version))) = true /\
  map (fun words => fold_right (fun group n => snd group + n) 0
    (fst (gd_mesh_groups words))) (gd_dynamic_words version) =
      [12;32;12;36;12;10;32;32] /\
  forallb (fun words =>
    gd_nonburning (fst (gd_mesh_groups words)) &&
    match snd (gd_mesh_groups words) with [65;66] => true | _ => false end)
    (gd_dynamic_words version) = true.
Theorem gd_area2_terrain_checked : GoombaArea2TerrainCertificate.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Definition Area2GoombaDeathBoundary : Prop :=
  GoombaDryDeathCheckExecution /\ GoombaArea2TerrainCertificate /\
  (forall version, fn_body (match version with
    | VersionUS => us_object_helpers.f_obj_mark_for_deletion
    | VersionJP => jp_object_helpers.f_obj_mark_for_deletion end) =
    Sassign (Efield
      (Ederef (Etempvar GD._obj (tptr (Tstruct GD._Object noattr)))
        (Tstruct GD._Object noattr)) GD._activeFlags tshort)
      (Econst_int Int.zero tint)).
Theorem gd_environmental_death_boundary_checked : Area2GoombaDeathBoundary.
Proof.
  split; [exact gd_dry_check_returns_without_death|].
  split; [exact gd_area2_terrain_checked|exact gd_mark_for_deletion_is_only_flag_write].
Qed.
