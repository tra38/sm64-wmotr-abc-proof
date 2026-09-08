From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight Clightdefs ClightBigstep Cop Ctypes
  Errors Events Floats Globalenvs Integers Maps Memory Values.
From Pedro.Generated Require Import
  us_behavior_data jp_behavior_data us_behavior_script jp_behavior_script
  us_surface_collision jp_surface_collision us_surface_load jp_surface_load
  us_mario jp_mario us_object_helpers jp_object_helpers.
From Pedro.Proofs Require Import
  ASTFacts GameTypes TTCCogExecution CogActionExecution GroundGapReturn
  DustCurObjUpdateExecution.
Import ListNotations.
Open Scope Z_scope.

Module CF := us_surface_collision.
Module CL := us_surface_load.
Module CB := us_behavior_script.

Definition clone_floor_search_function version : function :=
  match version with VersionUS => CF.f_find_floor_from_list
                   | VersionJP => jp_surface_collision.f_find_floor_from_list end.
Definition clone_break_function version : function :=
  match version with VersionUS => CB.f_bhv_cmd_break
                   | VersionJP => jp_behavior_script.f_bhv_cmd_break end.

(** The three actual scripts installed by the non-holdable path are BEGIN,
    BREAK. They contain neither a collision loader nor a native behavior call.
    Installing the script still crosses segmented_to_virtual; this receipt
    does not assume that the existing N64 address boundary has been solved. *)
Definition clone_carry_scripts_claim : Prop :=
  forall version,
    map (fun variable => gvar_init variable)
      (match version with
       | VersionUS => [us_behavior_data.v_bhvCarrySomething3;
                       us_behavior_data.v_bhvCarrySomething4;
                       us_behavior_data.v_bhvCarrySomething5]
       | VersionJP => [jp_behavior_data.v_bhvCarrySomething3;
                       jp_behavior_data.v_bhvCarrySomething4;
                       jp_behavior_data.v_bhvCarrySomething5] end) =
    repeat [Init_int32 (Int.repr 524288); Init_int32 (Int.repr 167772160)] 3 /\
    nth_error (gvar_init
      (match version with VersionUS => CB.v_BehaviorCmdTable
                          | VersionJP => jp_behavior_script.v_BehaviorCmdTable end)) 10 =
      Some (Init_addrof CB._bhv_cmd_break Ptrofs.zero).

Theorem generated_clone_carry_scripts_us_jp : clone_carry_scripts_claim.
Proof. intros []; vm_compute; split; reflexivity. Qed.

Theorem generated_clone_break_preserves_all_memory_us_jp :
  forall version (ge : Clight.genv) memory,
    eval_funcall function_entry2 ge memory (Internal (clone_break_function version))
      [] E0 memory (Vint Int.one).
Proof.
  intros version ge memory. destruct version; cbn [clone_break_function].
  all: eapply eval_funcall_internal;
    [action_entry | simpl fn_body; cog_stmt |
     cbn; split; [discriminate | reflexivity] | cbn; reflexivity].
Qed.

Ltac clone_empty_stmt :=
  lazymatch goal with |- exec_stmt ?entry ?ge ?e ?le ?m ?s ?t ?le' ?m' ?out =>
    let body := eval hnf in s in change (exec_stmt entry ge e le m body t le' m' out) end;
  lazymatch goal with
  | |- exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      eapply exec_Sloop_stop1 with (out' := Out_break);
      [clone_empty_stmt | constructor]
  | |- exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      first [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
               [clone_empty_stmt | clone_empty_stmt]
            |eapply exec_Sseq_2; [clone_empty_stmt | discriminate]]
  | |- exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse;
        [cog_expr | cbn; reflexivity | cog_reduce_statement; clone_empty_stmt]
  | _ => cog_stmt
  end.

(** Complete original floor-list search with an empty head. No permissions,
    object-position, hitbox, retained-floor or callee-execution hypothesis is
    needed. In particular even the output-height cell is not read or written. *)
Definition clone_empty_floor_execution_claim version : Prop :=
  forall (ge : Clight.genv) memory x y z height_pointer,
    eval_funcall function_entry2 ge memory
      (Internal (clone_floor_search_function version))
      [Vint Int.zero; Vint x; Vint y; Vint z; height_pointer]
      E0 memory (Vint Int.zero).

Theorem generated_empty_floor_list_returns_null_us_jp :
  forall version, clone_empty_floor_execution_claim version.
Proof.
  intros version ge memory px py pz height_pointer.
  destruct version; cbn [clone_floor_search_function].
  all: eapply eval_funcall_internal;
    [action_entry | simpl fn_body; clone_empty_stmt |
     cbn; split; [discriminate | reflexivity] | cbn; reflexivity].
Qed.

(** The generated search reads the node's surface and next fields. Neither
    the parent Object pointer nor its position/hitbox data is consulted.
    This is a syntax receipt, not a whole-list execution or alias theorem. *)
Definition clone_floor_search_source_claim version : Prop :=
  direct_callees_s (fn_body (clone_floor_search_function version)) = [] /\
  statement_mentions_ident_s CF._object
    (fn_body (clone_floor_search_function version)) = false /\
  statement_mentions_ident_s CF._Object
    (fn_body (clone_floor_search_function version)) = false /\
  statement_mentions_ident_s CF._surface
    (fn_body (clone_floor_search_function version)) = true /\
  statement_mentions_ident_s CF._next
    (fn_body (clone_floor_search_function version)) = true.

Theorem generated_clone_floor_search_source_us_jp :
  forall version, clone_floor_search_source_claim version.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Definition clone_normal_tag version : ident :=
  match version with VersionUS => CF.__769 | VersionJP => jp_surface_collision.__732 end.

Record clone_query_layout version (ce : composite_env) : Type := {
  clone_node_co : composite;
  clone_surface_co : composite;
  clone_normal_co : composite;
  clone_node_lookup : ce ! CF._SurfaceNode = Some clone_node_co;
  clone_surface_lookup : ce ! CF._Surface = Some clone_surface_co;
  clone_normal_lookup : ce ! (clone_normal_tag version) = Some clone_normal_co;
  clone_next_offset : field_offset ce CF._next (co_members clone_node_co) = OK (0, Full);
  clone_surface_offset : field_offset ce CF._surface (co_members clone_node_co) = OK (4, Full);
  clone_type_offset : field_offset ce CF._type (co_members clone_surface_co) = OK (0, Full);
  clone_v1_offset : field_offset ce CF._vertex1 (co_members clone_surface_co) = OK (10, Full);
  clone_v2_offset : field_offset ce CF._vertex2 (co_members clone_surface_co) = OK (16, Full);
  clone_v3_offset : field_offset ce CF._vertex3 (co_members clone_surface_co) = OK (22, Full);
  clone_normal_offset : field_offset ce CF._normal (co_members clone_surface_co) = OK (28, Full);
  clone_origin_offset : field_offset ce CF._originOffset (co_members clone_surface_co) = OK (40, Full);
  clone_nx_offset : field_offset ce CF._x (co_members clone_normal_co) = OK (0, Full);
  clone_ny_offset : field_offset ce CF._y (co_members clone_normal_co) = OK (4, Full);
  clone_nz_offset : field_offset ce CF._z (co_members clone_normal_co) = OK (8, Full)
}.

Definition clone_query_layout_receipt : Prop :=
  forall version,
    let ce := prog_comp_env (match version with VersionUS => CF.prog
                             | VersionJP => jp_surface_collision.prog end) in
    map (fun '(tag, field) => field_offset ce field
      (match ce ! tag with Some co => co_members co | None => [] end))
      [(CF._SurfaceNode, CF._next); (CF._SurfaceNode, CF._surface);
       (CF._Surface, CF._type); (CF._Surface, CF._vertex1);
       (CF._Surface, CF._vertex2); (CF._Surface, CF._vertex3);
       (CF._Surface, CF._normal); (CF._Surface, CF._originOffset);
       (clone_normal_tag version, CF._x); (clone_normal_tag version, CF._y);
       (clone_normal_tag version, CF._z)] =
      map (fun offset => OK (offset, Full)) [0;4;0;10;16;22;28;40;0;4;8] /\
    sizeof ce (Tstruct CF._SurfaceNode noattr) = 8.

Theorem clone_query_layout_generated_us_jp : clone_query_layout_receipt.
Proof. intros []; vm_compute; split; reflexivity. Qed.

(** Readable singleton list with the certified lower cog triangle's X/Z
    vertices and a horizontal plane at -2088. No Object cell is an input.
    This is a local query state, not an executed surface loader or clone route. *)
Definition published_cog_floor_image memory node surface camera : Prop :=
  Mem.load Mptr memory node 0 = Some (Vint Int.zero) /\
  Mem.load Mptr memory node 4 = Some (Vptr surface Ptrofs.zero) /\
  Mem.load Mint16signed memory surface 0 = Some (Vint (Int.repr 21)) /\
  Mem.load Mint16signed memory surface 10 = Some (Vint (Int.repr 1569)) /\
  Mem.load Mint16signed memory surface 14 = Some (Vint (Int.repr (-1168))) /\
  Mem.load Mint16signed memory surface 16 = Some (Vint (Int.repr 1273)) /\
  Mem.load Mint16signed memory surface 20 = Some (Vint (Int.repr (-1089))) /\
  Mem.load Mint16signed memory surface 22 = Some (Vint (Int.repr 1193)) /\
  Mem.load Mint16signed memory surface 26 = Some (Vint (Int.repr (-793))) /\
  Mem.load Mfloat32 memory surface 28 = Some (Vsingle Float32.zero) /\
  Mem.load Mfloat32 memory surface 32 = Some (Vsingle (Float32.of_int Int.one)) /\
  Mem.load Mfloat32 memory surface 36 = Some (Vsingle Float32.zero) /\
  Mem.load Mfloat32 memory surface 40 = Some (Vsingle (Float32.of_int (Int.repr 2088))) /\
  Mem.load Mint16signed memory camera 0 = Some (Vint Int.zero).

Lemma clone_readable_node_nonnull : forall ce memory node,
  Mem.load Mptr memory node 0 = Some (Vint Int.zero) ->
  sem_binary_operation ce One (Vptr node Ptrofs.zero)
    (tptr (Tstruct CF._SurfaceNode noattr)) (Vint Int.zero) (tptr tvoid) memory =
    Some (Vint Int.one).
Proof.
  intros ce memory node Hload.
  assert (Hvalid : Mem.weak_valid_pointer memory node 0 = true).
  { pose proof (Mem.load_valid_access _ _ _ _ _ Hload) as [Hr Ha].
    apply Mem.valid_pointer_implies. apply Mem.valid_pointer_nonempty_perm.
    eapply Mem.perm_implies; [apply Hr; change (0 <= 0 < 4); lia | constructor]. }
  change (sem_binary_operation ce One (Vptr node Ptrofs.zero)
    (tptr (Tstruct us_mario._Surface noattr)) (Vint Int.zero) (tptr tvoid) memory =
    Some (Vint Int.one)).
  apply cog_surface_nonnull. exact Hvalid.
Qed.

Lemma clone_cog_plane_height :
  Float32.div
    (Float32.neg (Float32.add
      (Float32.add (Float32.mul (Float32.of_int (Int.repr 1330)) Float32.zero)
        (Float32.mul Float32.zero (Float32.of_int (Int.repr (-1025)))))
      (Float32.of_int (Int.repr 2088))))
    (Float32.of_int Int.one) = Float32.of_int (Int.repr (-2088)).
Proof.
  rewrite <- (Float32.of_to_bits (Float32.div _ _)).
  rewrite <- (Float32.of_to_bits (Float32.of_int (Int.repr (-2088)))).
  f_equal.
Qed.

Ltac clone_operation :=
  first [solve [eapply clone_readable_node_nonnull; eassumption] |
    solve [cbn; reflexivity] |
    match goal with |- ?G => idtac "CLONE OPERATION" G end; fail 100].
Ltac clone_check tac :=
  first [solve [tac] | match goal with |- ?G => idtac "CLONE ATOMIC" G end; fail 100].
Ltac clone_expr :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Econst_single _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ =>
      eapply eval_Etempvar; first [apply PTree.gss | cbn; reflexivity]
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop; [clone_expr | clone_expr | clone_operation]
  | |- eval_expr _ _ _ _ (Eunop _ _ _) _ =>
      eapply eval_Eunop; [clone_expr | clone_operation]
  | |- eval_expr _ _ _ _ (Ecast _ _) _ =>
      eapply eval_Ecast; [clone_expr | clone_operation]
  | |- eval_expr _ _ _ _ _ _ =>
      eapply eval_Elvalue; [clone_lvalue |
        first [eapply deref_loc_value; [reflexivity | cbn; clone_check cog_memory_load]
              |eapply deref_loc_reference; reflexivity
              |eapply deref_loc_copy; reflexivity]]
  end
with clone_lvalue :=
  lazymatch goal with
  | |- eval_lvalue _ _ _ _ (Evar _ _) _ _ _ =>
      eapply eval_Evar_global; [reflexivity | eassumption]
  | |- eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ => eapply eval_Ederef; clone_expr
  | |- eval_lvalue _ _ _ _ (Efield _ _ _) _ _ _ =>
      eapply eval_Efield_struct; [clone_expr | reflexivity | clone_check ltac:(eassumption) | clone_check ltac:(eassumption)]
  end.
Ltac clone_query_stmt :=
  lazymatch goal with |- exec_stmt ?entry ?ge ?e ?le ?m ?s ?t ?le' ?m' ?out =>
    let body := eval hnf in s in change (exec_stmt entry ge e le m body t le' m' out) end;
  lazymatch goal with
  | |- exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      eapply exec_Sloop_stop1 with (out' := Out_break);
      [clone_query_stmt | constructor]
  | |- exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      first [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
               [clone_query_stmt | clone_query_stmt]
            |eapply exec_Sseq_2; [clone_query_stmt | discriminate]]
  | |- exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse;
        [clone_expr | cbn; reflexivity | cog_reduce_statement; clone_query_stmt]
  | |- exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ => eapply exec_Sset; clone_expr
  | |- exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ =>
      eapply exec_Sassign; [clone_lvalue | clone_expr | cbn; reflexivity |
        eapply assign_loc_value; [reflexivity |
          cbn; clone_check ltac:(first [eassumption | rewrite clone_cog_plane_height; eassumption])]]
  | |- exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      eapply exec_Sreturn_some; clone_expr
  | _ => constructor
  end.

Definition published_cog_floor_execution_claim version : Prop :=
  forall (ge : Clight.genv) before node surface camera height_cell,
    clone_query_layout version (genv_cenv ge) ->
    Genv.find_symbol ge CF._gCheckingSurfaceCollisionsForCamera = Some camera ->
    published_cog_floor_image before node surface camera ->
    Mem.valid_access before Mfloat32 height_cell 0 Writable ->
    exists after,
      eval_funcall function_entry2 ge before
        (Internal (clone_floor_search_function version))
        [Vptr node Ptrofs.zero; Vint (Int.repr 1330); Vint (Int.repr (-2088));
         Vint (Int.repr (-1025)); Vptr height_cell Ptrofs.zero]
        E0 after (Vptr surface Ptrofs.zero) /\
      Mem.store Mfloat32 before height_cell 0
        (Vsingle (Float32.of_int (Int.repr (-2088)))) = Some after.

(** A published triangle can still be selected regardless of the associated
    object's position, hitbox tangibility, collisionData or behavior. Those
    Object fields are absent from the execution premises. Its OLD plane is
    selected; changing Object position alone does not translate that plane. *)
Theorem generated_published_cog_floor_selected_us_jp :
  forall version, published_cog_floor_execution_claim version.
Proof.
  intros version ge before node surface camera height_cell Hlayout Hcamera Himage Hwrite.
  destruct (Mem.valid_access_store before Mfloat32 height_cell 0
    (Vsingle (Float32.of_int (Int.repr (-2088)))) Hwrite) as [after Hstore].
  exists after. split; [|exact Hstore].
  destruct Hlayout. unfold published_cog_floor_image in Himage.
  decompose [and] Himage. clear Himage.
  destruct version; cbn [clone_floor_search_function clone_normal_tag] in *.
  all: eapply eval_funcall_internal;
    [action_entry | simpl fn_body; timeout 20 clone_query_stmt |
     cbn; split; [discriminate | reflexivity] | cbn; reflexivity].
Qed.

Definition clone_break_dispatch_claim version : Prop :=
  first_loop_parts (fn_body (match version with
    | VersionUS => CB.f_cur_obj_update | VersionJP => jp_behavior_script.f_cur_obj_update end)) =
    Some (cur_obj_update_dispatch_body, cur_obj_update_dispatch_continue_test) /\
  forall (ge : Clight.genv) locals memory cursor script table handler,
    Genv.find_symbol ge CB._gCurBhvCommand = Some cursor ->
    Genv.find_symbol ge CB._BehaviorCmdTable = Some table ->
    Mem.load Mptr memory cursor 0 = Some (Vptr script (Ptrofs.repr 4)) ->
    Mem.load Mint32 memory script 4 = Some (Vint (Int.repr 167772160)) ->
    Mem.load Mptr memory table 40 = Some (Vptr handler Ptrofs.zero) ->
    Genv.find_funct_ptr ge handler = Some (Internal (clone_break_function version)) ->
    exists final_locals,
      exec_stmt function_entry2 ge (PTree.empty _) locals memory
        (Sloop cur_obj_update_dispatch_body cur_obj_update_dispatch_continue_test)
        E0 final_locals memory Out_normal /\
      final_locals ! CB._bhvProcResult = Some (Vint Int.one).

(** Execute the real command loop at the released clone's BREAK word. This
    includes the indirect table call and the loop exit, with no assumed
    callee execution. It does not include BEGIN, script installation, or
    cur_obj_update's surrounding generic flag, timer and graphics work. *)
Theorem generated_clone_break_dispatch_us_jp :
  forall version, clone_break_dispatch_claim version.
Proof.
  intro version. split.
  - destruct version; reflexivity.
  - intros ge locals memory cursor script table handler
      Hcursor_symbol Htable_symbol Hcursor Hopcode Htable Hhandler.
    eexists. split.
    + eapply exec_Sloop_stop2 with (out1 := Out_normal) (out2 := Out_break)
        (t1 := E0) (t2 := E0).
      * unfold cur_obj_update_dispatch_body.
        repeat (eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)).
        -- eapply exec_Sset. clone_expr.
        -- eapply exec_Sset. clone_expr.
        -- eapply exec_Sset. clone_expr.
        -- eapply exec_Scall.
           ++ reflexivity.
           ++ eapply eval_Etempvar. apply PTree.gss.
           ++ constructor.
           ++ unfold Genv.find_funct. cbn. exact Hhandler.
           ++ destruct version; reflexivity.
           ++ apply generated_clone_break_preserves_all_memory_us_jp.
        -- eapply exec_Sset. eapply eval_Etempvar. apply PTree.gss.
      * constructor.
      * unfold cur_obj_update_dispatch_continue_test.
        eapply exec_Sifthenelse with (b := false).
        -- clone_expr.
        -- reflexivity.
        -- constructor.
      * constructor.
    + apply PTree.gss.
Qed.
