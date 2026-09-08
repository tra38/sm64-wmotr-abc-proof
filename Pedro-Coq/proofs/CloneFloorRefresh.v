From Coq Require Import List ZArith.
From compcert Require Import AST Clight Clightdefs ClightBigstep Cop Ctypes
  Errors Events Globalenvs Integers Maps Memory Values.
From Pedro.Generated Require Import
  us_mario jp_mario us_surface_collision jp_surface_collision
  us_object_helpers jp_object_helpers
  us_surface_load jp_surface_load us_object_list_processor jp_object_list_processor.
From Pedro.Proofs Require Import ASTFacts GameTypes GroundGapReturn
  TTCCogExecution CogActionExecution.
Import ListNotations.
Open Scope Z_scope.
Module FR := us_surface_collision.
Module FM := us_mario.
Module FL := us_surface_load.
Module FO := us_object_list_processor.

Definition clone_nonholdable_branch version : option (expr * statement) :=
  match fn_body (match version with
    | VersionUS => us_object_helpers.f_obj_set_held_state
    | VersionJP => jp_object_helpers.f_obj_set_held_state end) with
  | Ssequence _ (Ssequence _ (Sifthenelse guard _ released)) => Some (guard, released)
  | _ => None end.

(** Exact guard and non-holdable branch. This ties the BREAK-script analysis
    to obj_set_held_state, without assuming an execution of its unresolved
    segmented_to_virtual address conversion. *)
Definition clone_nonholdable_source_claim : Prop :=
  forall version, clone_nonholdable_branch version =
    Some
      (Ebinop Oand (Etempvar us_object_helpers._t'2 tuint)
        (Ebinop Oshl (Econst_int (Int.repr 1) tint)
          (Econst_int (Int.repr 10) tint) tint) tuint,
       Ssequence
        (Ssequence
          (Scall (Some us_object_helpers._t'1)
            (Evar us_object_helpers._segmented_to_virtual
              (Tfunction [tptr tvoid] (tptr tvoid) cc_default))
            [Etempvar us_object_helpers._heldBehavior (tptr tuint)])
          (Sassign
            (Efield (Ederef
              (Etempvar us_object_helpers._obj (tptr (Tstruct us_object_helpers._Object noattr)))
              (Tstruct us_object_helpers._Object noattr))
              us_object_helpers._curBhvCommand (tptr tuint))
            (Etempvar us_object_helpers._t'1 (tptr tvoid))))
        (Sassign
          (Efield (Ederef
            (Etempvar us_object_helpers._obj (tptr (Tstruct us_object_helpers._Object noattr)))
            (Tstruct us_object_helpers._Object noattr))
            us_object_helpers._bhvStackIndex tuint)
          (Econst_int Int.zero tint))).

Theorem generated_nonholdable_script_replacement_us_jp : clone_nonholdable_source_claim.
Proof. intros []; reflexivity. Qed.

Definition clone_find_floor_function version : function :=
  match version with VersionUS => FR.f_find_floor
                   | VersionJP => jp_surface_collision.f_find_floor end.

(** Select the actual output-pointer reset after the coordinate casts and
    before either partition query. This is not a replacement floor routine. *)
Definition clone_floor_pointer_reset version : statement :=
  match ground_right_suffix 5 (fn_body (clone_find_floor_function version)) with
  | Ssequence first _ => first | _ => Sskip end.

Theorem generated_floor_pointer_reset_shape_us_jp :
  forall version, clone_floor_pointer_reset version =
    Sassign
      (Ederef (Etempvar FR._pfloor (tptr (tptr (Tstruct FR._Surface noattr))))
        (tptr (Tstruct FR._Surface noattr)))
      (Ecast (Econst_int Int.zero tint) (tptr tvoid)).
Proof. intros []; reflexivity. Qed.

Definition clone_floor_reset_execution_claim version : Prop :=
  forall (ge : Clight.genv) environment locals before mario,
    Mem.valid_access before Mptr mario 104 Writable ->
    exists after,
      exec_stmt function_entry2 ge environment
        (PTree.set FR._pfloor (Vptr mario (Ptrofs.repr 104)) locals) before
        (clone_floor_pointer_reset version) E0
        (PTree.set FR._pfloor (Vptr mario (Ptrofs.repr 104)) locals) after Out_normal /\
      Mem.load Mptr after mario 104 = Some (Vint Int.zero) /\
      (forall chunk other offset,
        other <> mario \/ offset + size_chunk chunk <= 104 \/ 108 <= offset ->
        Mem.load chunk after other offset = Mem.load chunk before other offset).

Definition clone_mario_floor_layout_receipt : Prop :=
  forall version,
    let ce := prog_comp_env (match version with VersionUS => FM.prog
                            | VersionJP => jp_mario.prog end) in
    field_offset ce FM._floor
      (match ce ! FM._MarioState with Some co => co_members co | None => [] end) =
      OK (104, Full).

Theorem clone_mario_floor_layout_generated_us_jp : clone_mario_floor_layout_receipt.
Proof. intros []; vm_compute; reflexivity. Qed.

(** A prior Mario floor reference is overwritten by the real query reset.
    Position, speed, particle flags, cog and seed cells outside this pointer
    cell are preserved by this statement. The complete query/caller remains
    a separate execution obligation. *)
Theorem generated_floor_query_resets_mario_floor_us_jp :
  forall version, clone_floor_reset_execution_claim version.
Proof.
  intros version ge environment locals before mario Hwrite.
  destruct (Mem.valid_access_store before Mptr mario 104 (Vint Int.zero) Hwrite)
    as [after Hstore].
  exists after. split.
  - rewrite generated_floor_pointer_reset_shape_us_jp.
    eapply exec_Sassign.
    + eapply eval_Ederef. eapply eval_Etempvar. apply PTree.gss.
    + eapply eval_Ecast; [constructor | reflexivity].
    + reflexivity.
    + eapply assign_loc_value; [reflexivity | exact Hstore].
  - split.
    + rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore). reflexivity.
    + intros chunk other offset Hapart.
      eapply Mem.load_store_other; [exact Hstore | exact Hapart].
Qed.

Fixpoint clone_named_call_arguments callee (body : statement) : list (list expr) :=
  match body with
  | Scall _ (Evar name _) args => if Pos.eqb name callee then [args] else []
  | Ssequence first rest | Sloop first rest =>
      clone_named_call_arguments callee first ++ clone_named_call_arguments callee rest
  | Sifthenelse _ yes no =>
      clone_named_call_arguments callee yes ++ clone_named_call_arguments callee no
  | Sswitch _ cases => clone_named_case_arguments callee cases
  | Slabel _ inner => clone_named_call_arguments callee inner
  | _ => [] end
with clone_named_case_arguments callee (cases : labeled_statements) : list (list expr) :=
  match cases with
  | LSnil => []
  | LScons _ body rest =>
      clone_named_call_arguments callee body ++ clone_named_case_arguments callee rest
  end.

Definition clone_mario_floor_address : expr :=
  Eaddrof
    (Efield (Ederef (Etempvar FM._m (tptr (Tstruct FM._MarioState noattr)))
      (Tstruct FM._MarioState noattr)) FM._floor (tptr (Tstruct FM._Surface noattr)))
    (tptr (tptr (Tstruct FM._Surface noattr))).

Definition clone_floor_refresh_source_claim version : Prop :=
  map (fun args => nth_error args 3)
    (clone_named_call_arguments FM._find_floor
      (fn_body (match version with VersionUS => FM.f_update_mario_geometry_inputs
                | VersionJP => jp_mario.f_update_mario_geometry_inputs end))) =
    repeat (Some clone_mario_floor_address) 2 /\
  calls_ident_s FM._update_mario_geometry_inputs
    (fn_body (match version with VersionUS => FM.f_update_mario_inputs
                | VersionJP => jp_mario.f_update_mario_inputs end)) = true /\
  direct_callees_s (fn_body (match version with VersionUS => FL.f_clear_dynamic_surfaces
                | VersionJP => jp_surface_load.f_clear_dynamic_surfaces end)) =
    [FL._clear_spatial_partition] /\
  filter (fun name => existsb (Pos.eqb name)
    [FO._clear_dynamic_surfaces; FO._update_terrain_objects;
     FO._update_non_terrain_objects])
    (direct_callees_s (fn_body (match version with VersionUS => FO.f_update_objects
                | VersionJP => jp_object_list_processor.f_update_objects end))) =
    [FO._clear_dynamic_surfaces; FO._update_terrain_objects; FO._update_non_terrain_objects].

Theorem generated_clone_floor_refresh_source_us_jp :
  forall version, clone_floor_refresh_source_claim version.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Definition clone_dynamic_clear_function version : function :=
  match version with VersionUS => FL.f_clear_dynamic_surfaces
                   | VersionJP => jp_surface_load.f_clear_dynamic_surfaces end.

(** Global Time Stop is a real exception: the original clear function performs
    no writes or calls. TTC's stopped-clock setting is a different variable. *)
Definition clone_time_stop_execution_claim version : Prop :=
  forall (ge : Clight.genv) memory time_state,
    Genv.find_symbol ge FL._gTimeStopState = Some time_state ->
    Mem.load Mint32 memory time_state 0 = Some (Vint (Int.repr 64)) ->
    eval_funcall function_entry2 ge memory (Internal (clone_dynamic_clear_function version))
      [] E0 memory Vundef.

Theorem generated_time_stop_retains_dynamic_lists_us_jp :
  forall version, clone_time_stop_execution_claim version.
Proof.
  intros version ge memory time_state Hsymbol Hload.
  destruct version; cbn [clone_dynamic_clear_function].
  all: eapply eval_funcall_internal;
    [action_entry | simpl fn_body; cog_stmt | cbn; reflexivity | cbn; reflexivity].
Qed.
