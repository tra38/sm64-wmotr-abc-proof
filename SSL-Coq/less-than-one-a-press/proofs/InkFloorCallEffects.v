(** Complete find_floor effects in the selected program. The two stack
    heights and the three named counter/flag globals are accounted for;
    every real list call is resolved and framed by InkFloorListEffects.
    No live-list completeness or result-selection premise is used here. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes InkFloorListEffects
  InkCopyEntry InkCopyCaller InkLateCallExecution ObjectContactNecessity
  SecretContactExecution UpperElevatorQueryResolution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ifc_surface := tptr (Tstruct IFL._Surface noattr).
Definition ifc_list_type := Tfunction
  [tptr (Tstruct IFL._SurfaceNode noattr); tint; tint; tint; tptr tfloat]
  ifc_surface cc_default.
Definition ifc_globals :=
  [IFL._gFindFloorIncludeSurfaceIntangible; IFL._gNumFindFloorMisses; IFL._gNumCalls].
Definition ifc_names := [IFL._height; IFL._dynamicHeight] ++ ifc_globals.
Definition ifc_member id ids := existsb (Pos.eqb id) ids.

Lemma ifc_member_in : forall id ids, ifc_member id ids = true -> In id ids.
Proof.
  intros id ids H. apply existsb_exists in H as (other & Hin & Heq).
  apply Pos.eqb_eq in Heq. congruence.
Qed.

Definition ifc_root lhs := match lhs with
  | Evar id _ => Some id
  | Efield (Evar id (Tstruct _ _)) _ _ => Some id
  | _ => None end.
Definition ifc_named_write lhs := match access_mode (typeof lhs), ifc_root lhs with
  | By_value _, Some id => ifc_member id ifc_names
  | _, _ => false end.
Definition ifc_write lhs :=
  ifl_pointer_write IFL._pfloor ifc_surface lhs || ifc_named_write lhs.
Definition ifc_height_arg args := match args with
  | [_; _; _; _; Eaddrof (Evar id ty) pty] =>
      ifc_member id [IFL._height; IFL._dynamicHeight] &&
      (if type_eq ty tfloat then if type_eq pty (tptr tfloat) then true else false else false)
  | _ => false end.
Definition ifc_call fn args := ilh_named IFL._find_floor_from_list ifc_list_type fn
  && ifc_height_arg args.

Lemma ifc_source : forall version,
  fn_vars (ueqr_native_body version UEQRFindFloor) =
    [(IFL._height, tfloat); (IFL._dynamicHeight, tfloat)] /\
  fn_params (ueqr_native_body version UEQRFindFloor) =
    [(IFL._xPos, tfloat); (IFL._yPos, tfloat); (IFL._zPos, tfloat);
     (IFL._pfloor, tptr ifc_surface)] /\
  ifl_shape IFL._pfloor ifc_write ifc_call
    (fn_body (ueqr_native_body version UEQRFindFloor)) = true.
Proof. intros []; repeat split; reflexivity. Qed.

(** Explicit separation of a protected cell from actual named destinations.
    This is an internal lemma interface, derived from entry allocations and
    symbol identity in the complete-call theorem below. *)
Definition ifc_name_separation (ge : genv) (e : env) b := forall id,
  In id ifc_names ->
  (forall target ty, e ! id = Some (target, ty) -> target <> b) /\
  (e ! id = None -> Genv.find_symbol ge id <> Some b).

Lemma ifc_variable_block : forall (ge : genv) (e : env) le m id ty loc ofs bf b,
  (forall target ty, e ! id = Some (target, ty) -> target <> b) ->
  (e ! id = None -> Genv.find_symbol ge id <> Some b) ->
  eval_lvalue ge e le m (Evar id ty) loc ofs bf -> loc <> b.
Proof.
  intros ge e le m id ty loc ofs bf b Hlocal Hglobal Hloc.
  inversion Hloc; subst.
  - eapply Hlocal; eauto.
  - intro Heq; subst. eapply Hglobal; eauto.
Qed.

Lemma ifc_root_block : forall (ge : genv) (e : env) le m lhs id loc ofs bf b,
  ifc_root lhs = Some id ->
  (forall target ty, e ! id = Some (target, ty) -> target <> b) ->
  (e ! id = None -> Genv.find_symbol ge id <> Some b) ->
  eval_lvalue ge e le m lhs loc ofs bf -> loc <> b.
Proof.
  intros ge e le m lhs id loc ofs bf b Hroot Hlocal Hglobal Hloc.
  destruct lhs; cbn [ifc_root] in Hroot; try discriminate.
  - inversion Hroot; subst. eapply ifc_variable_block; eauto.
  - destruct lhs; try discriminate. destruct t0; try discriminate.
    inversion Hroot; subst. inversion Hloc; subst; try discriminate.
    match goal with Hr : eval_expr _ _ _ _ (Evar _ _) _ |- _ =>
      inversion Hr; subst; clear Hr end.
    match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
      cbn [typeof] in Hd; inversion Hd; subst; try discriminate end.
    all: try solve [match goal with
      Hbad : eval_lvalue _ _ _ _ (Evar _ _) _ _ (Bits _ _ _ _) |- _ => inversion Hbad end].
    eapply ifc_variable_block; eauto.
Qed.

Lemma ifc_named_store_frame : forall ge e le m lhs rhs t le' m' out chunk b ofs,
  ifc_name_separation ge e b -> ifc_named_write lhs = true ->
  ocn_exec ge e le m (Sassign lhs rhs) t le' m' out ->
  t = E0 /\ Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros ge e le m lhs rhs t le' m' out chunk b ofs Hseparate Hallowed Hrun.
  unfold ifc_named_write in Hallowed.
  destruct (access_mode (typeof lhs)) eqn:Hmode; try discriminate.
  destruct (ifc_root lhs) as [id|] eqn:Hroot; try discriminate.
  apply ifc_member_in in Hallowed.
  destruct (Hseparate id Hallowed) as [Hlocal Hglobal].
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ lhs ?loc _ _ |- _ =>
    assert (loc <> b) as Hother by (eapply ifc_root_block; eauto) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
  - split; [reflexivity|]. eapply Mem.load_store_other; [eassumption|left; congruence].
  - congruence.
  - match goal with Hb : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hb; subst end.
    split; [reflexivity|]. eapply Mem.load_store_other; [eassumption|left; congruence].
Qed.

Lemma ifc_height_arg_exact : forall args, ifc_height_arg args = true ->
  exists a x y z id, args = [a; x; y; z; Eaddrof (Evar id tfloat) (tptr tfloat)] /\
    In id [IFL._height; IFL._dynamicHeight].
Proof.
  intros [|a [|x [|y [|z [|last rest]]]]]; try discriminate.
  destruct rest; try discriminate.
  all: destruct last; try discriminate.
  all: destruct last; try discriminate.
  cbn [ifc_height_arg].
  intros H. apply andb_true_iff in H as [Hid Htypes].
  destruct (type_eq t0 tfloat); try discriminate.
  destruct (type_eq t (tptr tfloat)); try discriminate. subst.
  do 5 eexists. split; [reflexivity|]. apply ifc_member_in. exact Hid.
Qed.

Lemma ifc_list_call_frame : forall version e le m opt fn args t le' m' out
    hb db chunk b ofs,
  e ! IFL._find_floor_from_list = None ->
  e ! IFL._height = Some (hb, tfloat) ->
  e ! IFL._dynamicHeight = Some (db, tfloat) -> hb <> b -> db <> b ->
  ifc_call fn args = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Scall opt fn args) t le' m' out ->
  t = E0 /\ Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version e le m opt fn args t le' m' out hb db chunk b ofs
    Hlocal Hheight Hdynamic Hhb Hdb Hallowed Hrun.
  apply andb_true_iff in Hallowed as [Hfn Hargs].
  apply ilh_named_exact in Hfn. subst fn.
  destruct (ifc_height_arg_exact args Hargs) as (a & x & y & z & id & -> & Hid).
  assert (exists target, e ! id = Some (target, tfloat) /\ target <> b) as Htarget.
  { destruct Hid as [<-|[<-|[]]]; eauto. }
  destruct Htarget as (target & Henv & Hdifferent).
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (upper_elevator_selected_query_body_resolves version UEQRFindFloorFromList)
    as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hr : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Hr; subst; clear Hr end.
  match goal with Hr : eval_expr _ _ _ _ (Eaddrof _ _) _ |- _ =>
    inversion Hr; subst; clear Hr end.
  all: try solve [match goal with
    Hbad : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion Hbad end].
  lazymatch goal with Hl : eval_lvalue _ _ _ _ (Evar id tfloat) _ _ _ |- _ =>
    destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ Henv Hl) as (Hblock & Hoffset & _);
    subst end.
  match goal with Hcast : sem_cast (Vptr _ _) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ (Internal _) _ _ _ _ |- _ =>
    destruct (ifl_completed_list_only_writes_height _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as (Ht & Hframe); split; [exact Ht|]; apply Hframe; left; congruence end.
Qed.

Lemma ifc_body_frame : forall version e le m hb db pb po chunk b ofs t le' m' out,
  e ! IFL._find_floor_from_list = None ->
  e ! IFL._height = Some (hb, tfloat) -> e ! IFL._dynamicHeight = Some (db, tfloat) ->
  hb <> b -> db <> b -> ifc_name_separation (Clight.globalenv (selected_clight_target version)) e b ->
  le ! IFL._pfloor = Some (Vptr pb po) ->
  ifl_disjoint pb (Ptrofs.unsigned po) 4 chunk b ofs ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ueqr_native_body version UEQRFindFloor)) t le' m' out ->
  t = E0 /\ Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version e le m hb db pb po chunk b ofs t le' m' out
    Hlocal Hheight Hdynamic Hhb Hdb Hnames Hptr Houtside Hrun.
  destruct (ifl_checked_frame (Clight.globalenv (selected_clight_target version)) e
    IFL._pfloor (Vptr pb po) (fun memory => Mem.load chunk memory b ofs)
    ifc_write ifc_call
    ltac:(intros temps memory lhs rhs tr last after outcome Hp Hw Hs;
      apply orb_true_iff in Hw as [Hw|Hw];
      [apply ifl_pointer_write_exact in Hw; subst lhs;
       destruct (ifl_pointer_store _ _ _ _ _ ifc_surface Mint32 _ _ _ _ _ _ _ Hp eq_refl Hs)
         as (Ht & value & Hstore); split; [exact Ht|];
       eapply Mem.load_store_other; [exact Hstore|exact Houtside]
      |eapply ifc_named_store_frame; eauto])
    ltac:(intros; eapply ifc_list_call_frame; eauto)
    _ _ _ _ _ _ _ Hrun (proj2 (proj2 (ifc_source version))) Hptr)
    as (Ht & Hframe & _). auto.
Qed.

Lemma ifc_free_list_frame : forall frees m m' chunk b ofs,
  Forall (fun '(target, _, _) => target <> b) frees ->
  Mem.free_list m frees = Some m' -> Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction frees as [|[[target lo] hi] rest IH]; intros m m' chunk b ofs Hblocks Hfree.
  - cbn in Hfree. inversion Hfree. reflexivity.
  - inversion Hblocks; subst. cbn in Hfree.
    destruct (Mem.free m target lo hi) as [middle|] eqn:Hone; try discriminate.
    match goal with Hrest : Forall _ rest |- _ => rewrite (IH _ _ _ _ _ Hrest Hfree) end.
    eapply Mem.load_free; [exact Hone|left; congruence].
Qed.

Theorem ifc_completed_floor_preserves_other_cells : forall version m x y z pb po t m' result
    chunk b ofs,
  Mem.valid_block m b ->
  (forall id, In id ifc_globals ->
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) id <> Some b) ->
  ifl_disjoint pb (Ptrofs.unsigned po) 4 chunk b ofs ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ueqr_native_body version UEQRFindFloor))
    [x; y; z; Vptr pb po] t m' result ->
  t = E0 /\ Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version m x y z pb po t m' result chunk b ofs Hvalid Hglobals Houtside Hcall.
  destruct (ifc_source version) as (Hvars & Hparams & _).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ (_ :: _) _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ [] _ _ |- _ => inversion Ha; subst; clear Ha end.
  lazymatch type of Hvalid with Mem.valid_block ?initial b =>
  lazymatch goal with Ha : Mem.alloc initial 0 _ = (?middle, ?hb),
    Hb : Mem.alloc ?middle 0 _ = (?entry, ?db) |- _ =>
    assert (hb <> b) as Hhb by
      (intro Heq; subst hb; exact (Mem.fresh_block_alloc _ _ _ _ _ Ha Hvalid));
    assert (Mem.valid_block middle b) as HmiddleValid by
      (eapply Mem.valid_block_alloc; [exact Ha|exact Hvalid]);
    assert (db <> b) as Hdb by
      (intro Heq; subst db; exact (Mem.fresh_block_alloc _ _ _ _ _ Hb HmiddleValid));
    assert (Mem.load chunk entry b ofs = Mem.load chunk initial b ofs) as HallocFrame by
      (erewrite Mem.load_alloc_unchanged; [|exact Hb|exact HmiddleValid];
       eapply Mem.load_alloc_unchanged; eauto)
  end end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IFL._pfloor = Some (Vptr pb po)) as Hptr by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb; apply PTree.gss) end.
  lazymatch goal with Hr : ClightBigstep.exec_stmt _ _ ?locals _ _ (fn_body _) _ _ _ _ |- _ =>
    lazymatch locals with PTree.set _ (?db, _) (PTree.set _ (?hb, _) _) =>
    assert (ifc_name_separation (Clight.globalenv (selected_clight_target version)) locals b)
      as Hnames by
      (intros id Hin; cbn [ifc_names ifc_globals In] in Hin;
       destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
       cbn [PTree.get PTree.set empty_env PTree.empty]; split;
       try (intros target ty Heq; inversion Heq; subst; assumption);
       try (intros; discriminate);
       intro Hnone; apply Hglobals; cbn [ifc_globals In]; tauto);
    destruct (ifc_body_frame version locals _ _ hb db pb po chunk b ofs _ _ _ _
      eq_refl ltac:(rewrite PTree.gso by discriminate; apply PTree.gss)
      (PTree.gss _ _ _) Hhb Hdb Hnames Hptr Houtside Hr) as (Ht & HbodyFrame)
    end end.
  split; [exact Ht|].
  lazymatch goal with Hfree : Mem.free_list ?last (blocks_of_env ?ge ?locals) = Some ?answer |- _ =>
    rewrite (ifc_free_list_frame (blocks_of_env ge locals) last answer chunk b ofs ltac:(
      lazymatch locals with PTree.set _ (?db, _) (PTree.set _ (?hb, _) _) =>
        first [change (Forall (fun '(target, _, _) => target <> b) [(hb, 0, 4); (db, 0, 4)])
          |change (Forall (fun '(target, _, _) => target <> b) [(db, 0, 4); (hb, 0, 4)])];
        repeat constructor; assumption
      end) Hfree)
  end.
  congruence.
Qed.

(** For an ordinary MarioState symbol, separation from all three globals is
    a consequence of distinct generated identifiers, not an extra premise. *)
Theorem ifc_floor_call_preserves_mario_position : forall version m mb x y z t m' result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Mem.valid_block m mb ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ueqr_native_body version UEQRFindFloor))
    [x; y; z; Vptr mb (Ptrofs.repr 104)] t m' result ->
  t = E0 /\ forall ofs, 60 <= ofs <= 68 ->
    Mem.load Mfloat32 m' mb ofs = Mem.load Mfloat32 m mb ofs.
Proof.
  intros version m mb x y z t m' result Hsymbol Hvalid Hcall.
  assert (forall ofs, 60 <= ofs <= 68 ->
    t = E0 /\ Mem.load Mfloat32 m' mb ofs = Mem.load Mfloat32 m mb ofs) as Hframe.
  { intros ofs Hrange. eapply ifc_completed_floor_preserves_other_cells; eauto.
    - intros id Hin Hsame.
      assert (us_object_list_processor._gMarioStates <> id) as Hids by
        (destruct Hin as [<-|[<-|[<-|[]]]]; discriminate).
      assert (mb <> mb) as Hcontra by (eapply Genv.global_addresses_distinct; eauto).
      exact (Hcontra eq_refl).
    - right; left. change (ofs + 4 <= 104). lia. }
  split; [exact (proj1 (Hframe 60 ltac:(lia)))|].
  intros; exact (proj2 (Hframe _ H)).
Qed.
