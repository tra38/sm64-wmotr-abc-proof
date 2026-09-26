(** The real stock play_sound implementation, generated from the complete
    pinned audio translation unit. Its completed execution only writes the
    request array and byte counter. Global-symbol injectivity supplies the
    separation from MarioState and all nine landing descriptors.

    This proves the C implementation's effect. The existing 38-unit target
    still declares play_sound external; it is not silently relinked here. *)
From Coq Require Import Bool List String ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated.runtime Require Import us_audio_external jp_audio_external.
From LessThanOneAPress.Generated Require Import us_mario jp_mario us_level_update.
From LessThanOneAPress.Proofs Require Import GameTypes InkPlatformWriteFrame
  InkLandingDescriptorAccess InkLandingCallerSource InkLandingHistoryGate
  ObjectContactNecessity SecretContactExecution.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module ISR := us_audio_external.

Definition isr_body version := match version with
| VersionUS => ISR.f_play_sound | VersionJP => jp_audio_external.f_play_sound end.
Definition isr_destinations := [ISR._sSoundRequests; ISR._sSoundRequestCount].
Definition isr_write lhs := match access_mode (typeof lhs), snd (ipw_roots lhs) with
| By_value _, Some (IPWvar id) => ipw_member id isr_destinations
| _, _ => false end.
Fixpoint isr_shape s := match s with
| Sskip | Sset _ _ => true
| Sassign lhs _ => isr_write lhs
| Ssequence a b => isr_shape a && isr_shape b
| _ => false end.

Theorem isr_real_bodies_only_write_the_sound_queue : forall version,
  fn_vars (isr_body version) = [] /\
  fn_params (isr_body version) = [(ISR._soundBits, tint); (ISR._pos, tptr tfloat)] /\
  fn_return (isr_body version) = tvoid /\
  isr_shape (fn_body (isr_body version)) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Definition isr_separate (ge : genv) b := forall id,
  In id isr_destinations -> Genv.find_symbol ge id <> Some b.

Lemma isr_actual_store_frame : forall ge le m lhs rhs t le' m' out chunk b ofs,
  isr_separate ge b -> isr_write lhs = true ->
  ocn_exec ge empty_env le m (Sassign lhs rhs) t le' m' out ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros ge le m lhs rhs t le' m' out chunk b ofs Hseparate Hshape Hrun.
  unfold isr_write in Hshape.
  destruct (access_mode (typeof lhs)) eqn:Hmode; try discriminate.
  destruct (snd (ipw_roots lhs)) as [[id|id]|] eqn:Hroot; try discriminate.
  apply ipw_member_spec in Hshape.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ lhs ?loc _ _ |- _ =>
    assert (loc <> b) as Hother by
      (eapply (proj2 (ipw_root_sound _ _ _ _)); [exact Hl|exact Hroot|];
       split; [intros; discriminate|intros _ target Hfind Heq; subst target;
         exact (Hseparate id Hshape Hfind)]) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
  - eapply Mem.load_store_other; [eassumption|left; congruence].
  - congruence.
  - match goal with Hb : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hb; subst end.
    eapply Mem.load_store_other; [eassumption|left; congruence].
Qed.

(** The game declaration and the generated definition have exactly the same
    C call interface. This does not turn the old external oracle into C. *)
Definition isr_type := Tfunction [tint; tptr tfloat] tvoid cc_default.
Definition isr_declaration : Clight.fundef :=
  External (EF_external "play_sound" (mksignature [AST.Xint; AST.Xptr] AST.Xvoid cc_default))
    [tint; tptr tfloat] tvoid cc_default.
Definition isr_find (definitions : list (ident * globdef Clight.fundef type)) :=
  find (fun entry => Pos.eqb (fst entry) ISR._play_sound) definitions.
Theorem isr_generated_interface_checked :
  isr_find us_mario.global_definitions = Some (ISR._play_sound, Gfun isr_declaration) /\
  isr_find jp_mario.global_definitions = Some (ISR._play_sound, Gfun isr_declaration) /\
  forall version, type_of_fundef (Internal (isr_body version)) = isr_type.
Proof. split; [reflexivity|]. split; [reflexivity|]. intros []; reflexivity. Qed.

Lemma isr_actual_body_frame : forall ge b,
  isr_separate ge b -> forall le m s t le' m' out,
  ocn_exec ge empty_env le m s t le' m' out -> isr_shape s = true ->
  t = E0 /\ out = Out_normal /\
  forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros ge b Hseparate le m s. revert le m.
  induction s; intros le m t le' m' out Hrun Hshape;
    cbn [isr_shape] in Hshape; try discriminate.
  - inversion Hrun; subst. repeat split; reflexivity.
  - split; [inversion Hrun; reflexivity|].
    split; [inversion Hrun; reflexivity|].
    intros. eapply isr_actual_store_frame; eassumption.
  - inversion Hrun; subst. repeat split; reflexivity.
  - apply andb_true_iff in Hshape as [Ha Hb]. inversion Hrun; subst.
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ s1 _ _ _ _ |- _ =>
        destruct (IHs1 _ _ _ _ _ _ Hr Ha) as (-> & _ & Hfirst) end.
      match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ s2 _ _ _ _ |- _ =>
        destruct (IHs2 _ _ _ _ _ _ Hr Hb) as (-> & -> & Hsecond) end.
    repeat split; try reflexivity. intros. rewrite Hsecond. apply Hfirst.
    + match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ s1 _ _ _ _ |- _ =>
        destruct (IHs1 _ _ _ _ _ _ Hr Ha) as (_ & Heq & _) end.
      contradiction.
Qed.

Theorem isr_completed_sound_request_preserves_other_blocks :
  forall version ge m args t m' result b,
  isr_separate ge b ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (isr_body version)) args t m' result ->
  t = E0 /\ forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros version ge m args t m' result b Hseparate Hcall.
  destruct (isr_real_bodies_only_write_the_sound_queue version) as (Hvars & Hparams & Hret & Hshape).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (isr_actual_body_frame ge b Hseparate _ _ _ _ _ _ _ Hr Hshape)
      as (Ht & _ & Hframe) end.
  split; assumption.
Qed.

Definition isr_game_globals := us_mario._gMarioState :: us_level_update._gMarioStates :: ildp_ids.
Theorem isr_game_globals_are_not_audio_destinations :
  forallb (fun id => negb (ipw_member id isr_destinations)) isr_game_globals = true.
Proof. vm_compute; reflexivity. Qed.

Lemma isr_named_game_global_is_separate : forall (ge : genv) id b,
  In id isr_game_globals -> Genv.find_symbol ge id = Some b -> isr_separate ge b.
Proof.
  intros ge id b Hin Hsymbol other Hother Hsame.
  assert (id <> other) as Hnames.
  { intros Heq; subst other.
    pose proof isr_game_globals_are_not_audio_destinations as Hcheck.
    apply forallb_forall with (x := id) in Hcheck; [|exact Hin].
    apply negb_true_iff in Hcheck. apply ipw_member_spec in Hother. congruence. }
  assert (b <> b) as Hbad by
    (eapply Genv.global_addresses_distinct; [exact Hnames|exact Hsymbol|exact Hsame]).
  exact (Hbad eq_refl).
Qed.

Definition StockSoundRequestGameFrame : Prop :=
  forall version (ge : genv) m args t m' result id b,
  In id isr_game_globals -> Genv.find_symbol ge id = Some b ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (isr_body version)) args t m' result ->
  t = E0 /\ forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs.

Theorem isr_real_sound_preserves_mario_and_landing_records : StockSoundRequestGameFrame.
Proof.
  intros version ge m args t m' result id b Hid Hsymbol Hcall.
  eapply isr_completed_sound_request_preserves_other_blocks; [|exact Hcall].
  eapply isr_named_game_global_is_separate; eassumption.
Qed.

(** Consume the proof at a real C callsite, with the same argument evaluation,
    memory, and return. Resolving play_sound to the stock body is an explicit
    link condition; the existing selected target still uses an external. *)
Definition StockSoundResolvedCallFrame : Prop :=
  forall version (ge : genv) fb id b le m opt args t le' m' out,
  Genv.find_symbol ge ISR._play_sound = Some fb ->
  Genv.find_funct_ptr ge fb = Some (Internal (isr_body version)) ->
  In id isr_game_globals -> Genv.find_symbol ge id = Some b ->
  ocn_exec ge empty_env le m (Scall opt (Evar ISR._play_sound isr_type) args)
    t le' m' out ->
  t = E0 /\ forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs.

Theorem isr_resolved_call_preserves_mario_and_landing_records : StockSoundResolvedCallFrame.
Proof.
  intros version ge fb id b le m opt args t le' m' out Hsymbol Hfunction Hid Hglobal Hrun.
  inversion Hrun; subst.
  match goal with H : classify_fun _ = _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (eapply (sce_function_name_value ge empty_env le m ISR._play_sound
        [tint; tptr tfloat] tvoid cc_default fb vf);
       [apply PTree.gempty|exact Hsymbol|exact H]); subst vf end.
  match goal with H : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr ge fb = Some fd) in H;
    rewrite Hfunction in H; inversion H; subst fd end.
  eapply isr_real_sound_preserves_mario_and_landing_records;
    [exact Hid|exact Hglobal|eassumption].
Qed.

Definition StockSoundImplementationBoundary : Prop :=
  StockSoundRequestGameFrame /\ StockSoundResolvedCallFrame /\
  (isr_find us_mario.global_definitions = Some (ISR._play_sound, Gfun isr_declaration) /\
   isr_find jp_mario.global_definitions = Some (ISR._play_sound, Gfun isr_declaration) /\
   forall version, type_of_fundef (Internal (isr_body version)) = isr_type).

Theorem isr_stock_sound_implementation_checked : StockSoundImplementationBoundary.
Proof.
  split; [exact isr_real_sound_preserves_mario_and_landing_records|].
  split; [exact isr_resolved_call_preserves_mario_and_landing_records|
    exact isr_generated_interface_checked].
Qed.
