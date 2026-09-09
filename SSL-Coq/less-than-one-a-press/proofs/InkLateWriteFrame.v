(** A small execution checker for the real late helper bodies. Allowed writes
    and calls need semantic frames; the checker does not supply their effects. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkCopyCaller InkControllerEdge InkMarioInputFlag InkLandingHistoryGate
  InkLandingPostStep InkLandingContinuationSource InkFloorResetExecution
  ObjectContactNecessity EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ilw_fresh id kept := negb (existsb (Pos.eqb id) kept).
Definition ilw_refs kept (refs : ident -> option val) (le : temp_env) :=
  forall id, In id kept -> le ! id = refs id.
Fixpoint ilw_shape kept (write_ok : expr -> bool)
  (call_ok : expr -> list expr -> bool) (s : statement) : bool := match s with
| Sskip | Sreturn _ => true
| Sset id _ => ilw_fresh id kept
| Sassign lhs _ => write_ok lhs
| Scall opt fn args =>
    (match opt with None => true | Some id => ilw_fresh id kept end) && call_ok fn args
| Ssequence a b | Sifthenelse _ a b =>
    ilw_shape kept write_ok call_ok a && ilw_shape kept write_ok call_ok b
| _ => false end.

Lemma ilw_set_refs : forall kept refs le id v,
  ilw_refs kept refs le -> ilw_fresh id kept = true ->
  ilw_refs kept refs (PTree.set id v le).
Proof.
  intros kept refs le id v Hrefs Hfresh other Hin.
  unfold ilw_fresh in Hfresh. apply negb_true_iff in Hfresh.
  assert (id <> other) as Hneq.
  { intro Heq. subst other.
    assert (existsb (Pos.eqb id) kept = true) as Hyes.
    { apply existsb_exists. exists id. split; [exact Hin|apply Pos.eqb_refl]. }
    congruence. }
  rewrite PTree.gso by congruence. apply Hrefs; exact Hin.
Qed.

Theorem ilw_checked_body_frame : forall ge e kept refs write_ok call_ok mb mo,
  (forall le m lhs rhs t le' m' out,
    ilw_refs kept refs le -> write_ok lhs = true ->
    ocn_exec ge e le m (Sassign lhs rhs) t le' m' out ->
    ilh_timer_load m' mb mo = ilh_timer_load m mb mo) ->
  (forall le m opt fn args t le' m' out,
    ilw_refs kept refs le -> call_ok fn args = true ->
    ocn_exec ge e le m (Scall opt fn args) t le' m' out ->
    ilh_timer_load m' mb mo = ilh_timer_load m mb mo) ->
  forall le m s t le' m' out,
    ocn_exec ge e le m s t le' m' out ->
    ilw_shape kept write_ok call_ok s = true -> ilw_refs kept refs le ->
    ilh_timer_load m' mb mo = ilh_timer_load m mb mo /\ ilw_refs kept refs le'.
Proof.
  intros ge e kept refs write_ok call_ok mb mo Hwrite Hcall
    le m s t le' m' out Hrun.
  induction Hrun; cbn [ilw_shape]; intros Hshape Hrefs; try discriminate;
    try (split; [reflexivity|exact Hrefs]).
  - split; [eapply Hwrite; eauto; econstructor; eauto|exact Hrefs].
  - split; [reflexivity|]. eapply ilw_set_refs; eauto.
  - apply andb_true_iff in Hshape as [Hfresh Hallowed].
    split; [eapply Hcall; eauto; econstructor; eauto|].
    destruct optid; cbn; [eapply ilw_set_refs; eauto|exact Hrefs].
  - apply andb_true_iff in Hshape as [Ha Hb].
    destruct (IHHrun1 Hwrite Hcall Ha Hrefs) as [Hfirst Hmiddle].
    destruct (IHHrun2 Hwrite Hcall Hb Hmiddle) as [Hsecond Hfinal].
    split; [congruence|exact Hfinal].
  - apply andb_true_iff in Hshape as [Ha Hb]. auto.
  - apply andb_true_iff in Hshape as [Ha Hb]. destruct b; auto.
  Unshelve. all: exact None.
Qed.

Definition ilw_flags := Efield ibcc_state IBM._flags tuint.
Lemma ilw_flags_field : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IBM._MarioState IBM._flags 4 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IBM._flags 4 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.
Lemma ilw_flags_store_preserves_timer : forall version e le m mb mo rhs t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) -> imf_room mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign ilw_flags rhs) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version e le m mb mo rhs t le' m' out Hm Hroom Hrun.
  inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue ?ge ?env ?temps ?memory _ _ _ _ |- _ =>
    destruct (ice_field_location ge env temps memory IBM._m IBM._MarioState
      IBM._flags tuint mb mo 4 _ _ _ Hm (ilw_flags_field version) Hl)
      as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  unfold ilh_timer_load. eapply Mem.load_store_other; [eassumption|].
  right. right. cbn [size_chunk]. rewrite !imf_address by (auto; lia). lia.
Qed.

Definition ilw_sound_write lhs := match lhs with
| Efield (Ederef (Etempvar id pty) sty) field fty =>
    if Pos.eq_dec id IBM._m then
    if type_eq pty (tptr (Tstruct IBM._MarioState noattr)) then
    if type_eq sty (Tstruct IBM._MarioState noattr) then
    if type_eq fty tuint then
      Pos.eqb field IBM._flags || Pos.eqb field IBM._particleFlags
    else false else false else false else false
| _ => false end.

Lemma ilw_sound_write_cases : forall lhs, ilw_sound_write lhs = true ->
  lhs = ilw_flags \/ lhs = ilc_dust_field.
Proof.
  intro lhs. unfold ilw_sound_write.
  destruct lhs; try discriminate.
  destruct lhs; try discriminate.
  destruct lhs; try discriminate.
  repeat match goal with |- context [if ?test then _ else _] =>
    destruct test; try discriminate; subst end.
  intro Hfields. apply orb_true_iff in Hfields as [Hflag|Hparticle];
    apply Pos.eqb_eq in Hflag || apply Pos.eqb_eq in Hparticle;
    subst; [left|right]; reflexivity.
Qed.

Lemma ilw_sound_write_frame : forall version e le m mb mo lhs rhs t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) -> imf_room mo ->
  ilw_sound_write lhs = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign lhs rhs) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros version e le m mb mo lhs rhs t le' m' out Hm Hroom Hshape Hrun.
  destruct (ilw_sound_write_cases lhs Hshape) as [Hflag | Hparticle]; subst lhs.
  - eapply ilw_flags_store_preserves_timer; eauto.
  - eapply ilp_particle_store_preserves_timer; eauto.
Qed.
