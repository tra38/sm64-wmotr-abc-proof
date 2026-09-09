(** Shared execution, not a new movement model: extract the five actual
    preparation stages from one enabled execute_mario_action pass and build
    their continuous Clight2 small-step prefix. No stage is assumed harmless. *)
From Coq Require Import Bool Classical_Prop List ZArith.
From compcert Require Import AST Clight ClightBigstep Events Memory Smallstep.
From LessThanOneAPress.Generated Require Import us_mario jp_mario.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution ObjectContactNecessity Area2Rank12BContact
  ClightRefinement EntryMemory SelectedClightTarget.
Import ListNotations.

Definition iap_body version := match version with
| VersionUS => us_mario.f_execute_mario_action
| VersionJP => jp_mario.f_execute_mario_action end.

Definition iap_enabled version := match fn_body (iap_body version) with
| Ssequence _ (Ssequence (Ssequence _ (Ssequence _ (Sifthenelse _ yes _))) _) => yes
| _ => Sskip end.
Definition iap_stages version := ocn_prefix_items 5 (iap_enabled version).
Definition iap_after_preparation version := rank12b_drop_sequences 5 (iap_enabled version).

Definition iap_call_name s := match s with
| Ssequence (Sset read_temp (Evar global _))
    (Scall None (Evar callee _) [Etempvar arg_temp _]) =>
  if Pos.eqb global us_mario._gMarioState && Pos.eqb read_temp arg_temp
  then Some callee else None
| _ => None end.

Lemma iap_generated_preparation : forall version,
  iap_enabled version = ocn_prepend (iap_stages version) (iap_after_preparation version) /\
  forallb ibk_normal (iap_stages version) = true /\
  map iap_call_name (skipn 1 (iap_stages version)) =
    [Some us_mario._mario_reset_bodystate; Some us_mario._update_mario_inputs;
     Some us_mario._mario_handle_special_floors; Some us_mario._mario_process_interactions].
Proof. intros []; repeat split; reflexivity. Qed.

(** Each entry retains the actual statement execution and its full memory
    effect. Adjacent entries share exactly the same locals and memory. *)
Inductive iap_stage_chain (ge : genv) (e : env) :
  temp_env -> mem -> list statement -> trace -> temp_env -> mem -> Prop :=
| iap_chain_nil : forall le m, iap_stage_chain ge e le m [] E0 le m
| iap_chain_cons : forall le m s rest t1 middle memory t2 le' m',
    ocn_exec ge e le m s t1 middle memory Out_normal ->
    iap_stage_chain ge e middle memory rest t2 le' m' ->
    iap_stage_chain ge e le m (s :: rest) (t1 ++ t2) le' m'.

Lemma iap_split_stages : forall ge e items rest le m t le' m' out,
  forallb ibk_normal items = true ->
  ocn_exec ge e le m (ocn_prepend items rest) t le' m' out ->
  exists middle memory pre suf,
    t = pre ++ suf /\ iap_stage_chain ge e le m items pre middle memory /\
    ocn_exec ge e middle memory rest suf le' m' out.
Proof.
  intros ge e items. induction items as [|s items IH]; intros rest le m t le' m' out Hnormal Hrun.
  - exists le, m, E0, t. split; [reflexivity|]. split; [constructor|exact Hrun].
  - cbn in Hnormal. apply andb_true_iff in Hnormal as [Hhead Htail].
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hhead Hrun)
      as (one_le & one_m & one_t & rest_t & Htrace & Hfirst & Hrest).
    destruct (IH _ _ _ _ _ _ _ Htail Hrest)
      as (middle & memory & pre & suf & Htrace2 & Hchain & Hsuffix).
    exists middle, memory, (one_t ++ pre), suf. split.
    + rewrite Htrace, Htrace2, app_assoc. reflexivity.
    + split; [econstructor; eauto|exact Hsuffix].
Qed.

(** Locate the first changed depth observation in that same stage chain.
    No finite-value or successful-load premise discards invalid observations. *)
Definition iap_depth m mb := Mem.load Mfloat32 m mb mario_state_quicksand_depth_offset.

Lemma iap_first_changed_depth_stage : forall ge e le m items t le' m',
  iap_stage_chain ge e le m items t le' m' -> forall mb,
  iap_depth m' mb <> iap_depth m mb ->
  exists before stage after cut_le cut_m next_le next_m pre mid suf,
    items = before ++ stage :: after /\ t = pre ++ (mid ++ suf) /\
    iap_stage_chain ge e le m before pre cut_le cut_m /\
    iap_depth cut_m mb = iap_depth m mb /\
    ocn_exec ge e cut_le cut_m stage mid next_le next_m Out_normal /\
    iap_depth next_m mb <> iap_depth cut_m mb /\
    iap_stage_chain ge e next_le next_m after suf le' m'.
Proof.
  intros ge e le m items t le' m' Hchain.
  induction Hchain; intros mb Hchanged.
  - contradiction Hchanged. reflexivity.
  - destruct (classic (iap_depth memory mb = iap_depth m mb)) as [Hsame|Hdifferent].
    + destruct (IHHchain mb ltac:(congruence))
        as (before & stage & after & cut_le & cut_m & next_le & next_m & pre & mid & suf &
          Hitems & Htrace & Hprefix & Hread & Hstage & Hchange & Hsuffix).
      exists (s :: before), stage, after, cut_le, cut_m, next_le, next_m, (t1 ++ pre), mid, suf.
      split; [cbn; rewrite Hitems; reflexivity|].
      split; [rewrite Htrace, app_assoc; reflexivity|].
      split; [econstructor; eauto|]. split; [congruence|].
      split; [exact Hstage|]. split; assumption.
    + exists [], s, rest, le, m, middle, memory, E0, t1, t2.
      split; [reflexivity|]. split; [reflexivity|].
      split; [constructor|]. split; [reflexivity|].
      split; [exact H|]. split; assumption.
Qed.

Lemma iap_normal_statement_steps : forall program e le m s t le' m',
  ocn_exec (Clight.globalenv program) e le m s t le' m' Out_normal ->
  forall f k,
  @Smallstep.star _ _ Clight.step2 (Clight.globalenv program)
    (State f s k e le m) t (State f Sskip k e le' m').
Proof.
  intros program e le m s t le' m' Hrun f k.
  destruct (ClightBigstep.exec_stmt_steps Clight.function_entry2 program
    e le m s t le' m' Out_normal Hrun f k) as (last & Hsteps & Hout).
  inversion Hout; subst. exact Hsteps.
Qed.

Lemma iap_chain_steps : forall program e le m items t le' m',
  iap_stage_chain (Clight.globalenv program) e le m items t le' m' ->
  forall f k rest,
  @Smallstep.star _ _ Clight.step2 (Clight.globalenv program)
    (State f (ocn_prepend items rest) k e le m) t (State f rest k e le' m').
Proof.
  intros program e le m items t le' m' Hchain.
  induction Hchain; intros f k suffix.
  - apply star_refl.
  - cbn [ocn_prepend].
    eapply star_left; [apply step_seq| |reflexivity].
    eapply star_trans.
    + eapply iap_normal_statement_steps. exact H.
    + eapply star_left; [apply step_skip_seq|apply IHHchain|reflexivity].
    + reflexivity.
Qed.

Definition InkActionPassPreparationHistory : Prop :=
  forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iap_enabled version) t le' m' out ->
  exists ready_le ready_m pre suf,
    t = pre ++ suf /\
    iap_stage_chain (Clight.globalenv (selected_clight_target version)) e
      le m (iap_stages version) pre ready_le ready_m /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e ready_le ready_m
      (iap_after_preparation version) suf le' m' out /\
    (forall mb, iap_depth ready_m mb <> iap_depth m mb ->
      exists before stage after cut_le cut_m next_le next_m first mid last,
        iap_stages version = before ++ stage :: after /\ pre = first ++ (mid ++ last) /\
        iap_stage_chain (Clight.globalenv (selected_clight_target version)) e
          le m before first cut_le cut_m /\
        iap_depth cut_m mb = iap_depth m mb /\
        ocn_exec (Clight.globalenv (selected_clight_target version)) e cut_le cut_m
          stage mid next_le next_m Out_normal /\
        iap_depth next_m mb <> iap_depth cut_m mb /\
        iap_stage_chain (Clight.globalenv (selected_clight_target version)) e
          next_le next_m after last ready_le ready_m) /\
    forall k, exists run : ImportedClightRun,
      run_program run = selected_clight_target version /\
      run_start run = State (iap_body version) (iap_enabled version) k e le m /\
      run_trace run = pre /\
      run_final run = State (iap_body version) (iap_after_preparation version) k e ready_le ready_m.

Theorem iap_actual_pass_builds_shared_preparation_run : InkActionPassPreparationHistory.
Proof.
  unfold InkActionPassPreparationHistory.
  intros version e le m t le' m' out Hrun.
  destruct (iap_generated_preparation version) as (Hsource & Hnormal & Hnames).
  rewrite Hsource in Hrun.
  destruct (iap_split_stages _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (ready_le & ready_m & pre & suf & Htrace & Hchain & Hsuffix).
  exists ready_le, ready_m, pre, suf.
  split; [exact Htrace|]. split; [exact Hchain|]. split; [exact Hsuffix|].
  split.
  - intros mb Hchanged. eapply iap_first_changed_depth_stage; eauto.
  -
  intro k.
  assert (@Smallstep.star _ _ Clight.step2 (Clight.globalenv (selected_clight_target version))
    (State (iap_body version) (iap_enabled version) k e le m) pre
    (State (iap_body version) (iap_after_preparation version) k e ready_le ready_m)) as Hsteps.
  { rewrite Hsource. eapply iap_chain_steps. exact Hchain. }
  exists {| run_program := selected_clight_target version;
    run_start := State (iap_body version) (iap_enabled version) k e le m;
    run_trace := pre;
    run_final := State (iap_body version) (iap_after_preparation version) k e ready_le ready_m;
    run_steps := Hsteps |}.
  repeat split; reflexivity.
Qed.
