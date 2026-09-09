(** The real landing interval after the ground result.  Its last two calls
    are kept separate from the action reset and the final depth store. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Integers Maps.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkBackwardSource InkBackwardExecution InkCopyCaller InkFloorResetExecution
  InkLandingHistoryReturn InkQuicksandSource ObjectContactNecessity
  ContactConsumerExecution Area2Rank12BContact.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition ilc_prefix version := ocn_prefix_items 2 (fn_body (imb_body version IMBLanding)).
Definition ilc_after_ground version := rank12b_drop_sequences 2
  (fn_body (imb_body version IMBLanding)).
Definition ilc_dispatch version := ibk_head (ilc_after_ground version).
Definition ilc_after_dispatch version := rank12b_drop_sequences 3
  (fn_body (imb_body version IMBLanding)).
Definition ilc_dust version := ibk_head (ilc_after_dispatch version).
Definition ilc_animation version := ibk_head (rank12b_drop_sequences 4
  (fn_body (imb_body version IMBLanding))).
Definition ilc_sound version := ibk_head (rank12b_drop_sequences 5
  (fn_body (imb_body version IMBLanding))).
Definition ilc_after_sound version := rank12b_drop_sequences 6
  (fn_body (imb_body version IMBLanding)).
Definition ilc_depth_gate version := ibk_head (ilc_after_sound version).
Definition ilc_depth_probe version := match ilc_depth_gate version with
| Ssequence probe _ => probe | _ => Sskip end.
Definition ilc_depth_choice := Etempvar IMB._t'2 tint.
Definition ilc_return := Sreturn (Some (Etempvar IMB._stepResult tuint)).
Definition ilc_dust_field := Efield ibcc_state IMB._particleFlags tuint.
Definition ilc_dust_write := Sassign ilc_dust_field
  (Ebinop Oor (Etempvar IMB._t'10 tuint)
    (Ebinop Oshl (Econst_int Int.one tint) (Econst_int Int.zero tint) tint) tuint).

Definition ilc_action_call := Scall None
  (Evar IMB._set_mario_action ilh_set_action_type)
  [Etempvar IMB._m (tptr (Tstruct IMB._MarioState noattr));
   Etempvar IMB._airAction tuint; Econst_int Int.zero tint].

Definition ilc_cases version := match ilc_dispatch version with
| Sswitch _ cases => cases | _ => LSnil end.

Theorem ilc_source_cuts : forall version,
  fn_vars (imb_body version IMBLanding) = [] /\
  fn_params (imb_body version IMBLanding) =
    [(IMB._m, tptr (Tstruct IMB._MarioState noattr));
     (IMB._animation, tshort); (IMB._airAction, tuint)] /\
  fn_body (imb_body version IMBLanding) =
    ocn_prepend (ilc_prefix version) (ilc_after_ground version) /\
  forallb ibk_normal (ilc_prefix version) = true /\
  ifr_keeps_temp IMB._m (ocn_prepend (ilc_prefix version) Sskip) = true /\
  ilc_after_ground version = Ssequence (ilc_dispatch version) (ilc_after_dispatch version) /\
  ilc_dispatch version = Sswitch (Etempvar IMB._stepResult tuint) (ilc_cases version) /\
  ilc_after_dispatch version = Ssequence (ilc_dust version)
    (Ssequence (ilc_animation version) (Ssequence (ilc_sound version) (ilc_after_sound version))) /\
  ilc_after_sound version = Ssequence (ilc_depth_gate version) ilc_return /\
  ilc_depth_gate version = Ssequence (ilc_depth_probe version)
    (Sifthenelse ilc_depth_choice (imb_landing_write version) Sskip) /\
  cce_readonly_keep IMB._m (ilc_depth_probe version) = true /\
  ibk_normal (ilc_depth_probe version) = true /\
  forallb ibk_normal [ilc_dust version; ilc_animation version; ilc_sound version;
    ilc_depth_gate version] = true /\
  ifr_keeps_temp IMB._m (ilc_after_dispatch version) = true /\
  ifr_keeps_temp IMB._stepResult (ilc_after_dispatch version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem ilc_zero_case_starts_with_real_action_call : forall version,
  exists unused,
    seq_of_labeled_statement (select_switch 0 (ilc_cases version)) =
      Ssequence (Ssequence ilc_action_call Sbreak) unused.
Proof. intros []; eexists; reflexivity. Qed.

Theorem ilc_dust_source : forall version,
  exists test,
    ilc_dust version = Ssequence
      (Sset IMB._t'9 (Efield ibcc_state IMB._forwardVel tfloat))
      (Sifthenelse test
        (Ssequence (Sset IMB._t'10 ilc_dust_field) ilc_dust_write) Sskip).
Proof. intros []; eexists; reflexivity. Qed.

Theorem ilc_last_two_calls_are_named : forall version,
  exists animation_type animation_args sound_type sound_args,
    ilc_animation version = Scall None
      (Evar IMB._set_mario_animation animation_type) animation_args /\
    ilc_sound version = Scall None
      (Evar IMB._play_mario_landing_sound_once sound_type) sound_args.
Proof. intros []; do 4 eexists; split; reflexivity. Qed.
