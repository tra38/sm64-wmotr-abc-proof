From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes Floats Globalenvs Integers Maps Memory Values Events.
From LessThanOneAPress.Generated Require Import us_mario jp_mario us_mario_step jp_mario_step.
From LessThanOneAPress.Proofs Require Import Area2SlideKickEntry Area2Rank9ACoinFlight
  UpperElevatorQuarterStepClosure ObjectContactNecessity SelectedClightTarget GameTypes ASTFacts
  InkLandingHistoryReturn.
Import ListNotations.
Local Open Scope Z_scope.

(** Source receipts for the vertical recurrence. These check the real bodies,
    not substitute action functions. The live projection remains separate. *)
Fixpoint sk_case tag cases := match cases with
| LSnil => Sskip
| LScons label body rest =>
    match label with Some n => if Z.eqb tag n then body else sk_case tag rest
    | None => sk_case tag rest end
end.
Definition sk_initializer_case version := match
  fn_body (match version with VersionUS => us_mario.f_set_mario_action_airborne
    | VersionJP => jp_mario.f_set_mario_action_airborne end) with
| Ssequence _ (Ssequence (Sswitch _ cases) _) => sk_case 25168042 cases
| _ => Sskip end.
Fixpoint sk_velocity_writes s := match s with
| Sassign lhs rhs => if expression_is_array_slot SK._vel 1 lhs then [rhs] else []
| Ssequence a b | Sloop a b | Sifthenelse _ a b =>
    sk_velocity_writes a ++ sk_velocity_writes b
| Sswitch _ cases => sk_velocity_cases cases
| Slabel _ body => sk_velocity_writes body
| _ => [] end
with sk_velocity_cases cases := match cases with
| LSnil => [] | LScons _ body rest => sk_velocity_writes body ++ sk_velocity_cases rest end.
Fixpoint sk_if_temp id s := match s with
| Sifthenelse (Etempvar found _) yes no =>
    if Pos.eqb found id then Some yes else
    match sk_if_temp id yes with Some a => Some a | None => sk_if_temp id no end
| Ssequence a b | Sifthenelse _ a b =>
    match sk_if_temp id a with Some c => Some c | None => sk_if_temp id b end
| _ => None end.
Definition sk_gravity_branch version :=
  sk_if_temp us_mario_step._t'7 (fn_body (match version with
  | VersionUS => us_mario_step.f_apply_gravity
  | VersionJP => jp_mario_step.f_apply_gravity end)).
Definition sk_fconst bits := Econst_single (Float32.of_bits (Int.repr bits)) tfloat.

Theorem sk_vertical_source_receipts : forall version,
  sk_velocity_writes (sk_initializer_case version) = [sk_fconst 1094713344] /\
  sk_velocity_writes (fn_body (ske_body version)) =
    [Ebinop Odiv (Eunop Oneg (Etempvar SK._t'10 tfloat) tfloat)
       (sk_fconst 1073741824) tfloat; sk_fconst 0] /\
  exists gravity,
    sk_gravity_branch version = Some gravity /\
    sk_velocity_writes gravity =
      [Ebinop Osub (Etempvar us_mario_step._t'32 tfloat)
         (sk_fconst 1073741824) tfloat;
       Eunop Oneg (sk_fconst 1117126656) tfloat] /\
    calls_ident_s SK._perform_air_step (fn_body (ske_body version)) = true /\
    calls_ident_with_two_int_literals_s SK._set_mario_action 8389722 0
      (fn_body (ske_body version)) = true /\
    assigns_field_int_constant_s SK._actionTimer 0 (fn_body (ske_body version)) = true.
Proof. intros []; repeat split; try reflexivity; eexists; repeat split; reflexivity. Qed.

Theorem sk_source_constants_checked :
  Float32.to_bits (rank9cf_integer 12) = Int.repr 1094713344 /\
  Float32.to_bits (rank9cf_integer 2) = Int.repr 1073741824 /\
  Float32.to_bits (rank9cf_integer 75) = Int.repr 1117126656.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** Explicit vertical certificate. Each state uses eighth-unit integers so
    all quarter steps, including a half-unit rebound speed, can be checked
    against binary32 without expanding a large nested Float32 term. *)
Record SKVerticalState := {
  sk_y8 : Z; sk_floor8 : Z; sk_velocity8 : Z;
  sk_bounced : bool; sk_timer : Z; sk_active : bool
}.
Definition sk_float8 z := Float32.div (rank9cf_integer z) (rank9cf_integer 8).
Definition sk_next_floor s := sk_floor8 s - 80.
Definition sk_next_timer s := (sk_timer s + 1) mod 65536.
Definition sk_gap8 s := sk_y8 s - sk_next_floor s.
Definition sk_accept s :=
  (30 <? sk_next_timer s) && (4000 <? sk_gap8 s).

Fixpoint sk_quarters n y floor velocity : Z * bool := match n with
| O => (y,false)
| S rest =>
  let next := y + velocity / 4 in
  if next <=? floor then (floor,true)
  else sk_quarters rest next floor velocity
end.
Definition sk_next s :=
  let floor := sk_next_floor s in
  let '(y,landed) := sk_quarters 4 (sk_y8 s) floor (sk_velocity8 s) in
  let gravity := Z.max (sk_velocity8 s - 16) (-600) in
  if landed then
    if negb (sk_bounced s) && (gravity <? 0) then
      {| sk_y8 := y; sk_floor8 := floor; sk_velocity8 := -gravity / 2;
         sk_bounced := true; sk_timer := 0; sk_active := true |}
    else {| sk_y8 := y; sk_floor8 := floor; sk_velocity8 := gravity;
         sk_bounced := sk_bounced s; sk_timer := sk_next_timer s; sk_active := false |}
  else {| sk_y8 := y; sk_floor8 := floor; sk_velocity8 := gravity;
         sk_bounced := sk_bounced s; sk_timer := sk_next_timer s; sk_active := true |}.
Fixpoint sk_samples fuel s := match fuel with
| O => []
| S rest => if sk_active s then
    s :: (if sk_accept s then [] else sk_samples rest (sk_next s))
  else []
end.
Definition sk_normal_start :=
  {| sk_y8 := 32000; sk_floor8 := 32000; sk_velocity8 := 96;
     sk_bounced := false; sk_timer := 0; sk_active := true |}.
Definition sk_normal_samples := sk_samples 60 sk_normal_start.
Definition sk_hard_start :=
  {| sk_y8 := 16000; sk_floor8 := 16000; sk_velocity8 := 300;
     sk_bounced := true; sk_timer := 0; sk_active := true |}.
Definition sk_hard_samples := sk_samples 40 sk_hard_start.

Definition sk_bits_equal a b := Int.eq (Float32.to_bits a) (Float32.to_bits b).
Fixpoint sk_quarters_exact n y floor velocity : bool := match n with
| O => true
| S rest =>
  let next := y + velocity / 4 in
  sk_bits_equal
    (Float32.add (sk_float8 y)
      (Float32.div (sk_float8 velocity) (rank9cf_integer 4)))
    (sk_float8 next) &&
  Bool.eqb (Float32.cmp Cle (sk_float8 next) (sk_float8 floor)) (next <=? floor) &&
  (if next <=? floor then true else sk_quarters_exact rest next floor velocity)
end.
Definition sk_sample_exact s :=
  let v := sk_velocity8 s in
  let raw_gravity := v - 16 in
  let gravity := Z.max raw_gravity (-600) in
  sk_bits_equal (Float32.sub (sk_float8 (sk_floor8 s)) (rank9cf_integer 10))
    (sk_float8 (sk_next_floor s)) &&
  sk_bits_equal (Float32.sub (sk_float8 (sk_y8 s)) (sk_float8 (sk_next_floor s)))
    (sk_float8 (sk_gap8 s)) &&
  Bool.eqb (ske_high (sk_float8 (sk_y8 s)) (sk_float8 (sk_next_floor s)))
    (4000 <? sk_gap8 s) &&
  Bool.eqb (ske_late (Int.repr (sk_next_timer s))) (30 <? sk_next_timer s) &&
  sk_quarters_exact 4 (sk_y8 s) (sk_next_floor s) v &&
  sk_bits_equal (Float32.sub (sk_float8 v) (rank9cf_integer 2))
    (sk_float8 raw_gravity) &&
  Bool.eqb (Float32.cmp Clt (sk_float8 raw_gravity) (rank9cf_integer (-75)))
    (raw_gravity <? -600) &&
  (if snd (sk_quarters 4 (sk_y8 s) (sk_next_floor s) v) &&
      negb (sk_bounced s) && (gravity <? 0) then
    sk_bits_equal (Float32.div (Float32.neg (sk_float8 gravity)) (rank9cf_integer 2))
      (sk_float8 (-gravity / 2))
   else true).

Theorem sk_normal_episode_checked :
  length sk_normal_samples = 51%nat /\
  forallb sk_sample_exact sk_normal_samples = true /\
  forallb (fun s => negb (sk_accept s)) sk_normal_samples = true /\
  forallb (fun s => negb (ske_high (sk_float8 (sk_y8 s))
    (sk_float8 (sk_next_floor s)))) sk_normal_samples = true /\
  ueq_scaled_list_max 0 (map sk_gap8 sk_normal_samples) = 1648 /\
  ueq_scaled_list_max 0 (map sk_gap8
    (filter (fun s => negb (sk_bounced s)) sk_normal_samples)) = 1136 /\
  map (fun s => (sk_timer s, sk_velocity8 (sk_next s)))
    (filter (fun s => snd (sk_quarters 4 (sk_y8 s) (sk_next_floor s) (sk_velocity8 s)))
      sk_normal_samples) = [(22,136);(27,-312)] /\
  forallb (fun s => sk_next_timer s <=? 30) sk_normal_samples = true /\
  sk_active (sk_next (last sk_normal_samples sk_normal_start)) = false.
Proof. vm_compute; repeat split; reflexivity. Qed.

Theorem sk_hard_rebound_is_different :
  length sk_hard_samples = 31%nat /\
  forallb sk_sample_exact sk_hard_samples = true /\
  sk_gap8 (last sk_hard_samples sk_hard_start) = 4520 /\
  sk_next_timer (last sk_hard_samples sk_hard_start) = 31 /\
  sk_accept (last sk_hard_samples sk_hard_start) = true /\
  ske_high (sk_float8 (sk_y8 (last sk_hard_samples sk_hard_start)))
    (sk_float8 (sk_next_floor (last sk_hard_samples sk_hard_start))) = true /\
  sk_bits_equal (Float32.div (Float32.neg (rank9cf_integer (-75)))
    (rank9cf_integer 2)) (sk_float8 300) = true.
Proof. vm_compute; repeat split; reflexivity. Qed.

Theorem sk_normal_sample_executes_no_timeout :
  forall version e le memory mb s timer,
  In s sk_normal_samples ->
  le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
  le ! SK._t'3 = Some (Vint timer) ->
  Mem.load Mfloat32 memory mb 64 = Some (Vsingle (sk_float8 (sk_y8 s))) ->
  Mem.load Mfloat32 memory mb 112 = Some (Vsingle (sk_float8 (sk_next_floor s))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le memory
    (ske_after_timer version) E0
    (ske_test_temps le timer (sk_float8 (sk_y8 s)) (sk_float8 (sk_next_floor s)))
    memory Out_normal.
Proof.
  intros version e le memory mb s timer Hin Hm Htimer Hy Hfloor.
  eapply ske_not_high_cannot_take_timeout; eauto.
  destruct sk_normal_episode_checked as (_ & _ & _ & H & _).
  rewrite forallb_forall in H. specialize (H s Hin). now apply negb_true_iff in H.
Qed.


Theorem sk_normal_sample_full_gate :
  forall version e le memory mb s before written,
  In s sk_normal_samples ->
  le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint16unsigned memory mb 26 = Some (Vint before) ->
  Mem.store Mint16unsigned memory mb 26 (Vint (ske_next_timer before)) = Some written ->
  Mem.load Mfloat32 memory mb 64 = Some (Vsingle (sk_float8 (sk_y8 s))) ->
  Mem.load Mfloat32 memory mb 112 = Some (Vsingle (sk_float8 (sk_next_floor s))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le memory
    (ske_gate version) E0
    (ske_test_temps (ske_increment_temps le before) (ske_next_timer before)
      (sk_float8 (sk_y8 s)) (sk_float8 (sk_next_floor s)))
    written Out_normal /\
  Mem.load Mint32 written mb 12 = Mem.load Mint32 memory mb 12.
Proof.
  intros version e le memory mb s before written Hin Hm Htimer Hstore Hy Hfloor.
  eapply ske_full_gate_no_timeout; eauto.
  destruct sk_normal_episode_checked as (_ & _ & _ & H & _).
  rewrite forallb_forall in H. specialize (H s Hin). now apply negb_true_iff in H.
Qed.

Record SlideKickEntryBoundary : Prop := {
  sk_boundary_resolution : forall version, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SK._act_slide_kick = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ske_body version));
  sk_boundary_normal_execution : forall version e le memory mb s before written,
    In s sk_normal_samples ->
    le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
    Mem.load Mint16unsigned memory mb 26 = Some (Vint before) ->
    Mem.store Mint16unsigned memory mb 26 (Vint (ske_next_timer before)) = Some written ->
    Mem.load Mfloat32 memory mb 64 = Some (Vsingle (sk_float8 (sk_y8 s))) ->
    Mem.load Mfloat32 memory mb 112 = Some (Vsingle (sk_float8 (sk_next_floor s))) ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le memory
      (ske_gate version) E0
      (ske_test_temps (ske_increment_temps le before) (ske_next_timer before)
        (sk_float8 (sk_y8 s)) (sk_float8 (sk_next_floor s)))
      written Out_normal /\
    Mem.load Mint32 written mb 12 = Mem.load Mint32 memory mb 12;
  sk_boundary_normal_certificate :
    length sk_normal_samples = 51%nat /\
    forallb sk_sample_exact sk_normal_samples = true /\
    ueq_scaled_list_max 0 (map sk_gap8 sk_normal_samples) = 1648;
  sk_boundary_hard_certificate :
    length sk_hard_samples = 31%nat /\
    forallb sk_sample_exact sk_hard_samples = true /\
    sk_gap8 (last sk_hard_samples sk_hard_start) = 4520 /\
    sk_accept (last sk_hard_samples sk_hard_start) = true;
  sk_boundary_source : forall version,
    sk_velocity_writes (sk_initializer_case version) = [sk_fconst 1094713344] /\
    sk_velocity_writes (fn_body (ske_body version)) =
      [Ebinop Odiv (Eunop Oneg (Etempvar SK._t'10 tfloat) tfloat)
        (sk_fconst 1073741824) tfloat; sk_fconst 0];
  sk_boundary_taken_execution : forall version e le m mb timer y floor trace after result,
    le ! SK._m = Some (Vptr mb Ptrofs.zero) ->
    le ! SK._t'3 = Some (Vint timer) ->
    e ! SK._set_mario_action = None ->
    Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
    Mem.load Mfloat32 m mb 112 = Some (Vsingle floor) ->
    ske_late timer = true -> ske_high y floor = true ->
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ilh_set_action_body version))
      [Vptr mb Ptrofs.zero; Vint (Int.repr 16779404); Vint (Int.repr 2)]
      trace after result ->
    exists last,
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (ske_after_timer version) trace last after
      (Out_return (Some (Vint Int.one, tuint)))
}.
Theorem sk_slide_kick_entry_boundary_checked : SlideKickEntryBoundary.
Proof.
  constructor.
  - exact ske_selected_body_resolves.
  - exact sk_normal_sample_full_gate.
  - destruct sk_normal_episode_checked as (Hn & He & _ & _ & Hp & _). auto.
  - destruct sk_hard_rebound_is_different as (Hn & He & Hg & _ & Ha & _). auto.
  - intro version. destruct (sk_vertical_source_receipts version) as (Hi & Hv & _). auto.
  - exact ske_high_timeout_calls_real_setter.
Qed.
