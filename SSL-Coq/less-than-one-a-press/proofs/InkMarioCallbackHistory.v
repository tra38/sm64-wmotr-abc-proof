(** Construct, rather than assume, the callback's call into the existing
    action prefix.  No completed Mario action or callback is a premise.
    The caller's freshly read object argument is retained exactly; the
    action prefix obtains its actual Mario object from MarioState instead. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Smallstep Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkScheduledActionSource
  InkActionPassStart InkActionPassHistory InkActionPassResolution InkBackwardSource
  OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition isc_body version := ish_body version ISMarioCallback.
Definition isc_object_type := tptr (Tstruct ISC._Object noattr).
Definition isc_action_type := Tfunction [isc_object_type] tint cc_default.
Definition isc_global := Evar ISC._gCurrentObject isc_object_type.
Definition isc_action_call := Scall (Some ISC._t'1)
  (Evar ISC._execute_mario_action isc_action_type)
  [Etempvar ISC._t'8 isc_object_type].
Definition isc_after_action := Sset ISC._particleFlags (Etempvar ISC._t'1 tint).
Definition isc_tail version := match fn_body (isc_body version) with
| Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition isc_initial_temps version := create_undef_temps (fn_temps (isc_body version)).
Definition isc_call_temps version object := PTree.set ISC._t'8 object
  (PTree.set ISC._particleFlags (Vint Int.zero) (isc_initial_temps version)).
Definition isc_action_cont version object k :=
  Kcall (Some ISC._t'1) (isc_body version) empty_env (isc_call_temps version object)
    (Kseq isc_after_action (Kseq (isc_tail version) k)).

Lemma isc_generated_prefix : forall version,
  fn_body (isc_body version) = Ssequence
    (Sset ISC._particleFlags (Econst_int Int.zero tint))
    (Ssequence (Ssequence (Ssequence (Sset ISC._t'8 isc_global) isc_action_call)
      isc_after_action) (isc_tail version)).
Proof. intros []; reflexivity. Qed.

Lemma ish_empty_call_entry : forall version kind m,
  function_entry2 (Clight.globalenv (selected_clight_target version))
    (ish_body version kind) [] m empty_env
    (create_undef_temps (fn_temps (ish_body version kind))) m.
Proof.
  intros version kind m. constructor.
  - destruct version, kind; constructor.
  - destruct version, kind; constructor.
  - destruct version, kind; vm_compute; intuition congruence.
  - destruct version, kind; apply alloc_variables_nil.
  - destruct version, kind; reflexivity.
Qed.

Lemma isc_current_object_read : forall (ge : genv) le m cell object,
  Genv.find_symbol ge ISC._gCurrentObject = Some cell ->
  Mem.load Mint32 m cell 0 = Some object ->
  eval_expr ge empty_env le m isc_global object.
Proof.
  intros ge le m cell object Hsymbol Hload.
  eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
  - apply eval_Evar_global; [reflexivity|exact Hsymbol].
  - eapply deref_loc_value with (chunk := Mint32); [reflexivity|exact Hload].
Qed.

Lemma isc_callback_reaches_action_call : forall version m cell object k,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISC._gCurrentObject = Some cell ->
  Mem.load Mint32 m cell 0 = Some object ->
  sem_cast object isc_object_type isc_object_type m = Some object ->
  star Clight.step2 (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (isc_body version)) [] k m) E0
    (Callstate (Internal (iap_body version)) [object]
      (isc_action_cont version object k) m).
Proof.
  intros version m cell object k Hsymbol Hload Hcast.
  destruct (ias_selected_action_resolves version) as (fb & Hfs & Hff).
  eapply star_left; [apply step_internal_function; apply ish_empty_call_entry| |reflexivity].
  rewrite isc_generated_prefix.
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left; [apply step_set; constructor| |reflexivity].
  eapply star_left; [apply step_skip_seq| |reflexivity].
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left; [apply step_seq| |reflexivity].
  eapply star_left; [apply step_set; eapply isc_current_object_read; eauto| |reflexivity].
  eapply star_left; [apply step_skip_seq| |reflexivity].
  apply star_one. unfold isc_action_call, isc_action_cont, isc_call_temps, isc_initial_temps.
  eapply step_call with (vf := Vptr fb Ptrofs.zero).
  - reflexivity.
  - eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
    + apply eval_Evar_global; [reflexivity|exact Hfs].
    + apply deref_loc_reference. reflexivity.
  - econstructor.
    + apply eval_Etempvar. apply PTree.gss.
    + exact Hcast.
    + constructor.
  - exact Hff.
  - destruct version; reflexivity.
Qed.

(** [argument] need not equal [object].  This does not make a wrong live
    object harmless after the action returns: the callback's later stores
    and copy are outside this constructed prefix.  The argument conversion
    is explicit: a failed read or undefined conversion is not discarded. *)
Theorem isc_callback_constructs_action_prefix :
  forall version m current_cell argument state_cell mario object action k,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    ISC._gCurrentObject = Some current_cell ->
  Mem.load Mint32 m current_cell 0 = Some argument ->
  sem_cast argument isc_object_type isc_object_type m = Some argument ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    IBM._gMarioState = Some state_cell ->
  Mem.load Mint32 m state_cell 0 = Some (Vptr mario Ptrofs.zero) ->
  Mem.load Mint32 m mario 12 = Some action ->
  bool_val action tuint m = Some true ->
  Mem.load Mint32 m mario 136 = Some object ->
  exists ready,
    star Clight.step2 (Clight.globalenv (selected_clight_target version))
      (Callstate (Internal (isc_body version)) [] k m) E0
      (State (iap_body version) (ias_flag_frontier version)
        (Kseq (ias_after_visibility version) (Kseq (ias_return version)
          (isc_action_cont version argument k))) empty_env ready m) /\
    ready ! (ias_o1 version) = Some object /\
    ready ! (ias_o2 version) = Some object.
Proof.
  intros version m current_cell argument state_cell mario object action k
    Hcs Hcurrent Hcast Hss Hstate Haction Hactive Hobject.
  destruct (ias_active_body_reaches_flag_read version (ias_initial_temps version argument)
    m state_cell mario object action (isc_action_cont version argument k)
    Hss Hstate Haction Hactive Hobject) as (ready & Hbody & Ho1 & Ho2).
  exists ready. split; [|auto].
  eapply star_trans.
  - eapply isc_callback_reaches_action_call; eauto.
  - eapply star_left; [apply step_internal_function; apply ias_call_entry|exact Hbody|reflexivity].
  - reflexivity.
Qed.
