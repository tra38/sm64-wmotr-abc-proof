(** Derive the ordinary State index from the copy's actual identity test. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkRawCopySource
  InkRawCopyExpressions InkBackwardExecution ObjectContactNecessity
  ContactConsumerExecution Area1Rank18CopyRead Area1Rank18StateArrayBound
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition irc_object_guard := Ebinop One
  (Etempvar IRC._t'37 (tptr (Tstruct IRC._Object noattr)))
  (Etempvar IRC._t'38 (tptr (Tstruct IRC._Object noattr))) tint.

Lemma irc_same_object_guard_false : forall ge e le m ob oo choice,
  le ! IRC._t'37 = Some (Vptr ob oo) ->
  le ! IRC._t'38 = Some (Vptr ob oo) ->
  ocn_test_value ge e le m irc_object_guard choice -> choice = false.
Proof.
  intros ge e le m ob oo choice Hleft Hright [answer [Hexpr Hbool]].
  unfold irc_object_guard in Hexpr. inversion Hexpr; subst.
  - repeat match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
      assert (v = Vptr ob oo) by (eapply ocn_temp_value; eauto); subst v; clear Hr end.
    lazymatch goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some answer |- _ =>
      change (option_map Val.of_bool
        (Val.cmpu_bool (Mem.valid_pointer m) Cne (Vptr ob oo) (Vptr ob oo)) = Some answer) in Hsem;
      cbn [Val.cmpu_bool] in Hsem;
      repeat match type of Hsem with context [if ?test then _ else _] =>
        destruct test eqn:?; cbn in Hsem; try discriminate end;
      try congruence;
      inversion Hsem; subst; rewrite Ptrofs.eq_true in Hbool;
      cbn in Hbool; inversion Hbool; reflexivity end.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Theorem irc_index_test_keeps_zero :
  forall version e le m cb gb ob oo t le' m' out,
  e ! IRC._gCurrentObject = None -> e ! IRC._gMarioObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IRC._gCurrentObject = Some cb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IRC._gMarioObject = Some gb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob oo) -> Mem.load Mint32 m gb 0 = Some (Vptr ob oo) ->
  le ! IRC._i = Some (Vint Int.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    rank18_index_test t le' m' out ->
  le' ! IRC._i = Some (Vint Int.zero) /\ m' = m /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m cb gb ob oo t le' m' out HlocalC HlocalG
    HsymbolC HsymbolG Hcurrent Hmario Hindex Hrun.
  unfold rank18_index_test in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sset IRC._t'37 (Evar IRC._gCurrentObject (tptr (Tstruct IRC._Object noattr))))
    _ _ _ _ _ eq_refl Hrun)
    as (first_le & first_m & first_trace & rest_trace & Htrace & Hfirst & Hrest).
  inversion Hfirst; subst.
  lazymatch goal with Hr : eval_expr _ _ _ _ (Evar IRC._gCurrentObject _) ?v |- _ =>
    pose proof (irc_global_pointer_read _ _ _ _ _ _ _ _
      HlocalC HsymbolC Hcurrent Hr) as Hvalue; subst v end.
  destruct (ibk_split_sequence _ _ _ _
    (Sset IRC._t'38 (Evar IRC._gMarioObject (tptr (Tstruct IRC._Object noattr))))
    _ _ _ _ _ eq_refl Hrest)
    as (guard_le & guard_m & second_trace & branch_trace & HrestTrace & Hsecond & Hbranch).
  inversion Hsecond; subst.
  lazymatch goal with Hr : eval_expr _ _ _ _ (Evar IRC._gMarioObject _) ?v |- _ =>
    pose proof (irc_global_pointer_read _ _ _ _ _ _ _ _
      HlocalG HsymbolG Hmario Hr) as Hvalue; subst v end.
  inversion Hbranch; subst.
  lazymatch goal with
  | Hr : eval_expr ?ge ?env ?temps ?memory (Ebinop One _ _ _) ?answer,
    Hb : bool_val ?answer _ ?memory = Some ?b |- _ =>
    assert (b = false) as Hfalse by
      (apply (irc_same_object_guard_false ge env temps memory ob oo b);
        [rewrite PTree.gso by discriminate; apply PTree.gss|apply PTree.gss|
         exists answer; split; assumption]); subst b end.
  match goal with Hskip : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
    inversion Hskip; subst end.
  repeat split; try reflexivity.
  repeat rewrite PTree.gso by discriminate. exact Hindex.
Qed.
