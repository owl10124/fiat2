Set Implicit Arguments.
From fiat2 Require Import Language TypeSystem TypeSound Value.

Require Import coqutil.Map.Interface coqutil.Datatypes.dlist.
From Utils Require Import Utils.

From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Tools.EGraph.Automation Tools.EGraph.Defs Tools.UnElab.
From Pyrosome Require Import Lang.FiatTest.
Import Core.Notations.
Import coqutil.Datatypes.Result Result.List Result.ResultMonadNotations.

Require Import coqutil.Word.Interface coqutil.Word.Properties.

Require Stdlib.derive.Derive.
Require Import Datatypes.String Lists.List.
Open Scope string.
Import ListNotations.
Open Scope list.

Require Import Stdlib.FSets.FMapInterface.
Require Import Stdlib.ZArith.ZArith.

Require coqutil.Map.SortedListString.
Local Existing Instance SortedListString.map.
Local Existing Instance SortedListString.ok.
Local Existing Instance SortedListString.Build_parameters.

Require Import Translator MapUtils Tactics.

Opaque map.put map.get map.empty.


Theorem ty_pyro_to_fiat_wf:
  forall (Gp:term) ft,
  Success ft = ty_pyro_to_fiat Gp ->
  type_wf ft.
Proof.
  induction ft using type_IH; intros; case_match' Gp; inj_all; 
  try solve [econstructor].
Qed.
Hint Resolve ty_pyro_to_fiat_wf: core.
(* just bools for now lol *)

Require Import Psatz.

Theorem env_pyro_to_fiat_unique:
  forall (Genv: list(string*type)) (Gp:term),
  Success Genv = env_pyro_to_fiat Gp ->
  exists fenv, 
  (fenv_wf Genv fenv /\
  forall t n, map.get fenv (of_nat n) = Some t ->
  n < length Genv).
Proof.
  induction Genv; intros; inj_all.
  - pose fenv_wf_nil; repeat (eexists); inj_all.
  - case_match' Gp; inj_all.
    specialize (IHGenv t1); inj_all.
    eapply fenv_wf_cons with (x:=of_nat (length a0)) in H as Hwf; eauto.
    * repeat eexists; try eapply Hwf.
      intros.
      assert (Hneq: n=length a0 \/ n<>length a0) by lia.
      destruct Hneq; inj_all; map_simpl.
      assert (of_nat (length a0) <> of_nat n). {
        unfold "<>"; intros.
        apply of_nat_inj in H3. lia.
        }
      map_simpl. eapply H0 in H1; lia.
    * invert_lhs; eauto.
      apply H0 in H1; lia.
Qed.

Theorem env_pyro_to_fiat_wf:
  forall (Genv: list(string*type)) (Gp:term),
  Success Genv = env_pyro_to_fiat Gp ->
  exists {fenv:map.rep}, fenv_wf Genv fenv.
Proof.
  intros; eauto.
  pose (env_pyro_to_fiat_unique) as Henv.
  specialize (Henv Genv Gp H).
  inj_all; eauto.
Qed.

Compute wf_judge_ind.


Print wf_term.

(*
   induction on judgement structure...
   wf_judge_ind should be good
   in CompilerFacts.v; see strengthening
   need a condition on sort, term and args

   wip folder boollang.v for eg on wfness induction

   desire some kind of alpha-equivalence on the fiat2 side
   define a relation of fiat2 programs "renamable"
   free vs bound variables
 *)

  Print wf_args.
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).

  Locate sort.
Definition pyro_is_wf_fiat (e:term) (t:SimpleVSubst.sort) :=
  forall fe, Success fe = expr_pyro_to_fiat e ->
  exists A Gp ft Genv fenv Gstore fstore,
  t = scon "val" [A;Gp] /\
  Success ft = ty_pyro_to_fiat A /\
  Success Genv = env_pyro_to_fiat Gp /\
  fenv_wf Gstore fstore /\
  fenv_wf Genv fenv /\
  type_of fstore fenv fe ft.


Theorem expr_pyro_to_fiat_wf: 
  (forall c t, wf_sort fiat_rules c t -> True)
  /\ (forall c e t, wf_term fiat_rules c e t -> pyro_is_wf_fiat e t)
      /\ (forall c s c', wf_args fiat_rules c s c' -> 
      Forall2 pyro_is_wf_fiat s (map snd c')).
Proof.
  unfold pyro_is_wf_fiat.
  apply wf_judge_ind; inj_all.
- intros; repeat (destruct c'; invert_cons); eauto.
  + basic_goal_prep;
      basic_core_crush.
      Search "lookup".
      Search In.


Functional Scheme expr_pyro_to_fiat_ind:= Induction for expr_pyro_to_fiat Sort Prop.
Theorem expr_pyro_to_fiat_wf: 
  forall (pt: term) A Gp
  (Hpwf: pyro_expr_wf pt A Gp),
  forall fe, Success fe = expr_pyro_to_fiat pt ->
  exists ft Genv fenv Gstore fstore,
  Success ft = ty_pyro_to_fiat A /\
  Success Genv = env_pyro_to_fiat Gp /\
  fenv_wf Gstore fstore /\
  fenv_wf Genv fenv /\
  type_of fstore fenv fe ft.
Proof.
  intros pt A Gp Hpwf. generalize A Gp.
  induction pt using wf_judge_ind.

  functional induction (expr_pyro_to_fiat pt); intros; inj_all; eauto.
  - edestruct IHr; eauto; clear IHr.
    edestruct IHr0; eauto; clear IHr0.
    inj_all.
    exists TBool
    repeat eexists; eauto.


