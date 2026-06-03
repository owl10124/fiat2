Set Implicit Arguments.
From fiat2 Require Import Language TypeSystem TypeSound Value.

Require Import coqutil.Map.Interface coqutil.Datatypes.dlist.
From Utils Require Import Utils.

From Pyrosome Require Import Theory.WfCutElim Theory.Core.
From Pyrosome Require Import Lang.FiatTest.
Import Core.Notations.
Import coqutil.Datatypes.Result Result.List Result.ResultMonadNotations.

Require Import coqutil.Word.Interface coqutil.Word.Properties.

Require Import Datatypes.String Lists.List.
Open Scope string.
Import ListNotations.
Open Scope list.

Require Import Stdlib.FSets.FMapInterface.

Require Import Translator MapUtils Tactics FiatRulesEq.
Import SimpleVSubst.

Require Import Psatz.

Section WithMap.
  Context {locals: forall T, map.map string T} 
  {locals_ok: forall T, map.ok (locals T)}.

  Opaque fiat_rules.

  Notation wf_args l :=
    (wf_args (Model:= core_model l)).

  Hint Constructors type_wf: core.
  Hint Resolve conj: core.

  Hint Resolve ty_sort_wf list_ty_sort_wf: core.

  Hint Resolve eq_sort_trivial: core.

  Theorem ty_pyro_to_fiat_wf:
    forall (Gp:term) (t:sort)
    (Hpwf: wf_term fiat_rules [] Gp t),
    (fun e t =>
    (t = {{s #"ty"}} ->
    forall ft, Success ft = ty_pyro_to_fiat e -> type_wf ft) /\
    (t = {{s #"list_ty"}} -> 
    forall tl, Success tl = list_ty_pyro_to_fiat e ->
    Forall type_wf tl)
    ) Gp t.
  Proof.
    apply wf_term_cut_ind; intros; intuition; try solve [inj_all].
    * repeat (destruct H; equality).
      all: inj_all.
      inversion H0; inj_all. 
      clear H1. 
      pose proof name_list_ty_ok a. constructor; inj_all.
    * repeat (destruct H; equality).
      all: inj_all. 
  Qed.

  Hint Resolve ty_pyro_to_fiat_wf: core.

  Theorem env_pyro_to_fiat_wf:
    forall (Gp:term) (t:sort)
    (Hpwf: wf_term fiat_rules [] Gp t),
    (fun e t =>
    forall (Genv: lenv)
    (Henv: Success Genv = env_pyro_to_fiat e),
    t = {{s #"env"}} ->
    exists fenv, (fenv_wf Genv fenv /\
    forall t n, map.get fenv (of_nat n) = Some t ->
    n < length Genv)
    ) Gp t.

  Proof.
    apply wf_term_cut_ind;
    intros; intuition; inj_all.
    - eexists; apply conj; try eapply fenv_wf_nil; intros; map_simpl.
    - apply fiat_rule_ext in H; inj_all.
      clear H3. 
      eexists; apply conj; try eapply fenv_wf_cons; intros; eauto; map_simpl.
      * specialize H4 with (n:=length a0). 
        destruct (map.get x (of_nat (length a0))); inj_all.
        specialize H4 with t2; inj_all. lia.
      * eapply ty_pyro_to_fiat_wf in case_match_eqn; eauto.
        inversion H0; eauto.
      * assert (Hneq: n=length a0 \/ n<>length a0) by lia.
        destruct Hneq; inj_all. 
        assert (of_nat (length a0) <> of_nat n). {
          unfold "<>"; intros. 
          apply of_nat_inj in H6. lia.
        }
        map_simpl. apply H4 in H3; lia.
  Qed.

  Hint Resolve env_pyro_to_fiat_wf: core.

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

  Theorem expr_pyro_to_fiat_wf: 
    forall (pt:term) (t:sort)
    (Hpwf: wf_term fiat_rules [] pt t),
    (fun e t =>
    forall A Gp, 
    t = scon "val" [A;Gp] ->
    forall fe, Success fe = expr_pyro_to_fiat e ->
    forall ft Genv fenv,
    Success ft = ty_pyro_to_fiat A ->
    Success Genv = env_pyro_to_fiat Gp ->
    fenv_wf Genv fenv ->
    type_of map.empty fenv fe ft
    ) pt t.
  Proof.
    apply wf_term_cut_ind;
    intros; intuition; cycle 1.
    - apply eq_sort_trivial in H1; inj_all.
      edestruct H0; eauto.
    - repeat (destruct H; equality).
      all: inversions.
      all: do_both; cbn in *.
      all: try solve [repeat econstructor; eauto].
      + specialize H2 with (con "list" [t1]) t2 a1 (TList a) Genv fenv; inj_all.
        repeat econstructor; eauto.
      + inversion H0; clear H0; inj_all.
        eapply ty_pyro_to_fiat_wf in H10; inj_all.
        repeat econstructor; eauto.
  Qed.

End WithMap.
