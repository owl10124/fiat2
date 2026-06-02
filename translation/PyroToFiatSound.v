Set Implicit Arguments.
From fiat2 Require Import Language TypeSystem TypeSound Value.

Require Import coqutil.Map.Interface coqutil.Datatypes.dlist.
From Utils Require Import Utils.

From Pyrosome Require Import Theory.WfCutElim Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Lang.SimpleVSTLC.
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
From Stdlib Require Import Psatz.

Require coqutil.Map.SortedListString.
Require Import Translator MapUtils Tactics.
Import SimpleVSubst.

Section WithMap.
  Context {locals: forall T, map.map string T} 
{locals_ok: forall T, map.ok (locals T)}.

  Print wf_args.
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).

Definition pyro_wf_fiat_ty (e:term) (t:sort) :=
  (t = (scon "ty" []) ->
  forall ft, Success ft = ty_pyro_to_fiat e ->
  type_wf ft) /\
  (t = (scon "list_ty" []) -> 
  forall tl, Success tl = list_ty_pyro_to_fiat e ->
  Forall type_wf (map snd tl)).

Hint Constructors type_wf: core.
Hint Resolve conj: core.
Hint Resolve eq_sort_refl: core.

Search wf_sort.
Lemma ty_sort_wf: wf_sort fiat_rules [] (scon "ty" []).
Proof. eapply wf_sort_by; t''; t'. Qed.
Lemma list_ty_sort_wf: wf_sort fiat_rules [] (scon "list_ty" []).
Proof. eapply wf_sort_by; t''; t'. Qed.
Hint Resolve ty_sort_wf list_ty_sort_wf: core.

Check wf_term_cut_ind.
Opaque fiat_rules.

Lemma ty_sort_eq:
  forall t c (Heq: eq_sort fiat_rules c t {{s #"ty"}}), 
  t = {{s #"ty"}}.
Proof.
  enough (forall t t' c (Heq: eq_sort fiat_rules c t t'), 
  t = {{s #"ty"}} <-> t' = {{s #"ty"}}) by (intros; eapply H; eauto).

  intros t t' c Heq.
  induction Heq; eauto; try easy.
  - repeat (destruct H; equality).
  - destruct t1', t2'.
    induction l; induction l0; compute in *; apply conj; intros; inj_all.
  - intuition.
Qed.

Definition pyro_ty_destruct (e:term) (t:sort) :=
  (t = {{s #"ty"}} ->
  e = {{e #"nat"}} \/
  e = {{e #"bool"}} \/
  e = {{e #"comparison"}} \/
  (exists l, e = {{e #"list" {l} }} /\ wf_term fiat_rules [] l {{s #"ty"}}) \/
  (exists l, e = {{e #"Trecord" {l} }} /\ wf_term fiat_rules [] l {{s #"list_ty"}})).

Lemma ty_sort_destruct:
  forall e t,
  wf_term fiat_rules [] e t ->
  pyro_ty_destruct e t.
Proof.
  apply wf_term_cut_ind; intros;
  unfold pyro_ty_destruct in *; inj_all.
  + intros. repeat (destruct H; equality).
    all: repeat (destruct s; inj_all).
    - inversion H0; inj_all.
      repeat right; eexists; eauto.
    - inversion H0; inj_all.
      do 3 right; left. eexists; eauto.
  + intros. inj_all. eapply ty_sort_eq in H1; inj_all.
Qed.

Lemma list_ty_sort_eq:
  forall t c (Heq: eq_sort fiat_rules c t {{s #"list_ty"}}),
  t = {{s #"list_ty"}}.
Proof.
  enough (forall t t' c (Heq: eq_sort fiat_rules c t t'), 
  t = scon "list_ty" [] <-> t' = scon "list_ty" []) by (intros; eapply H; eauto).
  intros t t' c Heq.
  induction Heq; eauto; try easy.
  - repeat (destruct H; equality).
  - destruct t1', t2'.
    induction l; induction l0; compute in *; apply conj; intros; inj_all.
  - intuition.
Qed.

Hint Resolve ty_sort_eq list_ty_sort_eq: core.

Theorem ty_pyro_to_fiat_wf:
  forall (Gp:term) (t:sort)
  (Hpwf: wf_term fiat_rules [] Gp t),
  (pyro_wf_fiat_ty Gp t).
Proof.
  unfold pyro_wf_fiat_ty.
  apply wf_term_cut_ind; intros; cycle 1.
  - inj_all.
  - apply conj; intros; inj_all; eauto.
  - apply conj; intros.
    * repeat (destruct H; equality).
      all: inj_all.
        enough (type_wf (TRecord a) /\ Forall (fun p => forall q, of_nat q = fst p -> length a > q) a) by intuition.
        clear H H0 H1.
        generalize dependent t.
        induction a; intros; destruct t; try solve [repeat constructor; eauto]; invert_cons.
        specialize IHa with t0; inj_all.
        inversion H; inj_all.
        pose proof Forall_map_fst as Hfst.
        specialize Hfst with (P:=(fun x => forall q, of_nat q = x -> length a1 > q)); simpl in Hfst.
        apply Hfst in H0.

        apply conj; constructor; invert_cons; try constructor; eauto.
        + unfold "~"; intros.
          From Stdlib Require Import Psatz.
          eapply Forall_In in H2; try eapply H0; inj_all.
          specialize H2 with (length a1); inj_all; lia.
        + admit.
        + apply of_nat_inj in H2; inj_all.
          admit.
        + apply Hfst in H0.
          eapply Forall_impl; try eapply H0; eauto.
    * inj_all;
      repeat (destruct H; equality); inj_all.
Admitted.

Hint Resolve ty_pyro_to_fiat_wf: core.

Lemma env_sort_eq:
  forall t c (Heq: eq_sort fiat_rules c t (scon "env" [])), 
  t = scon "env" [].
Proof.
  enough (forall t t' c (Heq: eq_sort fiat_rules c t t'), 
  t = scon "env" [] <-> t' = scon "env" []) by (intros; eapply H; eauto).
  intros t t' c Heq.
  induction Heq; eauto; try easy.
  - repeat (destruct H; equality).
  - destruct t1', t2'.
    induction l; induction l0; compute in *; apply conj; intros; inj_all.
  - intuition.
Qed.
Hint Resolve env_sort_eq: core.

Definition env_pyro_to_fiat_wf_term  (Gp:term) (t:sort)  :=
  forall (Genv: list(string*type))
  (Hs: t = scon "env" [])
  (Henv: Success Genv = env_pyro_to_fiat Gp),
  exists fenv, (fenv_wf Genv fenv /\
  forall t n, map.get fenv (of_nat n) = Some t ->
  n < length Genv).

Theorem env_pyro_to_fiat_wf:
  forall (Gp:term) (t:sort)
  (Hpwf: wf_term fiat_rules [] Gp t),
  env_pyro_to_fiat_wf_term Gp t.
Proof.
  apply wf_term_cut_ind;
  unfold env_pyro_to_fiat_wf_term;
  intros; intuition; inj_all; eauto.
  - eexists; apply conj; try eapply fenv_wf_nil; intros; map_simpl.
  - repeat (destruct H; equality).
    clear H2; specialize H3 with a0; inj_all.
    eexists; apply conj; try eapply fenv_wf_cons; intros; eauto; map_simpl.
      * specialize H2 with (n:=length a0). 
        destruct (map.get x (of_nat (length a0))); inj_all.
        specialize H2 with t; inj_all. lia.
      * eapply ty_pyro_to_fiat_wf in case_match_eqn; eauto.
        inversion H0; eauto.
      * assert (Hneq: n=length a0 \/ n<>length a0) by lia.
        destruct Hneq; inj_all. 
        assert (of_nat (length a0) <> of_nat n). {
        unfold "<>"; intros. 
        apply of_nat_inj in H5. lia.
        }
        map_simpl. apply H2 in H3; lia.
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

Definition pyro_expr_wf (e:term) (t:sort) :=
  forall A Gp, 
  t = scon "val" [A;Gp] ->
  forall fe, Success fe = expr_pyro_to_fiat e ->
  forall ft Genv fenv,
  Success ft = ty_pyro_to_fiat A ->
  Success Genv = env_pyro_to_fiat Gp ->
  fenv_wf Genv fenv ->
  type_of map.empty fenv fe ft.

Lemma val_sort_eq:
  forall t A Gp (Heq: eq_sort fiat_rules [] t (scon "val" [A;Gp]))
  (Ha: wf_term fiat_rules [] A (scon "ty" []))
  (HG: wf_term fiat_rules [] Gp (scon "env" [])),
  exists A' Gp',
  t = scon "val" [A';Gp'] /\
  eq_term fiat_rules [] (scon "ty" []) A A' /\ 
  eq_term fiat_rules [] (scon "env" []) Gp Gp'.
Proof.
  intros. 
  induction Heq; intros; inj_all; eauto.
  - repeat (destruct H; equality).
  - induction s1; destruct s2; inversion H; invert_cons.
    + rewrite sort_subst_nil. 
      repeat eexists. ; try rewrite term_subst_nil; auto.
    + clear IHHeq.
      Search term_subst.
      inversion Ha; inj_all.
Unset Printing Notations.
    Search apply_subst.
    


(*
Lemma val_sort_eq:
  forall t c A Gp (Heq: eq_sort fiat_rules c t (scon "val" [A;Gp]))
  (Ha: wf_term fiat_rules c A (scon "ty" []))
  (HG: wf_term fiat_rules c Gp (scon "env" [])),
  t = scon "val" [A;Gp].
Proof.
  intros.
  inj_all.
  pose proof ty_sort_eq.


  enough (forall t t' c (Heq: eq_sort fiat_rules c t t') A Gp,
  (*(Ha: wf_term fiat_rules c A (scon "ty" []))
     (HG: wf_term fiat_rules c Gp (scon "env" [])),*)
  t = scon "val" [A;Gp] <-> t' = scon "val" [A;Gp]) by (intros; eapply H; eauto).
  intros t t' c Heq.
  induction Heq; intros; eauto.
  - intros; subst.
    repeat (destruct H; equality).
  - intros; subst.
    destruct t1', t2'. 
    apply conj; intros; inversion H1; inj_all.
    + do 3 (destruct l; inj_all).
      inversion H4; inj_all.
      specialize IHHeq with t t0; destruct IHHeq; inj_all.
      inversion H1; inj_all.
      enough (term_subst s2 t0 = term_subst s1 t0 /\ term_subst s2 t = term_subst s1 t). {
        inj_all; f_equal; f_equal; eauto; f_equal; eauto.
      }
      f_equal; cbn.
      
      Search eq_subst.
      repeat f_equal.

Qed.
 *)

Theorem expr_pyro_to_fiat_wf: 
  forall (pt:term) (t:sort)
  (Hpwf: wf_term fiat_rules [] pt t),
  (pyro_expr_wf pt t).
Proof.
  apply wf_term_cut_ind;
  unfold pyro_expr_wf;
  intros; intuition.
  - repeat (destruct H; equality).
    all: inj_all.
    all: cbn in *.
    all: inversion H2; inj_all.
    all: try solve [repeat econstructor; eauto].
    + specialize H1 with (con "list" [t1]) Gp a0 (TList a1) Genv fenv; inj_all.
      repeat econstructor; eauto.
    + inversion H0; clear H0; inj_all.
      repeat econstructor; eapply ty_pyro_to_fiat_wf; eauto.
  - inj_all.
    inversion H1; inj_all.
    + repeat (destruct H2; equality).
    + 
    
Qed.


End WithMap.
