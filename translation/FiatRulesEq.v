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

  Notation wf_args l :=
    (wf_args (Model:= core_model l)).

Hint Constructors type_wf: core.
Hint Resolve conj: core.
Hint Resolve eq_sort_refl: core.

Lemma ty_sort_wf: wf_sort fiat_rules [] {{s #"ty"}}.
Proof. eapply wf_sort_by; t''; t'. Qed.
Lemma list_ty_sort_wf: wf_sort fiat_rules [] {{s #"list_ty"}}.
Proof. eapply wf_sort_by; t''; t'. Qed.
Hint Resolve ty_sort_wf list_ty_sort_wf: core.

Local Notation eq_subst l := (eq_subst (Model:= core_model l)).
Local Notation eq_args l := (eq_args (Model:= core_model l)).

Lemma fiat_wf_lang: wf_lang fiat_rules.
Proof. unfold fiat_rules. prove_from_known_elabs. Qed.
Hint Resolve fiat_wf_lang: core.
Opaque fiat_rules.

Lemma fiat_rule_sort_eq name c s1 s2
  : ~In (name, sort_eq_rule c s1 s2) fiat_rules.
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
Qed.

Lemma ty_eq_sort:
  forall t c (Heq: eq_sort fiat_rules c t {{s #"ty"}}), 
  t = {{s #"ty"}}.
Proof.
  enough (forall t t' c (Heq: eq_sort fiat_rules c t t'), 
  t = {{s #"ty"}} <-> t' = {{s #"ty"}}) by (intros; eapply H; eauto).

  intros t t' c Heq.
  induction Heq; eauto; try easy.
  - eapply fiat_rule_sort_eq in H; inj_all.
  - destruct t1', t2'.
    induction l; induction l0; compute in *; apply conj; intros; inj_all.
  - intuition.
Qed.

Lemma list_ty_eq_sort:
  forall t c (Heq: eq_sort fiat_rules c t {{s #"list_ty"}}), 
  t = {{s #"list_ty"}}.
Proof.
  enough (forall t t' c (Heq: eq_sort fiat_rules c t t'), 
  t = {{s #"list_ty"}} <-> t' = {{s #"list_ty"}}) by (intros; eapply H; eauto).

  intros t t' c Heq.
  induction Heq; eauto; try easy.
  - eapply fiat_rule_sort_eq in H; inj_all.
  - destruct t1', t2'.
    induction l; induction l0; compute in *; apply conj; intros; inj_all.
  - intuition.
Qed.

(*
Lemma fiat_rule_ty_term_eq name c e1 e2
  : ~In (name, term_eq_rule c e1 e2 {{s #"ty"}}) fiat_rules.
Proof.
  unfold not; intros.
  repeat (destruct H; equality).
Qed.

Lemma fiat_rule_list_ty_term_eq name c e1 e2
  : ~In (name, term_eq_rule c e1 e2 {{s #"list_ty"}}) fiat_rules.
Proof.
  unfold not; intros.
  repeat (destruct H; equality).
Qed.
 *)

Lemma ty_eq_term t e1 e2:
    eq_term fiat_rules [] t e1 e2 ->
    (t = scon "ty" [] \/ t = scon "list_ty" []) ->
    e1 = e2.
Proof.
  intros H.
  pattern e2; pattern e1; pattern t; revert t e1 e2 H.
  apply CutFreeInd.term_cut_ind; try typeclasses eauto; auto.
  1: apply wf_ctx_nil.
  all: intros; subst; try now intuition congruence.
  - destruct H2;
    repeat (destruct H; equality).
  - destruct H2.
    all: destruct t; cbn in H2; inversions.
    all: destruct l; cbn in H3; inversions; try tauto.
    all: repeat (destruct H; equality); inj_all.
    all: repeat lazymatch goal with
           | H : eq_args _ _ _ _ _ |- _ => safe_invert H
          | H : (?a = ?b \/ ?a = ?c -> _) |- _ => assert (a=b \/ a=c) by eauto; inj_all
                         end; auto; repeat f_equal.
  - destruct H2; inj_all.
    + eapply ty_eq_sort in H; inj_all.
    + eapply list_ty_eq_sort in H; inj_all.
Qed.

Lemma fiat_rule_ext s s0 s1 s2 args t:
  In ("ext", term_rule [(s, s0); (s1, s2)] args t) fiat_rules ->
  s0 = {{s #"ty"}} /\ s2 = {{s #"env"}}.
Proof.
  intros. repeat (destruct H; equality).
Qed.

Lemma env_eq_sort:
  forall t c (Heq: eq_sort fiat_rules c t {{s #"env"}}),
  t = {{s #"env"}}.
Proof.
  enough (forall t t' c (Heq: eq_sort fiat_rules c t t'), 
  t = scon "env" [] <-> t' = scon "env" []) by (intros; eapply H; eauto).
  intros t t' c Heq.
  induction Heq; eauto; try easy.
  - eapply fiat_rule_sort_eq in H; inj_all.
  - destruct t1', t2'.
    induction l; induction l0; compute in *; apply conj; intros; inj_all.
  - intuition.
Qed.

Lemma env_eq_term t e1 e2: 
    eq_term fiat_rules [] t e1 e2 ->
    t = scon "env" [] ->
    e1 = e2.
Proof.
  intros H.
  pattern e2; pattern e1; pattern t; revert t e1 e2 H.
  apply CutFreeInd.term_cut_ind; try typeclasses eauto; auto.
  1: apply wf_ctx_nil.
  all: intros; subst; try now intuition congruence.
  - repeat (destruct H; equality).
  - destruct t; destruct l; inj_all; inversions.
    repeat (destruct H; equality); inj_all.
    repeat lazymatch goal with
           | H : eq_args _ _ _ _ _ |- _ => safe_invert H
                         end; auto; repeat f_equal.
                         eapply ty_eq_term in H11; eauto; inj_all.
  - destruct t; destruct l; inj_all; inversions.
    all: eapply env_eq_sort in H; inversions; inj_all.
Qed.

Lemma eq_sort_trivial_cut_helper: 
    (forall t t0, eq_sort fiat_rules [] t t0 -> t = t0) /\ 
    (forall s t t0, eq_term fiat_rules [] s t t0 -> True) /\ 
    (forall c0 s s0, eq_subst fiat_rules [] c0 s s0 -> True) /\ 
    (forall c0 s s0, eq_args fiat_rules [] c0 s s0 -> True).
Proof. 
  apply CutFreeInd.cut_ind; try typeclasses eauto; eauto; intros; inj_all.
  - constructor.
  - eapply fiat_rule_sort_eq in H; tauto.
  - repeat (destruct H; equality).
    all: try solve [inversion H0; inj_all].
    all: repeat lazymatch goal with
           | H : eq_args _ _ _ _ _ |- _ => safe_invert H
                         end; auto; cbn in *.
         all: repeat f_equal. 
         all: try solve [eapply ty_eq_term; eauto].
         all: try solve [eapply env_eq_term; eauto].
Qed.

Lemma eq_sort_trivial s1 s2: 
    eq_sort fiat_rules [] s1 s2 -> s1 = s2.
Proof.
  intros; eapply eq_sort_trivial_cut_helper; eauto.
Qed.

End WithMap.
