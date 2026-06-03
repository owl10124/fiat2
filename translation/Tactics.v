Set Implicit Arguments.
From fiat2 Require Import Language TypeSystem TypeSound Value.

Require Import coqutil.Map.Interface coqutil.Datatypes.dlist.
From Utils Require Import Utils.

From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Tools.EGraph.Automation Tools.EGraph.Defs Tools.UnElab.
From Pyrosome Require Import Lang.FiatTest.
Import Core.Notations.
Import coqutil.Datatypes.Result Result.List Result.ResultMonadNotations.

Require Import coqutil.Word.Interface coqutil.Word.Properties.
Export Stdlib.Sorting.Permutation.

Require Stdlib.derive.Derive.
Require Import Datatypes.String Lists.List.
Open Scope string.
Import ListNotations.
Open Scope list.

Require Import Stdlib.FSets.FMapInterface.
Require Import Stdlib.ZArith.ZArith.

Ltac t'' := repeat (
  match goal with
  | [|-Model.wf_term _ _ _] => t'
  | [|-wf_term _ _ _ _] => eapply wf_term_by'
  | [|-wf_args _ _ _] => econstructor
  | [|-_] => unshelve (repeat t); simpl
  end); eauto 2.

Ltac inj_all_once:= (
  simpl in *; subst; try discriminate; try contradiction; auto;
  try lazymatch goal with
      | [H: exists a, ?b |- _] => destruct H
      | [H: ?a /\ ?b |- _] => destruct H
      | [H: ?a = ?a |-_] => clear H
      | [H: ?a = ?b, H': ?a = ?b |-_] => clear H'
      | [H: forall a, Success a = Success ?b -> ?P |-_] => 
          try (assert (Heq: Success b = Success b) by auto; 
          specialize (H b Heq); clear Heq)
      | [H: forall a a', Success (a, a') = Success (?c, ?c') -> ?P |-_] => 
          try (assert (Heq: Success (c,c') = Success (c,c')) by auto; 
          specialize (H c c' Heq); clear Heq)
      | [H: forall a, Success a = ?b -> ?P, H': Success ?c = ?b |-_] => 
          specialize (H c H')
      | [a: ?b * ?c |-_] => destruct a 
      | [H: (?a,?b)=(?c,?d) |-_] => inversion H; clear H
      | [H: NoDup ?x, H': NoDup ?x|-_] => clear H'
      | [H: StronglySorted ?x ?y, H': StronglySorted ?x ?y|-_] => clear H'
      | [H: type_wf ?x, H': type_wf ?x|-_] => clear H'
      | [H: type_of ?x ?y ?z ?w, H': type_of ?x ?y ?z ?w|-_] => clear H'
      | [H: ?a =? ?b = true |-_] => rewrite String.eqb_eq in H
      | [H: ?a =? ?b = false |-_] => rewrite String.eqb_neq in H
      | [H: ?a->?b, H': ?a |-_] => specialize (H H')
      | [H: (?a = ?a)->?b |-_] => assert (H':a=a) by eauto; specialize (H H'); clear H'
      | [H: (Success ?a) = (Success ?b) |- _] => injection H as H; subst
      | [H: (Failure ?a) = (Failure ?b) |- _] => injection H as H; subst
      | [H: (Some ?a) = (Some ?b) |- _] => injection H as H; subst
      | [H: ?b = Success ?a |- _] => symmetry in H
      | [H: ?b = Failure ?a |- _] => symmetry in H
      | [H: ?P ?b |- ?P ?a] => try solve [assert (Heq: a=b) by eauto; rewrite Heq; eauto]
      end).

Ltac inj_all := repeat (repeat inj_all_once; try case_match); auto.

Ltac equality_once := try (lazymatch goal with
                           | [H: Success ?a = ?b, H': Success ?c = ?b |-_] => assert (Heq: Success a = Success c) by (rewrite H; rewrite H'; auto); injection Heq as Heq; subst
                           | [H: Success ?a = ?b, H': Failure ?c = ?b |-_] => assert (Success a = Failure c) by (rewrite H; rewrite H'; auto); discriminate
                           | [H: ?a = ?b, H': ?a = ?c |-_] => match a with None => idtac | _ => rewrite H in H'; subst end
                           (*
                              | [H: ?a = ?b, H': ?b = ?c |-_] => rewrite H' in H; subst*)
                           | [H: ?a = ?c, H': ?b = ?c |- ?a = ?b] => solve [rewrite H; rewrite H'; auto]
                           end; inj_all_once); try match goal with 
                                                   | [H: ?P ?a |- ?P ?b ] => try solve [assert (H':b=a) by eauto; rewrite H'; auto] 
                                                   | [|- (?a,?b)=(?c,?d)] => try (assert (a=c) by eauto; f_equal; auto); 
                                                       try (assert (b=d) by eauto; f_equal; auto)
                                                   | [|- ?a::?b = ?c::?d] => try (assert (a=c) by eauto; f_equal; auto); 
                                                       try (assert (b=d) by eauto; f_equal; auto)
                                                   | [|- _] => try solve [repeat (f_equal); auto]
                                                   end.

Ltac equality := repeat (inj_all_once; equality_once); auto.
Ltac do_both := repeat (equality; inj_all); eauto.

Ltac invert_cons := repeat (
  try match goal with
      | [H: NoDup (?b::?c) |-_] => inversion H; clear H
      | [H: StronglySorted ?a (?b::?c) |-_] => inversion H; clear H
      | [H: Permutation [] (?a::?b) |-_] => eapply Permutation_nil in H
      | [H: Permutation (?a::?b) [] |-_] => eapply Permutation_sym in H; eapply Permutation_nil in H
      | [H: Permutation ?a ?a |-_] => clear H
      | [H: Forall2 ?p [] (?a::?b) |-_] => inversion H
      | [H: Forall2 ?p (?a::?b) [] |-_] => inversion H
      | [H: Forall ?p (?a::?b) |-_] => inversion H; clear H
      | [H: Forall2 ?p (?a::?b) (?c::?d) |- _] => inversion H; clear H
      | [H: (?a::?b)=(?c::?d) |-_] => inversion H; clear H
      end; inj_all).

Global Hint Constructors Permutation: permute.
Global Hint Resolve Permuted_record_sort
  Permutation_map
  Permutation_in
  Permutation_NoDup
  Permutation_refl
  Permutation_sym
  Permutation.Permutation_cons_inv 
  Permutation_trans: permute.
Global Hint Resolve in_eq in_map: core.

Ltac invert_type_of := repeat (
  match goal with
  | [H: type_of_atom _ _ |-_] => inversion H; clear H
  | [H: type_of_unop _ _ _ |-_] => inversion H; clear H
  | [H: type_of_binop _ _ _ _ |-_] => inversion H; clear H
  | [H: type_of_ternop _ _ _ _ _ |-_] => inversion H; clear H
  end; subst; try discriminate).

Search "get".
Ltac map_simpl := repeat (
  try (erewrite map.get_put_same in * by eauto; inj_all);
  try (erewrite map.get_put_diff in * by eauto; inj_all);
  try (erewrite map.get_empty in * by eauto; inj_all)
).
(*
   match goal with
   | [H: map.get (map.put ?m ?k ?v) ?k = _ |-_] => erewrite map.get_put_same in H
   | [H: _ = map.get (map.put ?m ?k ?v) ?k |-_] => erewrite map.get_put_same in H
   | [|- _ = map.get (map.put ?m ?k ?v) ?k] => erewrite map.get_put_same
   | [|- map.get (map.put ?m ?k ?v) ?k = _] => erewrite map.get_put_same

   | [|- _ = map.get (map.put ?m ?k ?v) ?k'] => (assert (Hdiff: k'<>k) by auto; erewrite map.get_put_diff; auto; clear Hdiff)
   | [|- map.get (map.put ?m ?k ?v) ?k' = _] => (assert (Hdiff: k'<>k) by auto; erewrite map.get_put_diff; auto; clear Hdiff)
   | [H: map.get (map.put ?m ?k ?v) ?k' = _ |-_] => (assert (Hdiff: k'<>k) by auto; erewrite map.get_put_diff in H; auto; clear Hdiff)
   | [H: _ = map.get (map.put ?m ?k ?v) ?k' |-_] => (assert (Hdiff: k'<>k) by auto; erewrite map.get_put_diff in H; auto; clear Hdiff)
   | [H: map.get map.empty ?k = _ |-_] => erewrite map.get_empty in H
   | [H: _ = map.get map.empty ?k |-_] => erewrite map.get_empty in H
   | [|- map.get map.empty ?k = _] => erewrite map.get_empty
   | [|- _ = map.get map.empty ?k] => erewrite map.get_empty
 *)

Ltac gather n :=
  repeat match goal with
         | [H: n = ?m|-_] => rewrite <- H in *
         | [H: ?m = n|-_] => rewrite H in *
         end.
