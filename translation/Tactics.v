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

Ltac inj_all := repeat (try case_match;
  match goal with
  | [H: (Success ?a) = (Success ?b) |- _] => injection H as H
  | [H: (Failure ?a) = (Failure ?b) |- _] => injection H as H
  | [H: (Some ?a) = (Some ?b) |- _] => injection H as H
  | [H: exists a, ?b |- _] => destruct H
  | [H: ?a /\ ?b |- _] => destruct H
  | [H: ?a =? ?b = true |-_] => try rewrite String.eqb_eq in H
  | [H: ?a =? ?b = false |-_] => try rewrite String.eqb_neq in H
  | [H: ?a = ?a |-_] => clear H
  | [H: forall a, Success a = Success ?b -> ?P |-_] => 
      assert (Heq: Success b = Success b) by auto; 
      specialize (H b Heq); clear Heq
  | [H: forall a a', Success (a, a') = Success (?c, ?c') -> ?P |-_] => 
      assert (Heq: Success (c,c') = Success (c,c')) by auto; 
      specialize (H c c' Heq); clear Heq
  | [H: forall a, Success a = ?b -> ?P, H': Success ?c = ?b |-_] => 
      specialize (H c H')
  | [|- _] => discriminate
  | [H: ?b = Success ?a |- _] => symmetry in H
  | [H: ?b = Failure ?a |- _] => symmetry in H
  | [H: Forall ?p (?a::?b) |- _] => inversion H; clear H
  | [H: Forall2 ?p (?a::?b) (?c::?d) |- _] => inversion H; clear H
  | [H: (?a::?b)=(?c::?d) |-_] => inversion H; clear H
  | [H: (?a,?b)=(?c,?d) |-_] => inversion H; clear H
  | [H: ?a, H': ~?a |-_] => contradiction
  | [H: ?a->?b |-_] => assert (Hnew: a) by auto; specialize (H Hnew); clear Hnew
  | [a: ?b * ?c |-_] => destruct a 
  | [|- _] => solve [repeat (f_equal); eauto]
  | [|- (?a,?b)=(?c,?d)] => assert (a=c) by eauto; f_equal; eauto
  | [|- (?a,?b)=(?c,?d)] => assert (b=d) by eauto; f_equal; eauto
  | [|- ?a::?b = ?c::?d] => assert (a=c) by eauto; f_equal; eauto
  | [|- ?a::?b = ?c::?d] => assert (b=d) by eauto; f_equal; eauto
  | [H: ?P ?b |- ?P ?a] => solve [assert (Heq: a=b) by eauto; rewrite Heq; eauto]
  | [H: NoDup ?x, H': NoDup ?x|-_] => clear H'
  | [H: StronglySorted ?x ?y, H': StronglySorted ?x ?y|-_] => clear H'
  | [|- _] => idtac
  end; simpl in *; subst; auto).

Ltac equality := repeat (match goal with
  | [H: ?a = ?b, H': ?a = ?c |-_] => match a with None => idtac | _ => rewrite H in H'; subst end
  | [H: ?a = ?b, H': ?b = ?c |-_] => rewrite H' in H; subst
  | [H: ?a = ?b, H': ?c = ?b |-_] => assert (Heq: a=c) by (rewrite H; auto); inj_all
  | [H: Success ?a = ?b, H': Success ?c = ?b |-_] => assert (Heq': Success a = Success c) by (rewrite H; rewrite H'; auto); injection Heq' as Heq'; subst
  | [H: ?a = ?c, H': ?b = ?c |- ?a = ?b] => rewrite H; rewrite H'; auto
  | [H: ?P ?a, H': ?a = ?b |- ?P ?b ] => rewrite H'; auto
  | [H: ?P ?a, H': ?b = ?a |- ?P ?b ] => rewrite H'; auto
  | [|-_] => idtac
                 end; subst; try discriminate); inj_all.

Ltac invert_type_of := repeat (
  match goal with
  | [H: type_of_atom _ _ |-_] => inversion H; clear H
  | [H: type_of_unop _ _ _ |-_] => inversion H; clear H
  | [H: type_of_binop _ _ _ _ |-_] => inversion H; clear H
  | [H: type_of_ternop _ _ _ _ _ |-_] => inversion H; clear H
  end; subst; try discriminate).

Search "get".
Ltac map_simpl := repeat (match goal with
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
end; auto); auto.
