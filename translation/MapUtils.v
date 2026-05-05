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

Require Import Stdlib.Sorting.Permutation.

Require Import Tactics Translator.

Ltac invert_cons := repeat (
  try match goal with
  | [H: NoDup (?b::?c) |-_] => inversion H; clear H
  | [H: StronglySorted ?a (?b::?c) |-_] => inversion H; clear H
  | [H: Permutation [] (?a::?b) |-_] => eapply Permutation_nil in H
  | [H: Permutation (?a::?b) [] |-_] => eapply Permutation_sym in H; eapply Permutation_nil in H
  | [H: Permutation ?a ?a |-_] => clear H
  | [H: Forall2 ?p [] (?a::?b) |-_] => inversion H
  | [H: Forall2 ?p (?a::?b) [] |-_] => inversion H
  | [H: Forall ?p (?a::?b) |-_] => eapply Forall_cons
  end; inj_all).

Hint Constructors Permutation: permute.
Hint Resolve Permuted_record_sort
  Permutation_map
  Permutation_in
  Permutation_NoDup
  Permutation_refl
  Permutation_sym
  Permutation.Permutation_cons_inv 
  Permutation_trans: permute.
Hint Resolve in_eq in_map: core.


Definition fenv_wf (Genv: list(string*type)) (fenv:map.rep) :=
  (Success fenv = fiat_env_to_map Genv) /\
  tenv_wf fenv.
Hint Unfold fenv_wf: core.

Opaque map.put map.get map.empty.

Theorem fiat_env_to_map_contains {x}{t}{Genv}{fenv:map.rep}:
  Success fenv = fiat_env_to_map ((x,t)::Genv) ->
  tenv_wf fenv -> map.get fenv x = Some t.
Proof. 
  simpl; intros; repeat (case_match; try discriminate).
  inversion H; map_simpl.
Qed.

Theorem string_eq_destruct (x:string) (x':string):
  (x=x' \/ x<>x').
Proof.
  rewrite <- String.eqb_neq;
  rewrite <- String.eqb_eq.
  destruct (x=?x'); eauto.
Qed.

Theorem fiat_env_to_map_contents {x}{t}{Genv}{G}{G'}:
  Success G = fiat_env_to_map ((x,t)::Genv) ->
  Success G' = fiat_env_to_map (Genv) ->
  tenv_wf G -> 
  forall x' t', map.get G x' = Some t' ->
  (x=x' /\ t=t') \/ (map.get G' x' = Some t').
Proof.
  simpl; intros; inj_all.
  destruct (string_eq_destruct x' x); repeat (inj_all; map_simpl).
Qed.

Theorem tenv_wf_ext {fenv:map.rep} {t:type} {s:string}:
  map.get fenv s = None ->
  tenv_wf (map.put fenv s t) -> tenv_wf fenv.
Proof.
  intros. unfold tenv_wf in *; intros.
  destruct (string_eq_destruct x s); repeat (inj_all; map_simpl; equality).
  eapply H0 with x; map_simpl.
Qed.
Hint Resolve tenv_wf_ext: core.

Theorem fenv_wf_ext {G} {fenv:map.rep} {t:type} {s:string}:
  fenv_wf ((s,t)::G) fenv -> 
  type_wf t /\ 
  exists fenv',
  fenv = map.put fenv' s t /\
  fenv_wf G fenv' /\
  None = map.get fenv' s.
Proof.
  intros. destruct H; inj_all; eauto.
  apply conj.
  - apply H0 with s; map_simpl.
  - eexists; repeat (apply conj); eauto.
Qed.

Hint Resolve fiat_env_to_map_contains fiat_env_to_map_contents fenv_wf_ext: core.

Ltac fenv_reduce := inj_all;
  repeat (match goal with
  | [H: fenv_wf (?a::?b) ?c |-_] => apply fenv_wf_ext in H
          end); map_simpl; inj_all.

Theorem lookup_fmap:
  forall Genv {fenv:map.rep} (HFenv: fenv_wf Genv fenv) x t {d},
  (exists a, Success a = lookup_ind x Genv /\ t = snd (nth a Genv d))
  <->
  (map.get fenv x = Some t).
Proof.
  induction Genv;
  intros. { unfold fenv_wf in HFenv; apply conj; intros; inj_all. }
  apply conj; intros; fenv_reduce; map_simpl.
  - eapply IHGenv; eauto.
  - exists 0; inj_all.
  - edestruct IHGenv; eauto; clear IHGenv.
    edestruct H4; eauto; clear H4.
    inj_all; equality.
  - edestruct IHGenv; eauto; clear IHGenv.
    edestruct H4; eauto; clear H4.
    inj_all; equality.
  Unshelve. exact ("",TUnit).
Qed.

Hint Rewrite lookup_fmap: core. 

Theorem sorted_perm_eq:
  forall {T} l l',
Permutation l l' ->
NoDup (map fst l) ->
StronglySorted
  (fun p p' : string * T => is_true (Value.record_entry_leb p p')) l ->
StronglySorted
  (fun p p' : string * T => is_true (Value.record_entry_leb p p')) l' ->
  l = l'.
Proof.
  do 5 intro.
  assert (NoDup (map fst l')). {
  assert (Permutation.Permutation (map fst l) (map fst l')) by eauto with permute.
  eauto with permute.
  }
  generalize dependent l'.
  induction l; destruct l'; intros; try solve [invert_cons].
  assert (Hinl': In a (p::l')) by eauto with permute.
  assert (Hinl: In p (a::l)) by eauto with permute.

    invert_cons.
    destruct Hinl' as [Hs'|Hinl']; destruct Hinl as [Hs|Hinl]; invert_cons; try solve [
      apply Permutation.Permutation_cons_inv in H;
      f_equal; eauto
    ].
    pose proof (Forall_In H7 Hinl');
    pose proof (Forall_In H10 Hinl); inj_all.
    unfold is_true, Value.record_entry_leb in *;
    inj_all.
    apply String.leb_antisym in H0, H1; inj_all; eauto.
    assert (In (fst (s,t0)) (map fst l')) by eauto; inj_all.
Qed.
Hint Resolve sorted_perm_eq: core.

Theorem record_sort_iff_sorted {T} {a a': list (string*T)}:
  NoDup (map fst a) ->
  a' = record_sort a <->
  (StronglySorted 
  (fun p p' : string * T => is_true (Value.record_entry_leb p p')) a' /\ 
  Permutation a a').
Proof.
  intros; apply conj; intros; inj_all; eauto.
  - eauto using StronglySorted_record_sort, Permuted_record_sort.
  - symmetry; eapply sorted_perm_eq; eauto using StronglySorted_record_sort, Permuted_record_sort with permute.
Qed.

Theorem fst_equal_equiv {T T'}: 
  forall (a: list (string*T)) (b: list (string*T')),
  map fst a = map fst b ->
  ((NoDup (map fst a) -> NoDup (map fst b)) /\
  (
  StronglySorted (fun p p' : string * T => is_true (Value.record_entry_leb p p')) a ->
  StronglySorted (fun p p' : string * T' => is_true (Value.record_entry_leb p p')) b 
  )).
Proof.
  unfold record_entry_leb.
  induction a; destruct b; intros; apply conj; intros; invert_cons.
  - apply SSorted_nil.
  - constructor; try apply IHa; inj_all.
  assert (Hforall: Forall (fun p => (fun q => is_true (s <=? q)) (fst p)) a0) by eauto.
  apply Forall_map_fst in Hforall.
  replace (map fst a0) with (map fst b) in Hforall.
  rewrite <- Forall_map_fst in Hforall.
  eauto.
Qed.
Hint Resolve fst_equal_equiv.

Ltac invert_lhs :=
  match goal with [|-?a=_] => set (b:=a); assert (a=b) by eauto; destruct b end.

Ltac invert_rhs :=
  match goal with 
  | [|- _ = ?a] => set (b:=a); assert (a=b) by eauto; destruct b
  | [|- exists _, _ = ?a] => set (b:=a); assert (a=b) by eauto; destruct b end.


Definition d:=("",TUnit).

Theorem lookup_fmap_none:
  forall Genv {fenv:map.rep} (HFenv: fenv_wf Genv fenv) x,
  (forall msg, Failure msg = lookup_ind x Genv ->
  map.get fenv x = None) /\
  (map.get fenv x = None ->
  exists msg, Failure msg = lookup_ind x Genv).
Proof.
  pose dnil.
  intros; apply conj; intros; inj_all.
  - invert_lhs; equality. rewrite <- lookup_fmap with (Genv:=Genv) in H0; inj_all; equality.
  - invert_rhs; eexists; equality.
    pose proof lookup_fmap (Genv:=Genv) (fenv:=fenv); inj_all. 
    specialize H1 with x (snd (nth a Genv d)) d; inj_all.
    destruct H1.
    lapply H1; eauto.
    intros; equality.
Unshelve. all: eauto.
Qed.
Hint Rewrite lookup_fmap_none: core.

Theorem fenv_wf_cons:
  forall {Genv} {fenv} (HFenv: fenv_wf Genv fenv) 
  x a {Hnew: map.get fenv x = None} {Htwf: type_wf a},
  fenv_wf ((x,a)::Genv) (map.put fenv x a).
Proof.
  intros.
  unfold fenv_wf in *; inj_all.
  apply conj; eauto. unfold tenv_wf in *; intros; map_simpl; eauto.
  destruct (string_eq_destruct x x0); repeat (inj_all; map_simpl); eauto.
Qed.
Hint Resolve fenv_wf_cons: core.
Hint Resolve StronglySorted_record_sort: core.

Hint Constructors StronglySorted: core.

Theorem all_success_permutation:
  forall {T} (l l': list (result T))
  (Hp: Permutation.Permutation l l') (sl: list T),
  Success sl = all_success l ->
  exists sl',
  Success sl' = all_success l' /\
  Permutation.Permutation sl sl'.
Proof.
  do 4 intro.
  induction Hp; intros; invert_cons; eauto with permute.
Qed.

Theorem Permutation_forall:
  forall {T} (l l': list T) P,
  Permutation l l' ->
  Forall P l -> Forall P l'.
Proof.
  induction 1; intros; invert_cons; eauto with permute.
Qed.

Hint Constructors Forall2: core.

Theorem Forall2_map_left:
  forall {T U T'} (l: list T) (l': list U) P (f: T -> T'),
  Forall2 (fun a b => P (f a) b) l l' <->
  Forall2 P (map f l) l'.
Proof.
  induction l; destruct l'; intros; apply conj; intros; 
  invert_cons; try inversion H; 
  econstructor; inj_all; try apply IHl; eauto.
Qed.

Theorem Forall2_map_right:
  forall {T U U'} (l: list T) (l': list U) P (f: U -> U'),
  Forall2 (fun a b => P a (f b)) l l' <->
  Forall2 P l (map f l').
Proof.
  induction l; destruct l'; intros; apply conj; intros; 
  invert_cons; try inversion H; 
  econstructor; inj_all; try apply IHl; eauto.
Qed.

Theorem Forall2_split:
  forall T T' (l: list T) (l': list T') p q, 
  Forall2 (fun a b => p a b /\ q a b) l l' <-> ((Forall2 p l l') /\ (Forall2 q l l')).
Proof.
  clear.
  induction l; destruct l'; intros; apply conj; intros; 
  invert_cons; try inversion H; repeat constructor; try rewrite IHl in H5; try rewrite IHl; inj_all.
Qed.

Hint Resolve Forall2_map_left Forall2_map_right Forall2_split: core.

Ltac gather n :=
  repeat match goal with
         | [H: n = ?m|-_] => rewrite <- H in *
         | [H: ?m = n|-_] => rewrite H in *
         end.


Theorem fenv_wf_nil:
  fenv_wf [] map.empty.
Proof.
  unfold fenv_wf in *; apply conj; inj_all.
Qed.
Hint Resolve fenv_wf_nil: core.
