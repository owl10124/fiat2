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
Import Stdlib.Sorting.Permutation.

Opaque map.put map.get map.empty.

Opaque fiat value_subst exp_subst.

Theorem type_lookup:
  forall a x Gstore Genv {fstore:map.rep} {fenv:map.rep}
  (HFst: fenv_wf Gstore fstore)
  (HFenv: fenv_wf Genv fenv)
(Hlookup: Success a = lookup_ind x Genv) {d},
  type_of fstore fenv (EVar x) (snd (nth a Genv d)).
Proof.
  induction a; intros; destruct Genv; fenv_reduce; econstructor; map_simpl.
  rewrite <- lookup_fmap; eauto.
Qed.
Hint Resolve type_lookup: core.

Require Import coqutil.Word.Naive.
Local Existing Instance word32_ok.

Theorem fiat_type_sound:
  forall Gstore Genv {fstore} {fenv} fe ft
(HFst: fenv_wf Gstore fstore)
  (HFenv: fenv_wf Genv fenv),
  Success ft = get_fiat_type fe Genv Gstore ->
  type_of fstore fenv fe ft.
Proof.
  unfold get_fiat_type, fenv_wf.
  intros.
  inj_all.
  epose typechecker_sound; eauto.
  eapply proj1 in a1; eauto.
Qed.
Hint Resolve fiat_type_sound: core.

(*
Ltac wf_term_ty := 
  lazymatch goal with
  | [H: Success ?a = ty_fiat_to_pyro ?ft ?Genv |- (wf_term _ _ ?a {{s #"ty"}})] => 
    eapply ty_fiat_to_pyro_wf; try apply H; auto
 end.*)

Theorem ty_fiat_to_pyro_wf:
  forall ft
  (Htwf: type_wf ft),
  forall A
  (Hty: Success A = ty_fiat_to_pyro ft),
  wf_term (fiat++value_subst++exp_subst) [] A {{s#"ty"}}.

Proof.
  induction ft using type_IH; intros;
  intros; inj_all; inversion Htwf; t''; eauto.
  - match goal with [H:Success a = all_success (map ?f' l) |-_] => set (f:=f') in * end.

    assert (map fst a = map fst l /\ StronglySorted (fun p p' => is_true (record_entry_leb p p')) a
    ). {
      generalize H2 case_match_eqn. clear.
      generalize dependent a.
      subst f.
      induction l; intros; destruct a; invert_cons; apply conj; inj_all.
      - eapply IHl; eauto.
      - specialize (IHl a1).
        constructor; inj_all.
        assert (Hfst: Forall (fun n => is_true (s <=? n)) (map fst l)) by (rewrite Forall_map; eauto).
        rewrite <- H in Hfst. rewrite Forall_map in Hfst; eauto.
    } inj_all.

    replace (record_sort a) with a in * by (eapply record_sort_iff_sorted; equality; eauto).

    subst f.
    repeat match goal with 
           | [H: Success ?a = ?b|-_] => generalize H; clear H 
           | [H: Forall ?a ?b|-_] => generalize H; clear H 
           end.
           clear. intros.
   repeat match goal with
           | [a: term|-_] => generalize dependent a 
           | [a: list (string * _) |-_] => generalize dependent a 
          end.
    induction l; intros; destruct a; invert_cons; repeat (inj_all; t'').
Qed.
Hint Resolve ty_fiat_to_pyro_wf: core.

Ltac sort_success a0 :=
    match goal with [H: Success a0 = all_success (map ?f ?tl'),
    H': StronglySorted _ ?tl'
    |-_] =>
    (assert (Hfst: map fst tl' = map fst a0) by (
      generalize H; clear; generalize dependent a0; induction tl'; intros; destruct a0; 
        invert_cons; eauto);
    pose proof (fst_equal_equiv tl' a0); inj_all;
    assert (NoDup (map fst tl')) by eauto with permute;

    assert (Ha: a0 = record_sort a0) by (
    rewrite record_sort_iff_sorted; repeat apply conj; try eapply fst_equal_equiv; eauto with permute);
    try rewrite <- Ha in *;
    assert (Ha': forall a, Permutation a a0 -> a0 = record_sort a) by (
    intros; rewrite record_sort_iff_sorted; repeat apply conj; try eapply fst_equal_equiv; eauto with permute);
    try erewrite <- Ha' in *; clear Ha'; eauto
    ) end.

Theorem ty_list_fiat_to_pyro_wf:
  forall l
  (Htwf: Forall type_wf (map snd l))
  (HDup: NoDup (map fst l)),
  forall lty
  (Hty: Success lty = ty_list_fiat_to_pyro l),
  wf_term (fiat++value_subst++exp_subst) [] lty {{s#"list_ty"}}.
Proof.
  intro l.
  unfold ty_list_fiat_to_pyro.
  remember (record_sort l) as l' in *.
  intros.
  rewrite Forall_map in Htwf.

  rewrite record_sort_iff_sorted in Heql'; eauto. inj_all.
  assert (HDup': NoDup (map fst l')) by eauto with permute.
  clear HDup.
  eapply Permutation_Forall in Htwf; eauto.
  inj_all.
  match goal with [H: Success _ = all_success (map ?f' l)|-_] => set (f:=f') end.
  assert (Permutation (map f l) (map f l')) by eauto with permute.
  eapply all_success_permutation in case_match_eqn; eauto.
  clear dependent l.

  inj_all.

  unfold f in *.
  sort_success x.
  clear dependent a.
  inj_all.

  generalize dependent x.
  generalize dependent lty.
  generalize dependent l'.

  induction l'; intros; destruct x; invert_cons; try solve [t''; eauto].
Qed.
Hint Resolve ty_list_fiat_to_pyro: core.

Theorem env_fiat_to_pyro_wf:
  forall Genv {fenv}
  (HGenv: fenv_wf Genv fenv),
  forall Gp (Henv: Success Gp = env_fiat_to_pyro Genv),
  wf_term (fiat++value_subst++exp_subst) [] Gp {{s#"env"}}.
Proof.
  induction Genv as [|(n,t)];
  intros; fenv_reduce; t''; eauto.
Qed.
Hint Resolve env_fiat_to_pyro_wf: core.

Theorem env_fiat_to_pyro_contents_wf:
  forall Genv {fenv}
  (HGenv: fenv_wf Genv fenv),
  forall G A (Henv: Success (con "ext" [A;G]) = env_fiat_to_pyro Genv),
  wf_term (fiat++value_subst++exp_subst) [] A {{s#"ty"}} /\
  wf_term (fiat++value_subst++exp_subst) [] G {{s#"env"}}.
Proof.
  induction Genv as [|(n,t)]; intros; fenv_reduce.
Qed.

Hint Resolve env_fiat_to_pyro_contents_wf type_of__type_wf: core.

Theorem get_ind_wkn_fiat_to_pyro_wf (n:nat):
  forall Genv {fenv} (HGenv: fenv_wf Genv fenv) 
  Gp (Henv: Success Gp = env_fiat_to_pyro Genv),
  forall wkn Gp'
  (Hw: Success (wkn, Gp') = get_ind_wkn n Gp),
  wf_term (fiat++value_subst++exp_subst) [] Gp' {{s#"env"}} /\
  wf_term (fiat++value_subst++exp_subst) [] wkn (scon "sub" [Gp';Gp]) /\
  (forall A Gp'', con "ext" [A;Gp''] = Gp' -> 
  wf_term (fiat++value_subst++exp_subst) [] Gp'' {{s#"env"}} /\
  wf_term (fiat++value_subst++exp_subst) [] A {{s#"ty"}} /\
  forall {d}, Success A = ty_fiat_to_pyro (snd (nth (S n) Genv d))).
Proof.
  induction n; intros; destruct Genv; inj_all; fenv_reduce.
  - repeat (try apply conj); t''; eauto.
    intros. destruct Genv; inj_all. fenv_reduce. 
  - edestruct IHn with (Genv:=Genv) as [HGp'' [HA Hind]]; eauto.
    repeat (try apply conj); t''; eauto.
Qed.
Hint Resolve get_ind_wkn_fiat_to_pyro_wf: core.

Theorem get_ind_fiat_to_pyro_wf (n:nat):
  forall Genv {fenv} (HGenv: fenv_wf Genv fenv) 
  Gp (Henv: Success Gp = env_fiat_to_pyro Genv),
  forall A (Hty: forall {d}, Success A = ty_fiat_to_pyro (snd (nth n Genv d))),
  forall pt
  (Hw: Success pt = get_ind n Gp),
  wf_term (fiat++value_subst++exp_subst) [] pt (scon "val" [A;Gp]).
Proof.
  intros. 
  set (d:=("",TUnit)); specialize Hty with d.
  destruct n; destruct Genv; fenv_reduce.
  - t''; eauto.
  - destruct n.
    + destruct Genv; fenv_reduce; t''; eauto.
    + specialize (get_ind_wkn_fiat_to_pyro_wf n H0) as H'.
      destruct Genv; fenv_reduce. 
      { destruct n; inj_all. }
      edestruct H4; eauto; clear H4.
      inj_all. specialize H8 with (s,t); rewrite <- H8 in Hty; inj_all.
      t''; eauto.
Qed.
Hint Resolve get_ind_fiat_to_pyro_wf: core.

Theorem record_ok:
  forall {fstore} {fenv} l tl'
  (Hty: type_of fstore fenv (ERecord l) (TRecord tl'))
  Gstore Genv
  (HFst: fenv_wf Gstore fstore)
  (HFenv: fenv_wf Genv fenv)
  pt
  (He: Success pt = expr_fiat_to_pyro (ERecord l) Genv Gstore),
  let l' := record_sort l in
  (map fst l') = (map fst tl') /\
  Forall2 (type_of fstore fenv) (map snd l') (map snd tl') /\
  StronglySorted (fun p p' => is_true (record_entry_leb p p')) tl' /\
  (Forall (fun p => exists pt, Success pt = expr_fiat_to_pyro (snd p) Genv Gstore) l') /\
  (Success pt = expr_fiat_to_pyro (ERecord l') Genv Gstore).
Proof.
  intros.
 specialize (StronglySorted_record_sort l) as Hsl. fold l' in Hsl.
 specialize (Permuted_record_sort l) as Hpl. fold l' in Hpl.

  intros; invert_cons; inversion Hty; equality.

  all: match goal with [H:Success ?a = all_success (map ?f' ?l)|-_] => set (f:=f') in * end.
  all: assert (Hpn: Permutation (map f l) (map f l')) by eauto with permute;
    specialize (all_success_permutation Hpn) as Hs; inj_all; equality.

    all: set (n := map fst l) in *; set (n' := map fst l') in *; inj_all;
    assert (Hpll': Permutation n n') by (unfold n, n'; eauto with permute);
    gather n; gather n'; assert (NoDup n') by eauto with permute.

    all: unfold n', n, f in *; sort_success x; equality.
    clear dependent a1.

    assert (
      Forall2 (fun a b => type_of fstore fenv (snd a) (snd b)) l' tl' /\
      n' = map fst tl'
    ). {
      unfold n'.
        apply Forall2_map_right with (f:=snd) in H2.
        apply Forall2_map_left with (f:=snd) in H2.

        assert (Hstrong: Forall2 (fun a b => type_of fstore fenv (snd a) (snd b) /\ fst a = fst b) l tl). {
          apply Forall2_split; apply conj; eauto. rewrite Forall2_fst_eq; equality.
        }
        gather n.
        eapply Forall2_Permuted_StronglySorted in Hstrong; repeat apply conj; eauto; intros; inj_all;
        try solve [eapply Forall2_impl; eauto; intros; inj_all];
        apply Forall2_fst_eq;
        apply Forall2_impl with (R2:=(fun a b => fst a = fst b)) in Hstrong; intros; inj_all.
      } inj_all.
    subst l'; remember (record_sort l) as l' in *.
    clear dependent l.

    repeat (apply conj; eauto).
    - apply Forall2_map_right with (f:=snd); apply Forall2_map_left with (f:=snd); eauto.
    - generalize case_match_eqn0; clear; generalize dependent x.
      induction l'; intros; destruct x; invert_cons.
Qed.
Hint Resolve record_ok: core.

Theorem type_of_unique:
  forall fe {fstore} {fenv} ft ft'
  (Hty: type_of fstore fenv fe ft) 
  (Hty': type_of fstore fenv fe ft')
  Gstore Genv
  (HFst: fenv_wf Gstore fstore)
  (HFenv: fenv_wf Genv fenv)
  pt
  (He: Success pt = expr_fiat_to_pyro fe Genv Gstore), ft = ft'.
Proof.
  induction fe using expr_IH; intros; inversion Hty; inversion Hty'; subst; try discriminate;
  try solve [inj_all; equality;
  invert_type_of; inj_all; equality; eauto].
  - (* evar *)
    equality.
    assert (t1=t0) by eauto; subst.
    assert (a0=t0) by eauto; subst.
    eapply lookup_fmap_none with (fenv:=fenv) in case_match_eqn6; eauto.
    eapply IHfe2 with (Genv := (x,t0)::Genv); eauto.
    eapply fenv_wf_cons; eauto.
    unfold fenv_wf in *; inj_all.
    eapply type_of__type_wf in H3; eauto.
  - (* records... *)
    pose proof (record_ok Hty HFst HFenv He) as Hrec.
    pose proof (record_ok Hty' HFst HFenv He) as Hrec'. 
    inj_all.
    specialize (StronglySorted_record_sort l) as Hsl.
    specialize (Permuted_record_sort l) as Hpl.
    f_equal.
    remember (record_sort l) as l' in *.
    apply Permutation_forall with (l':=l') in H; eauto.

    clear dependent a0.
    clear dependent l.
    clear dependent tl.
    clear H10.

    generalize dependent tl'.
    generalize dependent tl'0.
    induction l'; intros; destruct tl'0; destruct tl'; invert_cons.
  - (* eaccess *)
    specialize IHfe with (fstore:=fstore) (fenv:=fenv) (ft:=(TRecord tl)) (ft':=(TRecord tl0)) (Gstore:=Gstore) (Genv:=Genv); inj_all.
    inversion IHfe; equality.
Qed.
    
(*

    match goal with [H:Success a0 = all_success (map ?f' l)|-_] => set (f:=f') in * end.
    specialize (StronglySorted_record_sort l) as Hsl.
    set (l':=(record_sort l)) in *.
    set (a':=(record_sort a0)) in *.
    assert (Hpl: Permutation (map f l) (map f l')) by eauto with permute.
    specialize (all_success_permutation Hpl) as Hs; inj_all.

    set (n := map fst l) in *; set (n' := map fst l') in *; inj_all.
    assert (Hpll': Permutation n n') by (unfold n, n'; eauto with permute).


      assert ((map fst x = map fst l') /\ StronglySorted (fun p p' => is_true (record_entry_leb p p')) x). {
        clear Hpl. clear dependent a0. subst n n'; clear Hpll'.
        generalize dependent x.
        generalize dependent l'.
        clear. 
        unfold f, record_entry_leb in *.
        induction l'; intros; invert_cons.
        repeat (match goal with [a:?b*?c|-_]=>destruct a end).
        apply conj; try f_equal; equality.
        constructor; inj_all.
        assert (Hfst: Forall (fun n => is_true (s <=? n)) (map fst l')) by (rewrite Forall_map; eauto).
        rewrite <- H in Hfst. rewrite Forall_map in Hfst; eauto.
      } inj_all.

    assert (Hrec: x = a'). { 
      fold n' in H7.
      apply sorted_perm_eq; gather n'; gather n; unfold a'; eauto with permute. 
    }

    specialize (Permuted_record_sort l) as Hprl. fold l' in Hprl.

    apply permutation_forall with (l':=l') in H; eauto.

    (*
    assert (
    (map (fun p => (fst p, Success (fst (snd p)))) a0
    = map (fun p => (fst p, expr_fiat_to_pyro (snd p) Genv Gstore)) l) /\
    (map (fun p => (fst p, Success (snd (snd p)))) a0 
    = map (fun p => (fst p, ty_fiat_to_pyro (snd p))) tl) /\
    (map (fun p => (fst p, Success (snd (snd p)))) a0 
    = map (fun p => (fst p, ty_fiat_to_pyro (snd p))) tl0)
    ). {

      induction l'; intros; destruct a0, tl, tl0; invert_cons.
      repeat (match goal with [a:?b*?c|-_]=>destruct a end); inj_all.
      assert (a2=t1) by eauto; 
      assert (a2=t2) by eauto; equality.
      edestruct IHl with (tl:=tl) (tl0:=tl0); inj_all; eauto; equality.
      repeat (try apply conj; try f_equal); equality.
    } inj_all.
    (*
    apply permutation_forall with (l':=l') in H; eauto.

    subst l'. remember (record_sort l) as l'.
    gather x; gather l'; gather tl'; gather tl0'.
    clear dependent l.
    clear dependent a0. 
    clear dependent tl. 
    clear dependent tl0. 
    rename x into a0'.
    
     *)
     *)
    
    assert (Hpy: Forall 
      (fun p => exists pt, Success pt = expr_fiat_to_pyro (snd p) Genv Gstore)  
      l'). { 
        subst n n'; clear Hpll'.
        gather x. clear dependent a0.
        generalize dependent t.
        generalize dependent t0.
        generalize dependent x.
        clear Hpl Hprl.
        induction l'; intros; inj_all.
        repeat (match goal with [a:?b*?c|-_]=>destruct a end).
        unfold f in *.
        eapply Forall_cons; invert_cons; eauto.
      }

    assert (
      Forall2 (fun a b => type_of fstore fenv (snd a) (snd b)) l' tl' /\
      Forall2 (fun a b => type_of fstore fenv (snd a) (snd b)) l' tl'0 /\
      n' = map fst tl' /\
      n' = map fst tl'0
    ). {
      unfold n'.
        apply Forall2_map_right with (f:=snd) in H2, H9;
        apply Forall2_map_left with (f:=snd) in H2, H9.

        assert (Hstrong: Forall2 (fun a b => type_of fstore fenv (snd a) (snd b) /\ fst a = fst b) l tl). {
          apply Forall2_split; apply conj; eauto. rewrite Forall2_fst_eq; equality.
        }
        assert (Hstrong0: Forall2 (fun a b => type_of fstore fenv (snd a) (snd b) /\ fst a = fst b) l tl0). {
          apply Forall2_split; apply conj; eauto. rewrite Forall2_fst_eq; equality.
        }
        gather n.
        eapply Forall2_Permuted_StronglySorted in Hstrong, Hstrong0; repeat apply conj; eauto; intros; inj_all;
        try solve [eapply Forall2_impl; eauto; intros; inj_all];
        apply Forall2_fst_eq;
        apply Forall2_impl with (R2:=(fun a b => fst a = fst b)) in Hstrong, Hstrong0; intros; inj_all.
      } inj_all.
      subst l'. 
      remember (record_sort l) as l' in *.
      subst a'.
      remember (record_sort a0) as a' in *.
    subst n'.
    remember (map fst l') as n' in *.
    clear dependent a0.
    clear dependent l.
    clear dependent tl.
    clear dependent tl0.
    inj_all.

    assert (tl'=tl'0). {
      generalize dependent t;
      generalize dependent t0;
      generalize dependent tl';
      generalize dependent tl'0;
      generalize dependent a'.
        induction l'; intros; destruct tl'; destruct tl'0; invert_cons.
    } inj_all.

    (*
        apply Forall2_map_right with (f:=snd);
        apply Forall2_map_left with (f:=snd);
        apply Forall2_map_right with (f:=snd) in H2;
        apply Forall2_map_left with (f:=snd) in H2.

        set (n := map fst l) in *; gather n; inj_all.
        intros; inj_all.
        Compute Forall2_Permuted_StronglySorted.
    }

      apply permutation_forall with (l':=l) in Hpy; eauto with permute.

      assert (tl = tl0). {
        clear dependent x.
        clear case_match_eqn0 Hty Hty'.
        generalize dependent l.
        generalize HFst HFenv Heq.
        clear.
        intros.
        generalize dependent tl.
        generalize dependent tl0.
        generalize dependent l.
        induction l; intros; inj_all;
        destruct tl; try solve [inversion H2; eauto];
        destruct tl0; try solve [inversion H9; eauto].
        repeat (match goal with [a:?b*?c|-_]=>destruct a end).
        subst l' n; invert_cons.
        repeat (f_equal; inj_all; eauto).
        eapply IHl; eauto with permute.
      } inj_all.
      assert (tl'=tl'0); inj_all.
      apply sorted_perm_eq; eauto with permute.
     *)
Qed.
 *)

Hint Resolve type_of_unique: core.
Ltac inj_types := try repeat (
  try match goal with
  | [Hty: Success ?ft = get_fiat_type ?fe ?Genv ?Gstore, Hty': type_of ?fstore ?fenv ?fe ?ft' |-_] =>
      assert (Hfteq: ft=ft') by eauto;
      assert (type_wf ft') by (apply type_of__type_wf in Hty'; eauto);
      clear Hty'
  end; equality); inj_all.

Definition fiat_rules := fiat ++ value_subst ++ exp_subst.

Definition pyro_expr_wf (pexpr: term) (pty: term) (penv: term) :=
  wf_term fiat_rules [] pexpr (scon "val" [pty;penv]).

Theorem expr_fiat_to_pyro_wf:
  forall fe Gstore Genv (fstore:map.rep) (fenv:map.rep) ft
  (HFst: fenv_wf Gstore fstore)
  (HFenv: fenv_wf Genv fenv)
  (Hty: type_of fstore fenv fe ft),
  forall pt A Gp
  (He: Success pt = expr_fiat_to_pyro fe Genv Gstore)
  (Hty: Success A = ty_fiat_to_pyro ft)
  (Henv: Success Gp = env_fiat_to_pyro Genv),
  pyro_expr_wf pt A Gp.
Proof.
  unfold pyro_expr_wf in *;
  induction fe using expr_IH; simpl; inj_all; intros;
  inversion HFenv;
  inversion HFst;
  inversion Hty; clear Hty; invert_type_of; inj_types; try solve [t''; eauto].
  (*symmetry in case_match_eqn; 
  pose proof env_fiat_to_pyro_wf Genv HGenv HFenv case_match_eqn as HGenv_wf.*)
  - eapply get_ind_fiat_to_pyro_wf; eauto; intros.
    assert (Hty': type_of fstore fenv (EVar x) (snd (nth a0 Genv d))). {
      eapply type_lookup; eauto.
    }
    inversion Hty'; equality.
  - (* cons *)
    assert (Success (con "list" [a0]) = ty_fiat_to_pyro (TList t1)) by inj_all.
    t''; eauto.
  - (* let *)
    eapply lookup_fmap_none with (fenv:=fenv) in case_match_eqn6; eauto.
    specialize (fenv_wf_cons HFenv) as Hewf.
    edestruct Hewf with (x:=x) (a:=t1); eauto.
    inj_types.

    assert (pyro_expr_wf a3 A (con "ext" [a4;a])). {
      eapply IHfe2 with (Gstore:=Gstore) (Genv:=(x,t1)::Genv); eauto.
      inj_all.
    }

    t''; eauto.
  - (* record my beloathed... *)
    assert (Hty: type_of fstore fenv (ERecord l) (TRecord tl')) by (econstructor; eauto).
    assert (He: Success t = expr_fiat_to_pyro (ERecord l) Genv Gstore) by inj_all.
    pose proof (record_ok Hty HFst HFenv He) as Hrec.
    inj_all.
    specialize (StronglySorted_record_sort l) as Hsl.
    specialize (Permuted_record_sort l) as Hpl.
    f_equal.
    remember (record_sort l) as l' in *.
    rewrite record_sort_iff_sorted in Heql'; equality.

    clear dependent a4.
    apply Permutation_forall with (l':=l') in H; eauto.

   remember (map fst l') as n' in *.
   assert (NoDup (map fst tl')) by eauto with permute.
    assert (NoDup n') by (gather n'; eauto with permute).
    sort_success a0. equality.
    sort_success a. equality.

    clear dependent l.
    clear dependent tl.


    (*
    generalize dependent tl'.
    generalize dependent a1.
    generalize dependent t1.
    generalize dependent t2.
    

    assert (StronglySorted (fun p p' => is_true (Value.record_entry_leb p p')) l') by eauto using StronglySorted_record_sort.
    (*
    assert (StronglySorted (fun p p' => is_true (Value.record_entry_leb p p')) tl). {
      generalize l H5 H8 H4; clear.
      induction tl; intros; destruct l; invert_cons; econstructor; eauto.
      destruct p, a; unfold Value.record_entry_leb in *; inj_all.
      assert (Forall (fun p => is_true (s0<=? p)) (map fst l)). {
        rewrite Forall_map; eauto.
      }
      rewrite H3 in H.
      rewrite Forall_map in H; eauto.
   }
      assert (NoDup (map fst tl) /\ NoDup (map fst tl')) by
      (apply conj;
        eauto using Permutation.Permutation_NoDup, Permutation.Permutation_map).
      inj_all.
    assert (tl=tl') by eauto using sorted_perm_eq.
   *)
    invert_cons.
     *)
    rename a1 into a2.

    assert ((pyro_expr_wf t1 (con "Trecord" [a2]) a3 /\ 
    Success (con "Trecord" [a2]) = ty_fiat_to_pyro (TRecord tl')) /\
    wf_term (fiat++value_subst++exp_subst) [] a2 (scon "list_ty" []) /\
    t2 = a2
    ). {
      unfold pyro_expr_wf in *. equality.
      all: clear Hfst; sort_success a1.
      all: clear Heq; equality.
      inj_all.

      generalize dependent tl'.
      generalize dependent a.
      generalize dependent a0.
      generalize dependent a1.
      generalize dependent a3.
      generalize dependent t0.
      generalize dependent t1.
      generalize dependent t2.
      generalize HFst HFenv.
      generalize dependent l'.
      clear.

      induction l'; intros; destruct tl'; destruct a; destruct a1; invert_cons. 
      - repeat (apply conj); t''; eauto.
      - inversion HFst. inversion HFenv.
        inj_types.
      edestruct IHl'; eauto; clear IHl'; inj_all; equality.
      repeat (apply conj; t''; eauto).
    } inj_all.

  - inversion Hfteq; inj_all.
    inversion H3; clear H3; inj_all. (* type wf *)
    assert (Hpwf: pyro_expr_wf a0 (con "Trecord" [a1]) a). {
      eapply IHfe with (fenv:=fenv) (fstore:=fstore); eauto.
      eauto.
      unfold ty_list_fiat_to_pyro, ty_fiat_to_pyro in *.
      generalize case_match_eqn2; clear. generalize dependent a1.
      induction tl; intros; destruct a1; invert_cons.
    } clear dependent fe.
    unfold pyro_expr_wf in *.

    assert (Hlty: forall tl, StronglySorted (fun p p' => is_true (record_entry_leb p p')) tl
  -> Forall type_wf (map snd tl) -> NoDup (map fst tl) -> 
    forall a1, Success a1 = ty_list_fiat_to_pyro tl ->
    wf_term fiat_rules [] a1 (scon "list_ty" [])
    ). {
      intros.
      eapply ty_list_fiat_to_pyro_wf; eauto.
    }
    unfold ty_list_fiat_to_pyro, make_list_ty in *.
    inj_all.
    sort_success a3; equality.

    repeat (match goal with 
            | [a:term|-_] => generalize dependent a 
            end).
    generalize dependent s.
    generalize dependent a3.
    generalize dependent tl.
    generalize dependent ft.
    generalize dependent a2.

    induction a2; intros; destruct tl; simpl in *; try discriminate;
    invert_cons; try contradiction.
     * sort_success a4; inj_types.
       t''; eauto. eapply Hlty; inj_all; eauto; sort_success a1.
     * sort_success a5; inj_types.
       eapply IHa2 with (ft:=ft) (tl:=tl) (s:=s); eauto.
       t''; eauto. eapply Hlty; inj_all; eauto; sort_success a2.
Qed.
