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

Require Import Translator MapUtils Tactics.
Opaque fiat value_subst exp_subst.


Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Section WithMap.
    Context {locals: forall T, map.map string T} 
    {locals_ok: forall T, map.ok (locals T)}.

    Hint Unfold fenv_wf: core.
    Hint Resolve tenv_wf_ext: core.
    Hint Rewrite lookup_fmap: core. 
    Hint Resolve sorted_perm_eq: core.
    Hint Resolve fst_equal_equiv: core.
    Hint Rewrite lookup_fmap_none: core.
    Hint Constructors Forall2: core.
    Hint Resolve Forall2_map_left Forall2_map_right Forall2_split: core.

    Ltac fenv_reduce := inj_all;
      repeat (match goal with
              | [H: fenv_wf (?a::?b) ?c |-_] => apply fenv_wf_ext in H
              end); map_simpl.

    Theorem type_lookup:
      forall a x Gstore Genv {fstore:tenv} {fenv:tenv}
      (HFst: fenv_wf Gstore fstore)
      (HFenv: fenv_wf Genv fenv)
      (Hlookup: Success a = lookup_ind x Genv) {d},
      type_of fstore fenv (EVar x) (snd (nth a Genv d)).
    Proof.
      induction a; intros; destruct Genv; fenv_reduce; do_both;
      econstructor; map_simpl.
      rewrite <- lookup_fmap; eauto.
    Qed.
    Hint Resolve type_lookup: core.

    Theorem fiat_type_sound:
      forall Gstore Genv {fstore} {fenv} fe ft
      (HFst: fenv_wf Gstore fstore)
      (HFenv: fenv_wf Genv fenv),
      Success ft = get_fiat_type fe Genv Gstore ->
      type_of fstore fenv fe ft.
    Proof.
      unfold get_fiat_type, fenv_wf.
      intros. do_both.
      epose typechecker_sound; eauto.
      eapply proj1 in a1; eauto.
    Qed.
    Hint Resolve fiat_type_sound: core.

    (* Ltac to prove all_success of sorted records are typically sorted *)
    Ltac sort_success a0 :=
      lazymatch goal with [H: Success a0 = all_success (map ?f ?tl'),
      H': StronglySorted _ ?tl'|-_] =>
          (assert (Hfst: map fst tl' = map fst a0) by (
          generalize H; clear; generalize dependent a0; induction tl'; intros; destruct a0; 
          invert_cons; do_both; eauto with permute);
          pose proof (fst_equal_equiv tl' a0); inj_all;
          assert (NoDup (map fst tl')) by eauto with permute;

          assert (Ha: a0 = record_sort a0) by (
          rewrite record_sort_iff_sorted; repeat apply conj; try eapply fst_equal_equiv; eauto with permute);
          try rewrite <- Ha in *;
          assert (Ha': forall a, Permutation a a0 -> a0 = record_sort a) by (
          intros; rewrite record_sort_iff_sorted; repeat apply conj; try eapply fst_equal_equiv; eauto with permute);
          try erewrite <- Ha' in *; clear Ha'; eauto
          ) end.

    Theorem ty_fiat_to_pyro_wf:
      forall ft
      (Htwf: type_wf ft),
      forall A
      (Hty: Success A = ty_fiat_to_pyro ft),
      wf_term (fiat++value_subst++exp_subst) [] A {{s#"ty"}}.

    Proof.
      induction ft using type_IH; intros;
      intros; do_both; inversion Htwf; t''.
      - match goal with [H:Success a = all_success (map ?f' l) |-_] => set (f:=f') in * end.

        assert (map fst a = map fst l /\ StronglySorted (fun p p' => is_true (record_entry_leb p p')) a
        ). {
          generalize H2 case_match_eqn. clear.
          generalize dependent a.
          subst f.
          induction l; intros; destruct a; invert_cons; apply conj; invert_cons; do_both; eauto.
          - constructor.
          - eapply IHl; eauto.
          - specialize (IHl a1); inj_all.
            constructor; inj_all; eauto.
            assert (Hfst: Forall (fun n => is_true (s <=? n)) (map fst l)) by (rewrite Forall_map; eauto).
            rewrite <- H in Hfst. rewrite Forall_map in Hfst; eauto.
        } inj_all.

        subst f; sort_success a.

        repeat match goal with 
               | [H: Success ?a = ?b|-_] => generalize H; clear H 
               | [H: Forall ?a ?b|-_] => generalize H; clear H 
               end.
               clear. intros.
               repeat match goal with
                      | [a: term|-_] => generalize dependent a 
                      | [a: list (string * _) |-_] => generalize dependent a 
                      end.
                      induction l; intros; destruct a; invert_cons; do_both; t''.
    Qed.
    Hint Resolve ty_fiat_to_pyro_wf: core.


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
      do_both.
      match goal with [H: Success _ = all_success (map ?f' l)|-_] => set (f:=f') end.
      assert (Permutation (map f l) (map f l')) by eauto with permute.
      eapply all_success_permutation in case_match_eqn; eauto.
      clear dependent l.

      do_both.

      unfold f in *.
      sort_success x.
      clear dependent a.
      inj_all.

      generalize dependent x.
      generalize dependent lty.
      generalize dependent l'.

      induction l'; intros; destruct x; invert_cons; do_both; t''.
    Qed.
    Hint Resolve ty_list_fiat_to_pyro: core.

    Theorem env_fiat_to_pyro_wf:
      forall Genv {fenv}
      (HGenv: fenv_wf Genv fenv),
      forall Gp (Henv: Success Gp = env_fiat_to_pyro Genv),
      wf_term (fiat++value_subst++exp_subst) [] Gp {{s#"env"}}.
    Proof.
      induction Genv as [|(n,t)];
          intros; fenv_reduce; do_both; t''.
    Qed.
    Hint Resolve env_fiat_to_pyro_wf: core.

    Theorem env_fiat_to_pyro_contents_wf:
      forall Genv {fenv}
      (HGenv: fenv_wf Genv fenv),
      forall G A (Henv: Success (con "ext" [A;G]) = env_fiat_to_pyro Genv),
      wf_term (fiat++value_subst++exp_subst) [] A {{s#"ty"}} /\
      wf_term (fiat++value_subst++exp_subst) [] G {{s#"env"}}.
    Proof.
      induction Genv as [|(n,t)]; intros; fenv_reduce; do_both.
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
      induction n; intros; destruct Genv; do_both; fenv_reduce; do_both.
    - repeat apply conj; t''.
      intros. destruct Genv; do_both. fenv_reduce; do_both; eauto.
    - edestruct IHn with (Genv:=Genv) as [HGp'' [HA Hind]]; eauto.
      repeat apply conj; t''.
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
      destruct n; destruct Genv; fenv_reduce; do_both.
      - t''.
      - destruct n; do_both.
        + destruct Genv; fenv_reduce; do_both. t''.
        + specialize (get_ind_wkn_fiat_to_pyro_wf n) with (Genv:=Genv) (fenv:=x) as H';
          do_both.
          destruct Genv; fenv_reduce; do_both.
          { destruct n; do_both. }
          edestruct H'; eauto; clear H'; do_both.
          edestruct H6; do_both.
          specialize H9 with (s,t); rewrite <- H9 in Hty; do_both.
          t''.
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
      NoDup (map fst l') /\
      (map fst l') = (map fst tl') /\
      Forall2 (type_of fstore fenv) (map snd l') (map snd tl') /\
      StronglySorted (fun p p' => is_true (record_entry_leb p p')) tl' /\
      (Forall (fun p => exists pt, Success pt = expr_fiat_to_pyro (snd p) Genv Gstore) l') /\
      (Success pt = expr_fiat_to_pyro (ERecord l') Genv Gstore).
    Proof.
      intros.
      specialize (StronglySorted_record_sort l) as Hsl. fold l' in Hsl.
      specialize (Permuted_record_sort l) as Hpl. fold l' in Hpl.

      intros; invert_cons; inversion Hty; do_both.

      all: match goal with [H:Success ?a = all_success (map ?f' ?l)|-_] => set (f:=f') in * end.
      all: assert (Hpn: Permutation (map f l) (map f l')) by eauto with permute;
      specialize (all_success_permutation Hpn) as Hs; inj_all; do_both.

      all: set (n := map fst l) in *; set (n' := map fst l') in *; inj_all;
      assert (Hpll': Permutation n n') by (unfold n, n'; eauto with permute);
      gather n; gather n'; assert (NoDup n') by eauto with permute.

      all: unfold n', n, f in *; sort_success x; do_both.
      clear dependent a1.

      assert (
      Forall2 (fun a b => type_of fstore fenv (snd a) (snd b)) l' tl' /\
      n' = map fst tl'
      ). {
        unfold n'.
        apply Forall2_map_right with (f:=snd) in H2.
        apply Forall2_map_left with (f:=snd) in H2.

        assert (Hstrong: Forall2 (fun a b => type_of fstore fenv (snd a) (snd b) /\ fst a = fst b) l tl). {
          apply Forall2_split; apply conj; eauto. rewrite Forall2_fst_eq; do_both.
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
        induction l'; intros; destruct x; invert_cons; do_both.
    Qed.
    Hint Resolve record_ok: core.

    Ltac inj_types_once := 
      lazymatch goal with
      | [H: Failure _ = lookup_ind _ ?G |-_] =>
          eapply lookup_fmap_none with (Genv:=G) in H; eauto 2
      | [Hty: Success ?ft = get_fiat_type ?fe ?Genv ?Gstore,
          H: tenv_wf ?fenv,
          H': Success ?fenv = fiat_env_to_map ?Genv |-_] =>
              eapply fiat_type_sound in Hty; eauto 2
      | [H: TList _ = TList _ |-_] => inversion H; clear H
      | [H: TRecord _ = TRecord _ |-_] => inversion H; clear H
      | [H: type_wf (TList _)|-_] => inversion H; clear H
      | [Hty: type_of ?fstore ?fenv ?fe ?ft, Hty': type_of ?fstore ?fenv ?fe ?ft',
          HGenv: tenv_wf ?fenv |-_] =>
              assert (Heq: ft = ft') by eauto;
              try assert (type_wf ft') by (eapply type_of__type_wf in Hty'; eauto);
              clear Hty'
      end.
    Ltac inj_types := repeat (try inj_types_once; inj_all; equality).

    Hint Resolve fiat_env_to_map_contains fiat_env_to_map_contents fenv_wf_ext: core.
    Hint Resolve fenv_wf_nil fenv_wf_cons: core.

    Set Ltac Profiling.

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
      induction fe using expr_IH; intros; 
      inversion Hty; inversion Hty'; simpl in *; subst; try discriminate;
      try pose proof (record_ok Hty HFst HFenv He) as Hrec;
      try pose proof (record_ok Hty' HFst HFenv He) as Hrec'; 
      inversion HFst; inversion HFenv;
      invert_type_of.
      all: equality.
      Show Ltac Profile.
      all: inj_types.

      - (* records... *)
        remember (record_sort l) as l' in *.
        rewrite record_sort_iff_sorted in Heql'; inj_all; eauto with permute.
        inj_all.
        clear dependent a0.
        sort_success a1.
        rename a1 into a0.
        f_equal.
        apply Permutation_forall with (l':=l') in H; eauto.
        inj_all.

        clear dependent a0.
        clear dependent l.
        do_both.
        clear dependent tl.
        clear dependent tl0.

        generalize dependent tl'.
        generalize dependent tl'0.
        induction l'; intros; destruct tl'0; destruct tl'; invert_cons; 
        f_equal; inj_types.

      - (* ejoin *)
        f_equal.
        eapply IHfe4 with (Genv:=(y,a1)::(x,a0)::Genv); eauto.
        eapply fenv_wf_cons; map_simpl; eauto; do_both.

      - (* eproj *)
        f_equal. eauto.

    Qed.

    Hint Resolve type_of_unique: core.

    Definition fiat_rules := fiat ++ value_subst ++ exp_subst.

    Definition pyro_expr_wf (pexpr: term) (pty: term) (penv: term) :=
      wf_term fiat_rules [] pexpr (scon "val" [pty;penv]).

    Theorem expr_fiat_to_pyro_wf:
      forall fe Gstore Genv (fstore:tenv) (fenv:tenv) ft
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
      induction fe using expr_IH; intros;
      inversion Hty; simpl in *; subst; try discriminate;
      try pose proof (record_ok Hty HFst HFenv He) as Hrec;
      inversion HFenv; inversion HFst;
      invert_type_of.

      (* now this part takes about fifty years *)
      all: inj_types. 
      all: try solve [t''].

      Show Ltac Profile.
      Unset Ltac Profiling.
      - (* evar, of course *)
        eapply get_ind_fiat_to_pyro_wf; eauto; intros.
        assert (Hty': type_of fstore fenv (EVar x) (snd (nth a0 Genv d))). {
          eapply type_lookup; eauto.
        } inversion Hty'; do_both.

      - (* cons *)
        assert (Success (con "list" [a]) = ty_fiat_to_pyro (TList a3)) by inj_all.
        t''.

      - (* let *)
        specialize (fenv_wf_cons HFenv) as Hewf.
        edestruct Hewf with (x:=x); clear Hewf; eauto 2.
        inj_types.
        assert (pyro_expr_wf a3 A (con "ext" [a4;a])). {
          eapply IHfe2 with (Gstore:=Gstore) (Genv:=(x,a0)::Genv); eauto.
          do_both.
        }
        t''.

      - (* record my beloathed... *)
        specialize (Permuted_record_sort l) as Hpl.
        remember (record_sort l) as l' in *.
        rewrite record_sort_iff_sorted in Heql'; eauto with permute.
        inj_all.

        match goal with [H: Success ?x = all_success (map _ l) |-_] => clear dependent x end.
        apply Permutation_forall with (l':=l') in H; eauto.

        remember (map fst l') as n' in *.
        assert (NoDup (map fst tl')) by eauto with permute.
        assert (NoDup n') by (gather n'; eauto with permute).
        sort_success a1. do_both.

        rename Hfst into Hfst'.
        sort_success a0. do_both.
        rename Hfst into Hfst''.

        inj_types.

        clear dependent l.
        clear dependent tl.
        clear t2.

        rename t1 into t3.
        rename t0 into t2.
        rename a into a3.

        assert ((pyro_expr_wf t3 (con "Trecord" [a2]) a3 /\ 
        Success (con "Trecord" [a2]) = ty_fiat_to_pyro (TRecord tl')) /\
        wf_term (fiat++value_subst++exp_subst) [] a2 (scon "list_ty" []) /\
        t2 = a2
        ). {
          unfold pyro_expr_wf in *. do_both.
          all: sort_success a; inj_all; do_both.

          repeat (match goal with 
                  | [a: term |-_] => generalize dependent a
                  | [l: list _ |-_] => generalize dependent l 
                  end
          ).

          induction l'; intros; destruct tl'; destruct a; destruct a0; invert_cons. 
          - repeat apply conj; t''.
          - inversion HFst. inversion HFenv.
            inj_types.
            edestruct IHl'; eauto; clear IHl'; inj_all; do_both.
            repeat apply conj; t''.
        } inj_all.

      - (* EAccess *)
        match goal with [H: type_wf (TRecord _)|-_] => inversion H; clear H end.
        inj_all.

        assert (Hpwf: pyro_expr_wf a0 (con "Trecord" [a1]) a). {
          eapply IHfe with (fenv:=fenv) (fstore:=fstore); eauto.
          unfold ty_list_fiat_to_pyro, ty_fiat_to_pyro in *.
          inj_all.
        } 
        unfold pyro_expr_wf in *.
        clear dependent fe.

        assert (Hlty: 
        forall tl, StronglySorted (fun p p' => is_true (record_entry_leb p p')) tl -> 
        Forall type_wf (map snd tl) -> NoDup (map fst tl) -> 
        forall a1, Success a1 = ty_list_fiat_to_pyro tl ->
        wf_term fiat_rules [] a1 (scon "list_ty" [])
        ). {
          intros; eapply ty_list_fiat_to_pyro_wf; eauto.
        }
        unfold ty_list_fiat_to_pyro, make_list_ty in *.
        inj_all.
        sort_success a3; do_both.

        repeat match goal with [a:term|-_] => generalize dependent a end.
        generalize dependent s.
        generalize dependent a3.
        generalize dependent l.
        generalize dependent ft.
        generalize dependent a2.

        induction a2; intros; destruct l; simpl in *; try discriminate;
        invert_cons; try contradiction.
        * sort_success a4; inj_types.
          t''. eapply Hlty; inj_all; eauto; sort_success a1.
        * sort_success a5; inj_types.
          eapply IHa2 with (ft:=ft) (l:=l) (s:=s); eauto.
          t''. eapply Hlty; inj_all; eauto; sort_success a1.

      - (* EFilter *)
        t''; cbn.
        * eapply IHfe2 with (Genv:=(x,a1)::Genv) (Gstore:=Gstore); inj_all; eauto.
        * eapply IHfe1 with (Genv:=Genv) (Gstore:=Gstore); eauto; inj_all.
      - (* EJoin *)
        specialize (fenv_wf_cons HFenv) with (x:=x) (a:=a1) as HFenv'; inj_all.
        specialize (fenv_wf_cons HFenv') with (x:=y) (a:=a2) as HFenv''; map_simpl.
        inversion HFenv'; inversion HFenv''.
        inj_types.

        eapply IHfe4 in case_match_eqn13; eauto 2; inj_all.
        eapply IHfe3 in case_match_eqn12; eauto 2; inj_all.
        eapply IHfe2 in case_match_eqn11; eauto 2; inj_all.
        eapply IHfe1 in case_match_eqn10; eauto 2; inj_all.

        t''.

      - (* EProj *)
        specialize (fenv_wf_cons HFenv) with (x:=x) (a:=a2) as HFenv'; inj_all.
        inversion HFenv'.
        inj_types.

        eapply IHfe2 in case_match_eqn7; eauto 2; inj_all.
        eapply IHfe1 in case_match_eqn1; eauto 2; inj_all.

        t''.
    Qed.
  End WithMap.
End WithWord.
