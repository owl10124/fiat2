Set Implicit Arguments.
From fiat2 Require Import Language TypeSystem TypeSound.

Require Import coqutil.Map.Interface coqutil.Datatypes.dlist.
From Utils Require Import Utils.

From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Tools.EGraph.Automation Tools.EGraph.Defs Tools.UnElab.
From Pyrosome Require Import Lang.FiatTest.
Import Core.Notations.
Import coqutil.Datatypes.Result Result.List Result.ResultMonadNotations.

Require Stdlib.derive.Derive.
Require Import Datatypes.String Lists.List.
Open Scope string.
Import ListNotations.
Open Scope list.

Locate dlist.
Require Import Stdlib.FSets.FMapInterface.

Print expr.
Locate term.
About Term.term.
Compute {{e#"true"}}.
Compute {{e#"notb" #"true"}}.
Compute (con "andb" [{{e#"true"}};{{e#"true"}}]).

Fixpoint lookup_ind {T} (name: string) (rec: list (string * T)) :=
  match rec with
  | (name', _) :: rec' => if (name' =? name) then (Success 0) else 
      n <- lookup_ind name rec' ;; Success (S n)
| nil => error:("var" name "not found in env")
  end.

(*
Definition xa := lookup_ind "a" [("a", ABool);("b", ABool)].
Definition xb := lookup_ind "b" [("a", ABool);("b", ABool)].
Definition xc := lookup_ind "c" [("a", ABool);("b", ABool)].
Compute List.all_success([xc;xa;xb]).
Compute List.all_success([xa;xb]).
*)

(*
Fixpoint lookup (name: string) (rec: list (string * type)) :=
  match rec with
  | (name', val) :: rec' => 
      if (name' =? name) then (Success val) else (lookup name rec')
  | nil => Failure _
  end.
*)
Definition x := {{e #"ext" (#"ext" #"emp" #"bool") #"bool"}}.
Print x.

(*
Fixpoint pyro_env_hd (G: term) :=
  match G with 
  | con "ext" [a;G'] => Success a
  | con "emp" [] => error:(G "is empty")
  | _ => error:(G "is not an env")
  end.
Fixpoint pyro_env_wkn (G: term) :=
match G with 
  | con "ext" [a;G'] => Success G'
  | con "emp" [] => error:(G "is empty")
  | _ => error:(G "is not an env")
  end.
*)

Compute map.mk string type.

Require coqutil.Map.SortedListString.
Local Existing Instance SortedListString.map.

Print map.put.
Fixpoint fiat_env_to_map (G: list (string * type)) :=
  match G with
  | nil => Success map.empty
  | (n,t)::G' => 
      Gm <- fiat_env_to_map G' ;; 
      match map.get Gm n with None => Success (map.put Gm n t) | Some _ => error:("key" n "already in" G) end
  end.

(*
  fold_right 
    (fun x a => map.put a (fst x) (snd x))
    map.empty G.
 *)

Compute fenv <- fiat_env_to_map [("a",TBool)] ;; synthesize_expr fenv _ (EAtom (ABool true)).

(* wkn returns w and Gp', with w a substitution sending Gp to Gp'. essentially weakens n times *)
Fixpoint get_ind_wkn (n: nat) (Gp: term): result (term * term) :=
    match Gp with con "ext" [A;Gp'] =>
    match n with
    | 0 => Success (con "wkn" [A;Gp'], Gp')
    | S n => 
        '(w, Gp'') <- get_ind_wkn n Gp' ;;
         Success ((con "cmp" [w; con "wkn" [A;Gp']; Gp''; Gp'; Gp]), Gp'')
    end
    | _ => error:(Gp "not a nonempty env")
    end.

(* represents the kth term in Gp. *)
Definition get_ind (n: nat) (Gp: term): result term :=
    match n with
    | 0 => match Gp with 
      | con "ext" [A;Gp'] => Success (con "hd" [A;Gp'])
      | _ => error:(Gp "not a nonempty env")
     end
    | S n => '(w, Gp') <- get_ind_wkn n Gp ;; 
        match Gp' with 
        | con "ext" [A';Gp''] => 
         Success (con "val_subst" [con "hd" [A';Gp'']; A'; w; Gp'; Gp])
        | _ => error:(Gp' "not a nonempty env")
    end 
  end.

Compute x.
Compute get_ind 0 x.
Print dlist.dlist.
Print Result.

Require Import FunInd.

Fixpoint ty_fiat_to_pyro (ft: type): result term :=
  match ft with
  | TBool => Success {{e#"bool"}}
  | TList t => tl <- ty_fiat_to_pyro t ;; Success (con "list" [tl])
  | TRecord l => (rec_list <- (fold_right 
      (fun x a' => a <- a' ;; 
      trec <- ty_fiat_to_pyro (snd x) ;; 
      Success (con "cons_list_ty" [a; trec])) 
      (Success {{e#"empty_list_ty"}}) l) ;; Success (con "Trecord" [rec_list]))
  | _ => error:("fiat type" ft "not supported")
  end.

Definition term_to_sort (pt: term) :=
  match pt with
  | con x y => scon x y
  | _ => scon "" []
  end.

Fixpoint env_fiat_to_pyro (G: list (string * type)): result term :=
  match G with
  | [] => Success {{e#"emp"}}
  | (_,x)::G' => 
      A <- ty_fiat_to_pyro x ;;
      Gp <- env_fiat_to_pyro G' ;;
      Success (con "ext" [A;Gp])
  end.
  (*
  fold_right 
      (fun x Gp => (con "ext" [(ty_fiat_to_pyro (snd x) G); Gp])) 
      {{e#"emp"}} G.
   *)

Compute env_fiat_to_pyro [("a", TBool); ("b", TRecord([("a",TBool)]))].

Definition get_fiat_type (e: expr) (G: list (string * type)): result type :=
  fenv <- fiat_env_to_map G ;;
  '(t,_) <- synthesize_expr map.empty fenv e ;; Success t.

Fixpoint expr_fiat_to_pyro (fe: expr) (G: list (string * type)): result term :=
  (*(G: tenv) (fe: expr) (ft: type) (fwt: type_of G G fe ft) := *)
  Gp <- env_fiat_to_pyro G ;;
  match fe with
  | EVar name => n <- lookup_ind name G ;; get_ind n Gp
| EAtom fa => match fa with 
                | ABool b => match b with
                             | true => Success (con "true" [Gp])
                             | false => Success (con "false" [Gp])
                             end
                | ANil sft => match sft with 
                              | Some ft => 
                                  A <- ty_fiat_to_pyro ft ;;
                                  Success (con "lempty" [A; Gp])
                              | None => error:("anil defined without type")
                              end
                | _ => error:("atom" fa "not defined yet")
                end
  | EUnop op fe => 
      e <- expr_fiat_to_pyro fe G ;;
                       match op with
                       | ONot => Success (con "notb" [e; Gp]) 
                       | OLength => Success (con "length" [e; Gp])
                       | _ => error:("unop" op "not defined yet")
                       end
  | EBinop op fe1 fe2 => 
      e1 <- expr_fiat_to_pyro fe1 G ;; 
      e2 <- expr_fiat_to_pyro fe2 G ;;
      ty <- get_fiat_type fe1 G ;;
      A <- ty_fiat_to_pyro ty ;;
                             match op with
                             | OAnd => Success (con "andb" [e2;e1;Gp])
                             | OOr => Success (con "orb" [e2;e1;Gp])
                             | OCons => Success (con "cons" [e2;e1;A;Gp])
                             | _ => error:("binop" op "not defined yet")
                             end
  | EIf fcond fe1 fe2 => 
      cond <- expr_fiat_to_pyro fcond G ;;
      e1 <- expr_fiat_to_pyro fe1 G ;;
      e2 <- expr_fiat_to_pyro fe2 G ;;
      ty <- get_fiat_type fe1 G ;;
      A <- ty_fiat_to_pyro ty ;;
      Success (con "if" [e2;e1;A;cond;Gp])
  | ELet fe1 name fe2 => 
      ty_e1 <- get_fiat_type fe1 G ;;
      e1 <- expr_fiat_to_pyro fe1 G ;; 
      e2 <- expr_fiat_to_pyro fe2 ((name,ty_e1)::G) ;; 
      A <- ty_fiat_to_pyro ty_e1 ;;
      Success (con "val_subst" [
        e2;
        A;
        (con "snoc" [e1; A; (con "id" [Gp]); Gp; Gp]);
        (con "ext" [A;Gp]);
        Gp
      ]) 
  | ERecord gl => 
      '(rec,_) <- (fix build_rec (gl: list(string * expr)) (Gp: term) :=
        match gl with
        | nil => Success (con "empty_record" [Gp], con "empty_list_ty" [])
        | (name, expr) :: gl' => 
            v <- expr_fiat_to_pyro expr G ;;
            ty <- get_fiat_type expr G ;;
            A <- ty_fiat_to_pyro ty ;;
            '(l, lty) <- build_rec gl' Gp ;;
            Success (con "cons_record" [l;v;lty;A;Gp], con "cons_list_ty" [lty;A])
        end
      ) gl Gp ;; Success rec (* TODO elab works up to here... *)
  | EAccess fe name =>
      rec <- expr_fiat_to_pyro fe G ;;
      Success (con "car" [Gp;rec]) (*TODO*)
  | EFilter tag ftb name fp =>
      (* note name is the bound variable for the record in fp *)
      ty_tb <- get_fiat_type ftb G ;;
      match ty_tb with TList ty_rec =>
      tb <- expr_fiat_to_pyro ftb G ;; 
      p <- expr_fiat_to_pyro fp ((name, ty_rec) :: G) ;;
      Success (con "filter" [Gp;(con "val_subst" [p]);tb])
      | _ => error:("table" ftb "of type" ty_tb "not a list of records") end
  | EJoin tag fl1 fl2 name1 name2 fp fr =>
      (* TODO strings *)
      tb1 <- expr_fiat_to_pyro fl1 G ;;
      tb2 <- expr_fiat_to_pyro fl2 G ;;
      p <- expr_fiat_to_pyro fp G ;;
      r <- expr_fiat_to_pyro fr G ;;
        Success (con "join" [r;p;tb2;tb1;Gp])
  | EProj tag fl name fr =>
      (* TODO strings *)
      tb <- expr_fiat_to_pyro fl G ;; 
      r <- expr_fiat_to_pyro fr G ;;
      Success (con "proj" [r;tb;Gp])
  | _ => error:("term" fe "not defined")
  end.

Definition trx := expr_fiat_to_pyro (EAtom (ABool false)) [].

Compute trx.

(* do post-elab terms... i.e. outputs of trx_derived *)

(* synthesize type in typesystem.v? *)
Compute lang.

Ltac t'' := repeat (
  match goal with
  | [|-Model.wf_term _ _ _] => t'
  | [|-wf_term _ _ _ _] => eapply wf_term_by'
  | [|-wf_args _ _ _] => econstructor
  | [|-_] => unshelve (repeat t); simpl
  end).

Derive te
  SuchThat (elab_term (value_subst) [] {{e#"emp"}} te {{s#"env"}} )
  As te_wf.
Proof.  t''.  Qed.
Print te. Print te_wf.

Print wf_term.

Goal wf_term (value_subst) [] {{e#"emp"}} {{s#"env"}}.
Proof.  t''.  Qed.

Derive trx_derived
  SuchThat (elab_term (fiat++value_subst++exp_subst) [] {{e#"cons" #"false" (#"lempty" #"bool")}} trx_derived {{s#"val" #"emp" (#"list" #"bool")}} )
  As trx_wf.
Proof. t''. Qed.
Print trx_derived.  Print trx_wf.

Goal wf_term (fiat++value_subst++exp_subst) [] {{e#"true" #"emp"}} {{s#"val" #"emp" #"bool"}}.
Proof.  t''.  Qed.

Compute trx_derived.

Definition trx' := match (
  expr_fiat_to_pyro (
  (*
  ELet (EAtom (ABool false)) "x" (
    ELet (EAtom (ABool true)) "y" (
      EBinop OAnd (EVar "x") (EVar "y")))
   *)
  ELet (EAtom (ABool false)) "x" (
  ELet (EAtom (ABool true)) "y" (
   EUnop ONot (EVar "y")))
  ) [])
  with Success x => x | _ => {{e#""}} end.

Goal wf_term (fiat++value_subst++exp_subst) [] trx' {{s#"val" #"emp" #"bool"}}.
Proof.  t''.  Qed.

Compute hide_term_implicits (fiat++value_subst++exp_subst) trx'.

Compute hide_term_implicits (fiat++value_subst++exp_subst)
  (PositiveInstantiation.egraph_simpl' (fiat++value_subst++exp_subst) 20 20 60 [] trx').

(* do post-elab terms... i.e. outputs of trx_derived *)

(* synthesize type in typesystem.v? *)
Compute lang.

(*Compute hide_term_implicits (fiat++value_subst)
   (PositiveInstantiation.egraph_simpl' (fiat++value_subst) 5 5 5 [] trx_derived).*)

Definition tr :=
  match expr_fiat_to_pyro 
    (ERecord [("a", EAtom (ABool true)); ("b", EAtom (ABool false))]) nil 
    with Success x => x | _ => {{e#""}} end.
Compute tr.
Goal wf_term (fiat++value_subst++exp_subst) [] tr {{s#"val" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" (#"cons_list_ty" #"bool" #"empty_list_ty")))}}.
Proof. t''. Qed.
  
    (*;;
       Success (hide_term_implicits (fiat++value_subst++exp_subst) tr).*)

Compute ty_fiat_to_pyro (TRecord [("a", TBool); ("b", TBool)]).
Compute expr_fiat_to_pyro (EAtom (ABool true)) nil.
(* Success {{e#"true"}} *)
Compute expr_fiat_to_pyro (EUnop ONot (EAtom (ABool true))) nil.
(* Success {{e#"notb" #"true"}} *)
Compute 
tr <- expr_fiat_to_pyro (
(EBinop OCons 
    (ERecord [("a", EAtom (ABool true)); ("b", EAtom (ABool false))])
    (EBinop OCons
      (ERecord [("a", EAtom (ABool false)); ("b", EAtom (ABool false))])
      (EAtom (ANil (Some (TRecord [("a", TBool); ("b", TBool)]))))
    )
  )
) nil ;;
  Success (hide_term_implicits (fiat++value_subst++exp_subst) tr).

(*
Fixpoint expr_pyro_to_fiat (t: term): result expr := 
  match t with
  | con s l' => l <- (all_success (map expr_pyro_to_fiat l')) ;;
                    match s, l with
                    | "true", [] => Success (EAtom (ABool true))
                    | "false", [] => Success (EAtom (ABool false))
                    | "notb", [e] => Success (EUnop ONot e)
                    | "andb", [e2;e1] => Success (EBinop OAnd e1 e2)
                    | "orb", [e2;e1] => Success (EBinop OOr e1 e2)
                    | "cons", [e2;e1] => Success (EBinop OCons e1 e2)
                    | "if", [e2;e1;cond] => Success (EIf cond e1 e2)
                    | _, _ => error:("term" t "not defined")
                    end
  | _ => error:("term" t "not defined")
  end.
*)

Fixpoint ty_pyro_to_fiat (t: term): result type :=
  match t with
  | con s l => match s, l with
               | "bool", [] => Success TBool
               | _, _ => error:("term" t "not a type")
               end
  | _ => error:("term" t "not a type")
  end.

Fixpoint env_pyro_to_fiat (t: term): result (list (string * type)) :=
  match t with
  | con s l => match s, l with
               | "emp", [] => Success ([])
               | "ext", [A;Gp] => 
                   fe <- ty_pyro_to_fiat A ;;
                   G <- env_pyro_to_fiat Gp ;;
                   Success (("idk", fe) :: G) (* TODO *)
               | _, _ => error:("term" t "not an env")
               end
  | _ => error:("term" t "not an env") 
  end.

Fixpoint expr_pyro_to_fiat (t: term): result expr := (* * list (string * type)) := *)
  match t with
  | con s l => match s, l with
               | "true", [Gp] => Success (EAtom (ABool true))
               | "false", [Gp] => Success (EAtom (ABool false))
               | "notb", [e;Gp] => 
                   fe <- expr_pyro_to_fiat e ;; 
                   Success (EUnop ONot fe)
               | "andb", [e2;e1;Gp] => 
                   fe1 <- expr_pyro_to_fiat e1 ;; 
                   fe2 <- expr_pyro_to_fiat e2 ;; 
                   Success (EBinop OAnd fe1 fe2)
               | "orb", [e2;e1;Gp] => 
                   fe1 <- expr_pyro_to_fiat e1 ;; 
                   fe2 <- expr_pyro_to_fiat e2 ;; 
                   Success (EBinop OOr fe1 fe2)
               | "cons", [e2;e1;A;Gp] => 
                   fe1 <- expr_pyro_to_fiat e1 ;; 
                   fe2 <- expr_pyro_to_fiat e2 ;; 
                   Success (EBinop OCons fe1 fe2)
               | "if", [e2;e1;A;cond;Gp] => 
                   fcond <- expr_pyro_to_fiat cond ;; 
                   fe1 <- expr_pyro_to_fiat e1 ;; 
                   fe2 <- expr_pyro_to_fiat e2 ;; 
                   Success (EIf fcond fe1 fe2)
               | _, _ => error:("term" t "not an expr")
               end
  | _ => error:("term" t "not an expr")
  end.

(*Definition tx := EIf (EAtom (ABool true)) (EAtom (ABool true)) (EAtom (ABool false)).*)
Definition tx := EBinop OOr (EAtom (ABool false)) (EAtom (ABool false)).
Definition pytx := match (expr_fiat_to_pyro tx []) with Success p => p | Failure _ => var "" end.

Compute tx.
Compute pytx.
Compute expr_pyro_to_fiat pytx.
Goal (Success tx) = (expr_pyro_to_fiat pytx). Proof. auto. Qed.

Search type_of.
Ltac inj_all := repeat (try case_match;
  match goal with
  | [H: (Success ?a) = (Success ?b) |- _] => injection H as H
  | [H: (Some ?a) = (Some ?b) |- _] => injection H as H
  | [H: ?a =? ?b = true |-_] => try rewrite String.eqb_eq in H
  | [H: ?a =? ?b = false |-_] => try rewrite String.eqb_neq in H
  | [H: ?a = ?a |-_] => clear H
  | [H: ?b = Success ?a |- _] => symmetry in H
  | [|- _] => idtac
  end; simpl in *; subst; try discriminate; auto).

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
  | [H: map.get (map.put ?m ?k ?v) ?k' = _, H': ?k <> ?k' |-_] => (erewrite map.get_put_diff in H; auto)
  | [H: map.get (map.put ?m ?k ?v) ?k' = _, H': ?k' <> ?k |-_] => (erewrite map.get_put_diff in H; auto)
end).



Opaque fiat value_subst exp_subst.

Search type_wf.

(*
Check type_wf_ind.
Theorem type_ind_full {P}:
  P TWord -> P TInt -> P TBool -> P TString -> P TUnit ->
  (forall t : type, P t -> P (TOption t)) ->
  (forall t : type, P t -> P (TList t)) ->
  (forall l : list (string * type),
                NoDup (map fst l) ->
                StronglySorted
                  (fun p p' : string * type =>
                   is_true (Value.record_entry_leb p p'))
                  l ->
                  Forall P (map snd l) -> P (TRecord l)) ->
  (forall kt vt : type,
  P kt -> P vt -> P (TDict kt vt)) ->
  (forall t : type, P t -> P (TBag t)) ->
  (forall t : type, P t -> P(TSet t)) ->
  forall t, type_wf t -> P t.
Proof.
  intros. induction H10; eauto.
  induction l.

Print type_wf.
 *)

Definition fenv_wf (Genv: list(string*type)) :=
  exists fenv (HGenv: Success fenv = fiat_env_to_map Genv),
  tenv_wf fenv.
Hint Unfold fenv_wf.

Theorem ty_fiat_to_pyro_wf:
  forall ft
  (Htwf: type_wf ft),
  forall A
  (Hty: Success A = ty_fiat_to_pyro ft),
  wf_term (fiat++value_subst++exp_subst) [] A {{s#"ty"}}.

Proof.
  intros ft _.
  induction ft using type_IH;
  intros; inj_all; t''; eauto. 
  generalize dependent a.
  induction l; intros; repeat (inj_all; t'');
  inversion H; eauto.
Qed.
Hint Resolve ty_fiat_to_pyro_wf: core.

Opaque map.put map.get.
Axiom fenv_map_ok: map.ok (SortedListString.map type). (*TODO*)
Hint Resolve fenv_map_ok.

Theorem fiat_env_to_map_contains {x}{t}{Genv}{G}:
  Success G = fiat_env_to_map ((x,t)::Genv) ->
  tenv_wf G -> map.get G x = Some t.
Proof. 
  simpl; intros; repeat (case_match; try discriminate).
  inversion H.
  eapply map.get_put_same. Unshelve. eauto.
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
  pose fenv_map_ok.
  simpl; intros; repeat (case_match; try discriminate).
  injection H0 as H0; rewrite <- H0 in *; clear H0 a.
  injection H as H; rewrite H in *; clear H G.
  destruct (string_eq_destruct x' x).
  - left; inj_all; map_simpl. inj_all.
  - right; map_simpl.
Qed.

Theorem fenv_wf_ext {G} {s} {t}:
  fenv_wf ((s,t)::G) -> fenv_wf G.
Proof.
  pose fenv_map_ok.
  intros. destruct H as [fenv [H H']]. inj_all.
  econstructor; eexists; eauto.
  unfold tenv_wf in *; intros.
  eapply H' with x0; erewrite map.get_put_diff; eauto.
  unfold "<>"; intros; subst. rewrite H in *; discriminate.
Qed.

Theorem fenv_wf__type_wf {G} {s} {t}:
  fenv_wf ((s,t)::G) -> type_wf t.
Proof.
  intros. destruct H as [fenv [H H']]. inj_all.
  eapply H' with s; eauto using map.get_put_same.
Qed.

Hint Resolve fiat_env_to_map_contains fiat_env_to_map_contents fenv_wf_ext fenv_wf__type_wf: core.

Ltac wf_term_ty := 
  lazymatch goal with
  | [H: Success ?a = ty_fiat_to_pyro ?ft ?Genv |- (wf_term _ _ ?a {{s #"ty"}})] => 
    eapply ty_fiat_to_pyro_wf; try apply H; auto
  end.

Theorem env_fiat_to_pyro_wf:
  forall Genv
  (HGenv: fenv_wf Genv),
  forall Gp (Henv: Success Gp = env_fiat_to_pyro Genv),
  wf_term (fiat++value_subst++exp_subst) [] Gp {{s#"env"}}.
Proof.
  induction Genv as [|(n,t)]; 
  intros; simpl in Henv; try solve [inversion Henv; t''].
  inj_all. t''; eauto.
Qed.
Hint Resolve env_fiat_to_pyro_wf: core.

Theorem env_fiat_to_pyro_contents_wf:
  forall Genv
  (HGenv: fenv_wf Genv),
  forall G A (Henv: Success (con "ext" [A;G]) = env_fiat_to_pyro Genv),
  wf_term (fiat++value_subst++exp_subst) [] A {{s#"ty"}} /\
  wf_term (fiat++value_subst++exp_subst) [] G {{s#"env"}}.
Proof.
  induction Genv as [|(n,t)]; intros; inj_all.
  apply conj; eauto.
Qed.

Hint Resolve env_fiat_to_pyro_contents_wf type_of__type_wf: core.

Theorem get_ind_wkn_fiat_to_pyro_wf (n:nat):
  forall Genv (HGenv: fenv_wf Genv) 
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
  induction n; intros; destruct Genv; inj_all.
  - repeat (try apply conj); t''; eauto.
    intros. destruct Genv; inj_all. repeat (try apply conj); eauto.
  - edestruct IHn with (Genv:=Genv) as [H [H' H'']]; eauto.
    repeat (try apply conj); t''; eauto.
Qed.
Hint Resolve get_ind_wkn_fiat_to_pyro_wf: core.

Theorem get_ind_fiat_to_pyro_wf (n:nat):
  forall Genv (HGenv: fenv_wf Genv) 
  Gp (Henv: Success Gp = env_fiat_to_pyro Genv),
  forall A {d} (Hty: Success A = ty_fiat_to_pyro (snd (nth n Genv d))),
  forall pt
  (Hw: Success pt = get_ind n Gp),
  wf_term (fiat++value_subst++exp_subst) [] pt (scon "val" [A;Gp]).
Proof.
  destruct n.
  - intros. destruct Genv; inj_all. t''; eauto.
  - destruct n.
    + intros. 
      pose proof get_ind_wkn_fiat_to_pyro_wf 0 HGenv Henv as H'.
      destruct Genv; inj_all; destruct Genv; inj_all; 
      eauto.
      edestruct H'; eauto. clear H'.
      destruct H0 as [Hswf Hext].
      edestruct Hext; eauto; clear Hext.
      t''; eauto.
    + intros. 
      destruct Genv; inj_all.
      assert (HGenv': fenv_wf Genv) by eauto.
      pose proof get_ind_wkn_fiat_to_pyro_wf n HGenv' as H''.
      destruct Genv; inj_all. { destruct n; inj_all. }
      eauto.
      edestruct H''; eauto. clear H''.
      destruct H0 as [Hswf Hext].
      edestruct Hext as [HGp'' [Ha Hn]]; eauto; clear Hext.
      specialize Hn with d; rewrite <- Hn in Hty; inj_all.
      t''; eauto.
Qed.
Hint Resolve get_ind_fiat_to_pyro_wf: core.

Theorem type_lookup:
  forall a x Gstore Genv {fstore} {fenv}
  (HGst: Success fstore = fiat_env_to_map Gstore) 
  (HFst: fenv_wf Gstore)
  (HGenv: Success fenv = fiat_env_to_map Genv) 
  (HFenv: fenv_wf Genv)
  (Hlookup: Success a = lookup_ind x Genv) {d},
  type_of fstore fenv (EVar x) (snd (nth a Genv d)).
Proof.
  pose fenv_map_ok.
  induction a; intros; destruct Genv; inj_all.
  - econstructor; eauto using map.get_put_same.
  - econstructor; erewrite map.get_put_diff; eauto.
    assert (H: type_of fstore a (EVar x0) (snd (nth a0 Genv d))) by eauto.
    inversion H; eauto.
Qed.
Hint Resolve type_lookup: core.

Search synthesize_expr.

Theorem fiat_type_sound:
  forall Gstore Genv {fstore} {fenv} fe ft
  (HGst: Success fstore = fiat_env_to_map Gstore) 
  (HFst: fenv_wf Gstore)
  (HGenv: Success fenv = fiat_env_to_map Genv) 
  (HFenv: fenv_wf Genv)
  (Hft: Success ft = get_fiat_type fe Genv),
  type_of fstore fenv fe ft.
Proof.
  pose fenv_map_ok.
  unfold get_fiat_type.
  intros.
  inj_all.
  destruct HFst as [fst [Hst Hst']];
  destruct HFenv as [fenv' [Henv Henv']].
  rewrite <- Hst in *.
  rewrite <- Henv in *;
  inj_all. symmetry in case_match_eqn0.
  eapply proj1.

  epose typechecker_sound.


Theorem expr_fiat_to_pyro_wf:
  forall Gstore Genv {fstore} {fenv} fe ft
  (HGst: Success fstore = fiat_env_to_map Gstore) 
  (HFst: fenv_wf Gstore)
  (HGenv: Success fenv = fiat_env_to_map Genv) 
  (HFenv: fenv_wf Genv)
  (Hty: type_of fstore fenv fe ft),
  forall pt A Gp
  (He: Success pt = expr_fiat_to_pyro fe Genv)
  (Hty: Success A = ty_fiat_to_pyro ft)
  (Henv: Success Gp = env_fiat_to_pyro Genv),
  wf_term (fiat++value_subst++exp_subst) [] pt (scon "val" [A;Gp]).
Proof.
  pose fenv_map_ok.
  induction fe; simpl; 
  unfold get_fiat_type in *; inj_all; intros;
  inversion Hty; clear Hty; invert_type_of; inj_all; try solve [t''; eauto].
  (*symmetry in case_match_eqn; 
  pose proof env_fiat_to_pyro_wf Genv HGenv HFenv case_match_eqn as HGenv_wf.*)
  - assert (Hty': type_of fstore fenv (EVar x0) (snd (nth a0 Genv ("",TUnit)))) by eauto. 
    inversion Hty'. rewrite H1 in H0.
    inj_all; eauto. (*eapply get_ind_fiat_to_pyro_wf with (Genv:=Genv)*)
  - 
    assert (type_of fstore fenv fe1 a2). {
    unfold get_fiat_type in *; inj_all.


  }
    assert (wf_term (fiat ++ value_subst ++ exp_subst) [] a0 (scon "val" [a4;a])) by eauto.
assert (wf_term (fiat ++ value_subst ++ exp_subst) [] a1 (scon "val" [a4;a])) by eauto.
    eapply IHfe1 with (Gp:=a) (pt:=a0) (ft:=t1) (A:=a4).
    t''; eauto.
    inversion Hty.
    inversion H0; clear H0;
    inj_all.
  - inversion Hty; inversion H0; inj_all. t''; eauto.
  - inversion Hty; inversion H0; inj_all. t''; eauto.
  - inversion Hty; inversion H0; inj_all. t''; eauto.
  - inversion Hty; inversion H1; inj_all. t''; eauto.
  - inversion Hty; inversion H1; inj_all.
  - inversion Hty. inversion H1; inj_all.
  - inversion Hty; inversion H0
    edestruct IHfe with (ft:=TBool); eauto. {
      inversion Hty; inversion H1; inj_all.
    }
    inj_all; eexists; t''; eauto.
    assert (type_wf t)


    destruct Genv; try discriminate.
    generalize dependent a;
    generalize dependent Genv;
    generalize dependent x0.
    destruct a0. {
      intros; inj_all.
      eexists. t''; eauto.
    }
    induction a0; intros; destruct Genv; try solve [inj_all].
    * inj_all. eexists; t''; eauto.
    * inj_all. eexists; t''; eauto.

      pose proof tenv_wf_ext HFenv case_match_eqn4 as HFenv'.
      pose proof tenv_wf_ext HFenv' case_match_eqn3 as HFenv''.
      (*
      epose proof env_fiat_to_pyro_wf Genv case_match_eqn2 HFenv'' case_match_eqn7 as H.
      epose proof ty_fiat_to_pyro_wf _ _ HFenv' _ case_match_eqn6.
      epose proof ty_fiat_to_pyro_wf _ _ HFenv _ case_match_eqn5.
       *)

      (*
      destruct (string_eq_destruct x0 s). {
        subst; assert (Ht: s=?s=true) by (rewrite String.eqb_eq; auto). simpl in case_match_eqn0; rewrite Ht in case_match_eqn0; discriminate.
      }
         inj_all; map_simpl.*)
      assert (Hlookup: lookup_ind x0 ((s0,t5)::Genv) = Success (S a4)). {
        simpl.
        assert (Ht: s0=?x0=false) by (rewrite String.eqb_neq; auto).
        rewrite Ht.
        inj_all.
      }
      edestruct IHa0 with  (fstore:=fstore); try eapply Hlookup; try eapply HFenv'; inj_all; eauto; try solve [inversion Hty; erewrite map.get_put_diff in H0; eauto; constructor; eauto].
      clear IHa0. 
      assert (wf_term (fiat ++ value_subst ++ exp_subst) [] t2 {{s #"ty"}}). {
        inversion H.
        - 

      }
        inj_all. eexists.
        t''; eauto.
      all: try solve [wf_term_ty; try apply HFenv; inj_all; eauto].
      all: try solve [wf_term_ty; try apply HFenv'; inj_all; eauto].
      all: try solve [wf_term_ty; try apply HFenv''; inj_all; eauto].
      { 


      }
      Unshelve. all: try eauto using map.get_put_same.
    
