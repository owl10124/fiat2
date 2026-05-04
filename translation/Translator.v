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

Locate dlist.
Require Import Stdlib.FSets.FMapInterface.
Require Import Stdlib.ZArith.ZArith.

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
Definition record_sort {T} := Mergesort.Sectioned.sort (
  fun (a b:(string*T)) => (Value.record_entry_leb a b)
).
 *)

Definition x := {{e #"ext" (#"ext" #"emp" #"bool") #"bool"}}.
Print x.

Require coqutil.Map.SortedListString.
Local Existing Instance SortedListString.map.
Local Existing Instance SortedListString.ok.
Local Existing Instance SortedListString.Build_parameters.

Fixpoint fiat_env_to_map (G: list (string * type)) :=
match G with
  | nil => Success map.empty
  | (n,t)::G' => 
Gm<- fiat_env_to_map G' ;; 
      match map.get Gm n with None => Success (map.put Gm n t) | Some _ => error:("key" n "already in" G) end
  end.

(*
  fold_right 
    (fun x a => map.put a (fst x) (snd x))
    map.empty G.
 *)

Compute fenv <- fiat_env_to_map [("a",TBool)] ;; synthesize_expr fenv _ (EAtom (ABool true)).

(*wkn returns w and Gp', with w a substitution sending Gp to Gp'. essentially weakens n times *)
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
  | TRecord l => (l <- all_success (
      map (fun x => ty <- ty_fiat_to_pyro (snd x) ;; Success (fst x, ty)) l) ;;
      rec_list <- (fold_right 
      (fun x a' => a <- a' ;; 
      Success (con "cons_list_ty" [a; snd x])) 
      (Success {{e#"empty_list_ty"}}) (record_sort l)) ;; Success (con "Trecord" [rec_list]))
  | _ => error:("fiat type" ft "not supported")
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

Definition get_fiat_type (e: expr) (Genv: list (string * type)) (Gstore: list (string * type)): result type :=
  fenv <- fiat_env_to_map Genv ;;
  fstore <- fiat_env_to_map Gstore ;;
  '(t,_) <- synthesize_expr fstore fenv e ;; Success t.

Fixpoint expr_fiat_to_pyro (fe: expr) (Genv: list (string * type)) (Gstore: list (string * type)): result term :=
  (*(G: tenv) (fe: expr) (ft: type) (fwt: type_of G G fe ft) := *)
  Gp <- env_fiat_to_pyro Genv ;;
  match fe with
  | EVar name => n <- lookup_ind name Genv ;; get_ind n Gp
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
      e <- expr_fiat_to_pyro fe Genv Gstore ;;
                       match op with
                       | ONot => Success (con "notb" [e; Gp]) 
                       | OLength => Success (con "length" [e; Gp])
                       | _ => error:("unop" op "not defined yet")
                       end
  | EBinop op fe1 fe2 => 
      e1 <- expr_fiat_to_pyro fe1 Genv Gstore ;; 
      e2 <- expr_fiat_to_pyro fe2 Genv Gstore ;;
      ty <- get_fiat_type fe1 Genv Gstore ;;
      A <- ty_fiat_to_pyro ty ;;
                             match op with
                             | OAnd => Success (con "andb" [e2;e1;Gp])
                             | OOr => Success (con "orb" [e2;e1;Gp])
                             | OCons => Success (con "cons" [e2;e1;A;Gp])
                             | _ => error:("binop" op "not defined yet")
                             end
  | EIf fcond fe1 fe2 => 
      cond <- expr_fiat_to_pyro fcond Genv Gstore ;;
      e1 <- expr_fiat_to_pyro fe1 Genv Gstore ;;
      e2 <- expr_fiat_to_pyro fe2 Genv Gstore ;;
      ty <- get_fiat_type fe1 Genv Gstore ;;
      A <- ty_fiat_to_pyro ty ;;
      Success (con "if" [e2;e1;A;cond;Gp])
  | ELet fe1 name fe2 => 
      ty_e1 <- get_fiat_type fe1 Genv Gstore ;;
      ty_e2 <- get_fiat_type fe2 ((name,ty_e1)::Genv) Gstore ;; 
      e1 <- expr_fiat_to_pyro fe1 Genv Gstore ;; 
      e2 <- expr_fiat_to_pyro fe2 ((name,ty_e1)::Genv) Gstore ;; 
      A <- ty_fiat_to_pyro ty_e1 ;;
      A' <- ty_fiat_to_pyro ty_e2 ;;
      match (lookup_ind name Genv) with Success n => error:("TODO can't handle remappings")
      | _ =>
      Success (con "val_subst" [
        e2;
        A';
        (con "snoc" [e1; A; (con "id" [Gp]); Gp; Gp]);
        (con "ext" [A;Gp]);
        Gp
      ])
      end
  | ERecord gl => 
      l <- (all_success (map (fun (p:string*expr) => (
        v <- expr_fiat_to_pyro (snd p) Genv Gstore ;;
        ty <- get_fiat_type (snd p) Genv Gstore ;; 
        A <- ty_fiat_to_pyro ty ;;
        Success (fst p, (v, A))))
      gl)) ;;
      '(rec,_) <- (fix build_rec (l: list (string*(term*term))) (Gp: term) :=
        match l with
        | nil => Success (con "empty_record" [Gp], con "empty_list_ty" [])
        | (_,(v,A)) :: l' => 
            '(l, lty) <- build_rec l' Gp ;;
            Success (con "cons_record" [l;v;lty;A;Gp], con "cons_list_ty" [lty;A])
        end
        ) (record_sort l) Gp ;; Success rec
      (*
      '(rec,_) <- (fix build_rec (gl: list(string * expr)) (Gp: term) :=
        match gl with
        | nil => Success (con "empty_record" [Gp], con "empty_list_ty" [])
        | (name, expr) :: gl' => 
            v <- expr_fiat_to_pyro expr Genv Gstore ;;
            ty <- get_fiat_type expr Genv Gstore ;;
            A <- ty_fiat_to_pyro ty ;;
            '(l, lty) <- build_rec gl' Gp ;;
            Success (con "cons_record" [l;v;lty;A;Gp], con "cons_list_ty" [lty;A])
        end
      ) gl Gp ;; Success rec (* TODO elab works up to here... *)
         *)
  | EAccess fe name =>
      rec <- expr_fiat_to_pyro fe Genv Gstore ;; (* as a list! *)
      ty <- get_fiat_type fe Genv Gstore ;;
      A <- ty_fiat_to_pyro ty ;;
      match ty with TRecord tl =>
      n <- (lookup_ind name tl) ;; Success ((fix get (n: nat) := match n with
                                               | 0 => (con "car" [rec;A;Gp])
                                               | S n => (con "cdr" [get n;A;Gp])
                                               end) n)
      | _ => error:("eaccess argument " fe "of incorrect type" ty)
      end
      (*
  | EFilter tag ftb name fp =>
      (* note name is the bound variable for the record in fp *)
      ty_tb <- get_fiat_type ftb Genv Gstore ;;
      match ty_tb with TList ty_rec =>
      tb <- expr_fiat_to_pyro ftb Genv Gstore ;; 
      p <- expr_fiat_to_pyro fp ((name, ty_rec) :: Genv) Gstore ;;
      Success (con "filter" [Gp;(con "val_subst" [p]);tb])
      | _ => error:("table" ftb "of type" ty_tb "not a list of records") end
  | EJoin tag fl1 fl2 name1 name2 fp fr =>
      (* TODO strings *)
      tb1 <- expr_fiat_to_pyro fl1 Genv Gstore ;;
      tb2 <- expr_fiat_to_pyro fl2 Genv Gstore ;;
      p <- expr_fiat_to_pyro fp Genv Gstore ;;
      r <- expr_fiat_to_pyro fr Genv Gstore ;;
        Success (con "join" [r;p;tb2;tb1;Gp])
  | EProj tag fl name fr =>
      (* TODO strings *)
      tb <- expr_fiat_to_pyro fl Genv Gstore ;; 
      r <- expr_fiat_to_pyro fr Genv Gstore ;;
      Success (con "proj" [r;tb;Gp])
       *)
  | _ => error:("term" fe "not defined")
  end.

Definition trx := expr_fiat_to_pyro (EAtom (ABool false)) [] [].

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
  ) [] [])
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
    (ERecord [("a", EAtom (ABool true)); ("b", EAtom (ABool false))]) [] []
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
) [] [] ;;
  Success (hide_term_implicits (fiat++value_subst++exp_subst) tr).

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
                   Success ((of_nat (length G), fe) :: G) (* TODO *)
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
Definition pytx := match (expr_fiat_to_pyro tx [] []) with Success p => p | Failure _ => var "" end.

Compute tx.
Compute pytx.
Compute expr_pyro_to_fiat pytx.
Goal (Success tx) = (expr_pyro_to_fiat pytx). Proof. auto. Qed.

Search type_of.
Ltac inj_all := repeat (try case_match;
  match goal with
  | [H: (Success ?a) = (Success ?b) |- _] => injection H as H
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

Opaque fiat value_subst exp_subst.

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
  destruct (string_eq_destruct x0 s); repeat (inj_all; map_simpl; equality).
  eapply H0 with x0; map_simpl.
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
Search StronglySorted.

Locate Permutation.Permutation.
Require Import Stdlib.Sorting.Permutation.

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
    specialize H1 with x0 (snd (nth a Genv d)) d; inj_all.
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
  destruct (string_eq_destruct x0 x1); repeat (inj_all; map_simpl); eauto.
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
    generalize H H3 case_match_eqn case_match_eqn0. clear.
    generalize dependent a0.
    generalize dependent a.
    induction l; intros; destruct a; invert_cons; repeat (inj_all; t'').
Qed.
Hint Resolve ty_fiat_to_pyro_wf: core.



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

    all: assert ((map fst x0 = map fst l') /\ StronglySorted (fun p p' => is_true (record_entry_leb p p')) x0) by (
        generalize case_match_eqn0 Hsl;
        clear; 
        unfold f, record_entry_leb in *;
        generalize dependent x0;
        induction l'; intros; destruct x0; invert_cons;
        constructor; inj_all;
        assert (Hfst: Forall (fun n => is_true (s <=? n)) (map fst l')) by (rewrite Forall_map; eauto);
        rewrite <- H in Hfst; rewrite Forall_map in Hfst; eauto
      ); equality.

    all: set (n := map fst l) in *; set (n' := map fst l') in *; inj_all;
    assert (Hpll': Permutation n n') by (unfold n, n'; eauto with permute).

    all: assert (Hrs: x0 = record_sort x0 /\ x0 = record_sort a1) by
      (apply conj; apply sorted_perm_eq; gather n'; gather n; eauto with permute).
    all: destruct Hrs as [Hrs Hrs']; rewrite <- Hrs in *; rewrite <- Hrs' in *; equality.
    replace (record_sort tl) with tl' in * by (eapply record_sort_iff_sorted; eauto with permute).

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

    repeat (apply conj; eauto).
    - apply Forall2_map_right with (f:=snd); apply Forall2_map_left with (f:=snd); eauto.
    - eapply Permutation_Forall with l; eauto.
      generalize case_match_eqn2; clear; generalize dependent a1; unfold f.
      induction l; intros; destruct a1; invert_cons.
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
    eapply IHfe2 with (Genv := (x0,t0)::Genv); eauto.
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


      assert ((map fst x0 = map fst l') /\ StronglySorted (fun p p' => is_true (record_entry_leb p p')) x0). {
        clear Hpl. clear dependent a0. subst n n'; clear Hpll'.
        generalize dependent x0.
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

    assert (Hrec: x0 = a'). { 
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
    gather x0; gather l'; gather tl'; gather tl0'.
    clear dependent l.
    clear dependent a0. 
    clear dependent tl. 
    clear dependent tl0. 
    rename x0 into a0'.
    
     *)
     *)
    
    assert (Hpy: Forall 
      (fun p => exists pt, Success pt = expr_fiat_to_pyro (snd p) Genv Gstore)  
      l'). { 
        subst n n'; clear Hpll'.
        gather x0. clear dependent a0.
        generalize dependent t.
        generalize dependent t0.
        generalize dependent x0.
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
        clear dependent x0.
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
Ltac inj_types := repeat (
  match goal with
  | [Hty: type_of ?fstore ?fenv ?fe ?ft, Hty': type_of ?fstore ?fenv ?fe ?ft' |-_] =>
      assert (ft=ft') by eauto
  end; inj_all); inj_all.

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
    assert (Hty': type_of fstore fenv (EVar x0) (snd (nth a0 Genv d0))). {
      eapply type_lookup; eauto.
    }
    inversion Hty'; equality.
  - (* cons *)
    assert (a3=t1) by eauto; equality.
    assert (type_wf t1) by (apply type_of__type_wf in H8; eauto).
    assert (Success (con "list" [a0]) = ty_fiat_to_pyro (TList t1)) by inj_all.
    t''; eauto.
  - (* if *)
    assert (a3=ft) by eauto; equality.
    assert (type_wf ft) by (apply type_of__type_wf in H8; eauto).
    t''; eauto.
  - (* let *)
    assert (a0=t1) by eauto; equality.
    assert (type_wf t1) by (apply type_of__type_wf in H7; eauto).
    eapply lookup_fmap_none with (fenv:=fenv) in case_match_eqn6; eauto.
    specialize (fenv_wf_cons HFenv) as Hewf.
    edestruct Hewf with (x:=x0) (a:=t1); eauto.
    assert (a1=ft) by eauto; equality.
    assert (type_wf ft) by (apply type_of__type_wf in H8; eauto).

    assert (pyro_expr_wf a3 A (con "ext" [a4;a])). {
      eapply IHfe2 with (Gstore:=Gstore) (Genv:=(x0,t1)::Genv); eauto.
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

    assert (Hfst: map fst tl' = map fst a1) by (
      generalize case_match_eqn1; clear; generalize dependent a1; induction tl'; intros; destruct a1; 
        invert_cons
    ).
    pose proof (fst_equal_equiv tl' a1).
    assert (NoDup (map fst tl')) by eauto with permute.

    assert (Ha1: a1 = record_sort a1) by (
    rewrite record_sort_iff_sorted; repeat apply conj; try eapply fst_equal_equiv; eauto with permute).
    rewrite <- Ha1 in *.

    assert (Hfsta: map fst l' = map fst a) by (
        generalize case_match_eqn; clear; generalize dependent a; induction l'; intros; destruct a; 
        invert_cons
    ).
    pose proof (fst_equal_equiv l' a).
       remember (map fst l') as n' in *.
      assert (NoDup n') by (gather n'; eauto with permute).

      assert (Ha: a = record_sort a) by (
      gather n'; inj_all;
      rewrite record_sort_iff_sorted; repeat apply conj; try eapply fst_equal_equiv; eauto with permute).
      rewrite <- Ha in *.

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

    assert ((pyro_expr_wf t1 (con "Trecord" [a2]) a3 /\ 
    Success (con "Trecord" [a2]) = ty_fiat_to_pyro (TRecord tl')) /\
    wf_term (fiat++value_subst++exp_subst) [] a2 (scon "list_ty" []) /\
    t2 = a2
    ). {
      unfold pyro_expr_wf in *. inj_all.
      all: replace (record_sort a0) with a0 in * by (
      rewrite record_sort_iff_sorted; repeat apply conj; try eapply fst_equal_equiv; eauto with permute).
      all: equality.
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

      induction l'; intros; destruct tl'; destruct a; destruct a1; invert_cons; 
      try solve [repeat (apply conj); t''; eauto].
      edestruct IHl'; eauto; clear IHl'; inj_all.
      - apply record_sort_iff_sorted; eauto.
      - assert (a4=t1) by eauto. equality.
        clear Heq; equality.
      assert (type_wf t1). {
        destruct HFst, HFenv.
        eapply type_of__type_wf with (Gstore:=fstore) (Genv:=fenv); eauto.
      }
      equality.
      repeat apply conj; t''; eauto.
    }
    inj_all.
  - 
    match goal with [H: _ = get_fiat_type _ _ _ |-_] => eapply fiat_type_sound with (fstore:=fstore) (fenv:=fenv) in H end; eauto.
    assert (Htr: TRecord l = TRecord tl) by eauto. inversion Htr; inj_all.
    assert (Hrec: Success (con "Trecord" [a4]) = ty_fiat_to_pyro (TRecord tl)) by inj_all.
    specialize (ty_fiat_to_pyro_wf) with (ft:=TRecord tl) as Hrec'.
    equality. 

    assert (Htwf: type_wf (TRecord tl)). {
      eapply type_of__type_wf; try eapply H5; eauto.
    }
    inversion Htwf; inj_all.
    assert (map fst tl = map fst a2). {
      generalize case_match_eqn2. 
      clear. generalize dependent a2.
      induction tl; intros; destruct a2; invert_cons.
    }
    assert (Ha2: a2 = record_sort a2). {
      apply record_sort_iff_sorted; inj_all.
      apply conj; eauto with permute.
      eapply fst_equal_equiv; eauto.
    }
    rewrite <- Ha2 in *. equality. clear Ha2.
    clear case_match_eqn1.
    clear H5.
    clear Htwf.
    clear Hrec'.
    match goal with [|-?g] => enough (g /\ 
    wf_term fiat_rules [] a3 (scon "list_ty" [])
    ) by (inj_all; eauto) end.
    generalize dependent a2.
    generalize dependent a3.
    generalize dependent ft.
    generalize dependent A.
    generalize dependent fe.
    generalize dependent a0.
    generalize dependent s.
    generalize dependent tl.
    generalize dependent a1.
Admitted.
(*
    induction a1; induction tl; intros.
     * destruct a2; destruct a3; invert_cons.
     * destruct a2; invert_cons; equality.
       + clear IHtl.
         apply conj. {
         t''; eauto.
       }
     * 
     * t''; eauto.


    (*
    assert (wf_term (fiat++value_subst++exp_subst) [] a3 (scon "list_ty" [])). {
      remember (record_sort a2) as a2'. 
      clear Hrec'.
      generalize dependent tl.
      generalize dependent a3. subst a2'.
      induction a2; intros; destruct a3; invert_cons; try solve [t''; eauto].
      - t''. 
        
                }
    assert (Hrec: pyro_expr_wf a0 (con "Trecord" [a3]) a). {
      eapply IHfe with (Gstore:=Gstore) (Genv:=Genv);
      inj_all.
       }*)
    
    generalize dependent s.
    generalize dependent tl.
    induction a1; intros; inj_all.
     * destruct tl; invert_cons.
       + t''; eauto.
     * t''; eauto; inj_all.
Qed.
 *)

Theorem fenv_wf_nil:
  fenv_wf [] map.empty.
Proof.
  unfold fenv_wf in *; apply conj; inj_all.
Qed.
Hint Resolve fenv_wf_nil: core.

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


