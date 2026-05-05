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

Definition fiat_rules := fiat ++ value_subst ++ exp_subst.


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

Definition make_list_ty (l: list term): result term :=
      fold_right 
      (fun x a' => a <- a' ;; 
      Success (con "cons_list_ty" [a; x]))
      (Success {{e#"empty_list_ty"}}) l.

Fixpoint ty_fiat_to_pyro (ft: type): result term :=
  match ft with
  | TBool => Success {{e#"bool"}}
  | TList t => tl <- ty_fiat_to_pyro t ;; Success (con "list" [tl])
  | TRecord l => l <- all_success (
      map (fun x => ty <- ty_fiat_to_pyro (snd x) ;; Success (fst x, ty)) l) ;; 
      lty <- make_list_ty (map snd (record_sort l)) ;; Success (con "Trecord" [lty])
  | _ => error:("fiat type" ft "not supported")
  end.

Definition ty_list_fiat_to_pyro (l: list (string * type)): result term :=
      l <- all_success (
      map (fun x => ty <- ty_fiat_to_pyro (snd x) ;; Success (fst x, ty)) l) ;;
      make_list_ty (map snd (record_sort l)).

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
  | EAccess fe name =>
      rec <- expr_fiat_to_pyro fe Genv Gstore ;; (* as a list! *)
      ty <- get_fiat_type fe Genv Gstore ;;
      match ty with TRecord tl =>
        lty <- (ty_list_fiat_to_pyro tl) ;;
        n <- (lookup_ind name tl) ;; (
        (fix get (n: nat) (tl: list (string * type)) (rec:term) := match tl with 
                                         | (_,ft) :: tl' =>
                                             A <- ty_fiat_to_pyro ft ;;
                                             lty' <- ty_list_fiat_to_pyro tl' ;;
                                             match n with 
                                             | 0 => Success (con "car" [rec;lty';A;Gp]) 
                                             | S n => get n tl' (con "cdr" [rec;lty';A;Gp])
                                             end 
                                         | [] => error:("list is incorrectly empty") 
                                         end) n tl rec)
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
  SuchThat (elab_term fiat_rules [] {{e#"cons" #"false" (#"lempty" #"bool")}} trx_derived {{s#"val" #"emp" (#"list" #"bool")}} )
  As trx_wf.
Proof. t''. Qed.
Print trx_derived.  Print trx_wf.

Goal wf_term (fiat_rules) [] {{e#"true" #"emp"}} {{s#"val" #"emp" #"bool"}}.
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

Goal wf_term (fiat_rules) [] trx' {{s#"val" #"emp" #"bool"}}.
Proof.  t''.  Qed.

Compute hide_term_implicits (fiat_rules) trx'.

Compute hide_term_implicits (fiat_rules)
  (PositiveInstantiation.egraph_simpl' (fiat_rules) 20 20 60 [] trx').

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
Goal wf_term (fiat_rules) [] tr {{s#"val" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" (#"cons_list_ty" #"bool" #"empty_list_ty")))}}.
Proof. t''. Qed.
  
    (*;;
       Success (hide_term_implicits (fiat_rules) tr).*)

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
  Success (hide_term_implicits (fiat_rules) tr).

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
