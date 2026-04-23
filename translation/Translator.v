Set Implicit Arguments.
From fiat2 Require Import Language TypeSystem.

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

Fixpoint fiat_env_to_map (G: list (string * type)) :=
  fold_right 
    (fun x a => map.put a (fst x) (snd x))
    map.empty G.

Compute synthesize_expr (fiat_env_to_map [("a",TBool)]) _ (EAtom (ABool true)).


(* represents the kth term in Gp. 
wkn returns w and Gp', with w a substitution sending Gp to Gp' *)
Definition get_ind (n: nat) (Gp: term): result term :=
  let wkn := (fix wkn (n: nat) (Gp: term) :=
    match Gp with con "ext" [A;Gp'] =>
    match n with
    | 0 => Success (con "wkn" [A;Gp'], Gp')
    | S n => 
        '(w, Gp'') <- wkn n Gp' ;;
         Success ((con "cmp" [w; con "wkn" [A;Gp']; Gp''; Gp'; Gp]), Gp'')
    end
    | _ => error:(Gp "not a nonempty env")
    end) in
    match n with
    | 0 => match Gp with 
      | con "ext" [A;Gp'] => Success (con "hd" [A;Gp'])
      | _ => error:(Gp "not a nonempty env")
     end
    | S n => '(w, Gp') <- wkn n Gp ;; 
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

Fixpoint ty_fiat_to_pyro (ft: type) (G: list (string * type)): term :=
  match ft with
  | TBool => con "bool" []
  | TList t => con "list" [ty_fiat_to_pyro t G]
  | TRecord l => con "Trecord" [(
      fold_right 
      (fun x a => (con "cons_list_ty" [a; (ty_fiat_to_pyro (snd x) G)])) 
      (con "empty_list_ty" []) l
  )]
  | _ => {{e#""}} (*TODO*)
  end.

Definition env_fiat_to_pyro (G: list (string * type)): term :=
  fold_right 
      (fun x Gp => (con "ext" [(ty_fiat_to_pyro (snd x) G); Gp])) 
      {{e#"emp"}} G.

Compute env_fiat_to_pyro [("a", TBool); ("b", TRecord([("a",TBool)]))].

Definition get_fiat_type (e: expr) (G: list (string * type)): result type :=
  '(t,_) <- synthesize_expr map.empty (fiat_env_to_map G) e ;; Success t.

Fixpoint expr_fiat_to_pyro (fe: expr) (G: list (string * type)): result term :=
  (*(G: tenv) (fe: expr) (ft: type) (fwt: type_of G G fe ft) := *)
  let Gp := (env_fiat_to_pyro G) in 
  match fe with
  | EVar name => n <- lookup_ind name G ;; get_ind n Gp
  | EAtom fa => match fa with 
                | ABool b => match b with
                             | true => Success (con "true" [Gp])
                             | false => Success (con "false" [Gp])
                             end
                | ANil sft => match sft with 
                              | Some ft => Success (con "lempty" [ty_fiat_to_pyro ft G; Gp])
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
      let A := ty_fiat_to_pyro ty G in
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
      let A := ty_fiat_to_pyro ty G in
      Success (con "if" [e2;e1;A;cond;Gp])
  | ELet fe1 name fe2 => 
      ty_e1 <- get_fiat_type fe1 G ;;
      e1 <- expr_fiat_to_pyro fe1 G ;; 
      e2 <- expr_fiat_to_pyro fe2 ((name,ty_e1)::G) ;; 
      let A := ty_fiat_to_pyro ty_e1 G in
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
            let A := ty_fiat_to_pyro ty G in
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

(*
Derive trx_derived
  SuchThat (elab_term (fiat++value_subst) [] {{e#"false"}} trx_derived {{s#"val" #"emp" #"bool"}} )
  As trx_wf.
Proof.
  unfold trx, trx_derived.
  unshelve (repeat t); apply todo.
Qed.

Compute trx_derived.
Goal (trx = Success trx_derived). Proof. auto. Qed.
*)

Definition trx' := match (
  expr_fiat_to_pyro (
  (*
  ELet (EAtom (ABool false)) "x" (
    ELet (EAtom (ABool true)) "y" (
      EBinop OAnd (EVar "x") (EVar "y")))
   *)
  (*
  ELet (EAtom (ABool false)) "x" (
   *)
  ELet (EAtom (ABool false)) "x" (
  ELet (EAtom (ABool true)) "y" (
   EUnop ONot (EVar "x")))
  ) [])
  with Success x => x | _ => {{e#""}} end.

Compute trx'.
Compute hide_term_implicits (fiat++value_subst++exp_subst) trx'.

(*
Compute hide_term_implicits (fiat++value_subst++exp_subst)
  (PositiveInstantiation.egraph_simpl' (fiat++value_subst++exp_subst) 20 20 60 [] trx').

(* do post-elab terms... i.e. outputs of trx_derived *)

(* synthesize type in typesystem.v? *)
Compute lang.

Derive trx_derived
  SuchThat (elab_term (fiat++value_subst) [] trx trx_derived {{s#"val" #"emp" #"bool"}} )
  As trx_wf.
Proof.
  unfold trx, trx_derived.
  unshelve (repeat t); apply todo.
Qed.
Compute trx_derived.
 *)

(*Compute hide_term_implicits (fiat++value_subst)
   (PositiveInstantiation.egraph_simpl' (fiat++value_subst) 5 5 5 [] trx_derived).*)

Compute 
  tr <- expr_fiat_to_pyro 
    (ERecord [("a", EAtom (ABool true)); ("b", EAtom (ABool false))]) nil ;;
  Success (hide_term_implicits (fiat++value_subst++exp_subst) tr).

Compute ty_fiat_to_pyro (TRecord [("a", TBool); ("b", TBool)]) nil.
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

Compute tr <- expr_fiat_to_pyro (EFilter 
  LikeList 
  (EBinop OCons 
    (ERecord [("a", EAtom (ABool true)); ("b", EAtom (ABool false))])
    (EBinop OCons
      (ERecord [("a", EAtom (ABool false)); ("b", EAtom (ABool false))])
      (EAtom (ANil (Some(TRecord [("a", TBool); ("b", TBool)]))))
    )
  )
  "r"
  (EAccess (EVar "r") "a")  
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

Compute (PositiveInstantiation.egraph_simpl' (fiat++value_subst++exp_subst) 20 20 60 [] pytx).
