Set Implicit Arguments.
From fiat2 Require Import Language TypeSystem.

Require Import Datatypes.String Lists.List.
Require Import coqutil.Map.Interface.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Tools.EGraph.Automation Tools.EGraph.Defs Tools.UnElab.
Import Core.Notations.

Require Coq.derive.Derive.

Compute value_subst_def.

From Pyrosome.Lang Require Import FiatPyro.


Print expr.
Locate term.
About Term.term.
Unset Printing Notations.
Compute {{e#"true"}}.
Compute {{e#"notb" #"true"}}.
Compute (con "andb" [{{e#"true"}};{{e#"true"}}]).

Search "if".

Fixpoint lookup_ind {T} (name: string) (rec: list (string * T)) :=
  match rec with
  | (name', _) :: rec' => if (name' =? name) then (Some 0) else 
      (match lookup_ind name rec' with
       | Some n => Some (S n)
       | None => None
       end)
  | nil => None
  end.

Fixpoint lookup (name: string) (rec: list (string * type)) :=
  match rec with
  | (name', val) :: rec' => 
      if (name' =? name) then (Some val) else (lookup name rec')
  | nil => None
  end.

Compute fold_right.

Fixpoint ty_fiat_to_pyro (ft: type) :=
  match ft with
  | TBool => {{e#"bool"}}
  | TList t => con "list" [ty_fiat_to_pyro t]
  | TRecord l => con "Trecord" [(
      fold_right 
      (fun x a => (con "cons_list_ty" [(ty_fiat_to_pyro (snd x)); a])) 
      {{e#"empty_list_ty"}} l
  )]
  | _ => {{e#""}} (*TODO*)
  end.

Fixpoint get_ind (n: nat) :=
  let wkn := (fix wkn (n: nat) :=
    match n with
    | 0 => {{e#"wkn"}}
    | S n => con "cmp" [{{e#"wkn"}}; wkn n]
    end) in
  match n with
  | 0 => {{e#"hd"}}
  | S n => con "val_subst" [{{e#"hd"}}; wkn n]
  end.

(*
Compute type_of.
Locate map.map.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
 *)

Fixpoint fiat_to_pyro (fe: expr) (G: list (string * option unit)) :=
  (*(G: tenv) (fe: expr) (ft: type) (fwt: type_of G G fe ft) := *)
  match fe with
  | EVar name => match lookup_ind name G with
                     | Some n => Some (get_ind n)
                     | None => None
                     end
  | EAtom fa => match fa with 
                | ABool b => match b with
                             | true => Some {{e#"true"}}
                             | false => Some {{e#"false"}}
                             end
                | ANil sft => match sft with 
                              | Some ft => Some (con "lempty" [ty_fiat_to_pyro ft])
                              | None => None
                              end
                | _ => None
                end
  | EUnop op fe => match (fiat_to_pyro fe G) with
                   | Some e =>
                       match op with
                       | ONot => Some (con "notb" [e]) 
                       | OLength => Some (con "length" [e])
                       | _ => None
                       end
                   | _ => None
                   end
  | EBinop op fe1 fe2 => match 
      fiat_to_pyro fe1 G,
      fiat_to_pyro fe2 G with
                         | Some e1, Some e2 =>
                             match op with
                             | OAnd => Some (con "andb" [e2;e1])
                             | OOr => Some (con "orb" [e2;e1])
                             | _ => None
                             end
                         | _,_ => None
                         end
  | EIf fcond fe1 fe2 => match 
      fiat_to_pyro fcond G,
      fiat_to_pyro fe1 G,
      fiat_to_pyro fe2 G with
                         | Some cond, Some e1, Some e2 => 
                             Some (con "if" [e2;e1;cond])
                         | _,_,_ => None
                         end
  | ELet fe1 name fe2 => match fiat_to_pyro fe1 G, fiat_to_pyro fe2 ((name,None)::G) with
                         | Some e1, Some e2 =>
                             Some (con "val_subst" [e2;(con "snoc" [e1;{{e#"id"}}])])
                         | _,_ => None
                         end
  | ERecord gl => match (fold_right 
      (fun x a => match fiat_to_pyro (snd x) G, a with
                  | Some x', Some a' => Some (con "cons" [a';x'])
                  | _,_ => None 
                  end) 
                  (Some {{e#"empty_record"}}) gl) with
                  | Some l => Some (con "Trecord" [l])
                  | None => None
                  end
  | EFilter tag ftb name fp =>
      (* note name is the bound variable for the record in fp *)
      match fiat_to_pyro ftb G, fiat_to_pyro fp ((name,None) :: G) with
      | Some tb, Some p => Some (con "filter" [(con "val_subst" [p]);tb])
      | _,_ => None
      end
  | EJoin tag fl1 fl2 name1 name2 fp fr =>
      (* TODO strings *)
      match 
      fiat_to_pyro fl1 G, 
      fiat_to_pyro fl2 G, 
      fiat_to_pyro fp G, 
      fiat_to_pyro fr G with
      | Some tb1, Some tb2, Some p, Some r =>
          Some (con "join" [r;p;tb2;tb1])
      | _,_,_,_ => None
      end
  | EProj tag fl name fr =>
      (* TODO strings *)
      match fiat_to_pyro fl G, fiat_to_pyro fr G with
      | Some tb, Some r => Some (con "proj" [r;tb])
      | _,_ => None
      end
  | _ => None
  end.

Definition trx := match (
  fiat_to_pyro (
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
  with Some x => x | _ => {{e#""}} end.

Compute trx.

Derive trx_derived
  SuchThat (elab_term (fiat++value_subst) [] trx trx_derived {{s#"val" #"emp" #"bool"}} )
  As trx_wf.
Proof.
  unfold trx, trx_derived.
  unshelve (repeat t); apply todo.
Qed.
Compute trx_derived.

Compute hide_term_implicits (fiat++value_subst)
  (PositiveInstantiation.egraph_simpl' (fiat++value_subst) 5 5 5 [] trx_derived).

Compute fiat_to_pyro (EAtom (ABool true)).
(* Some {{e#"true"}} *)
Compute fiat_to_pyro (EUnop ONot (EAtom (ABool true))).
(* Some {{e#"notb" #"true"}} *)

Definition U := EAtom AUnit.

Fixpoint only_if_all {T} (l: list (option T)) :=
  match l with
  | h :: l' => match h, (only_if_all l') with
               | Some h', Some l' => Some (h'::l')
               | _,_ => None
               end
  | nil => Some nil
  end.

Fixpoint pyro_to_fiat (t: term): option expr := 
  match t with
  | con s l' => match (only_if_all (map pyro_to_fiat l')) with
                | Some l =>
                    match s, l with
                    | "true", [] => Some (EAtom (ABool true))
                    | "false", [] => Some (EAtom (ABool false))
                    | "notb", [e] => Some (EUnop ONot e)
                    | "andb", [e2;e1] => Some (EBinop OAnd e1 e2)
                    | "orb", [e2;e1] => Some (EBinop OOr e1 e2)
                    | "if", [e2;e1;cond] => Some (EIf cond e1 e2)
                    | _, _ => None
                    end
                | None => None
                end
  | _ => None
  end.

Definition tx := EIf (EAtom (ABool true)) (EAtom (ABool true)) (EAtom (ABool false)).
Definition pytx := match (fiat_to_pyro tx []) with
                   | Some p => p
                   | None => var ""
                   end.
Compute tx.
Compute pytx.
Compute pyro_to_fiat pytx.


