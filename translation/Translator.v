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
Require Import Tactics.

Section WithMap.
  Context {locals: forall T, map.map string T} {locals_ok: forall T, map.ok (locals T)}.
  Definition tenv := locals type.
  Definition lenv := (list (string * type)).

  Definition fiat_rules := fiat ++ exp_subst ++ value_subst.

  Definition pyro_expr_wf (pexpr: term) (pty: term) (penv: term) :=
    wf_term fiat_rules [] pexpr (scon "val" [pty;penv]).

  Compute {{e#"true"}}.
  Compute {{e#"notb" #"true"}}.
  Compute (con "andb" [{{e#"true"}};{{e#"true"}}]).

  Fixpoint lookup_ind {T} (name: string) (rec: list (string * T)) :=
    match rec with
    | (name', _) :: rec' => if (name' =? name) then (Success 0) else 
        n <- lookup_ind name rec' ;; Success (S n)
    | nil => error:("var" name "not found in env")
    end.

  Definition x := {{e #"ext" (#"ext" #"emp" #"bool") #"bool"}}.
  Print x.

  Fixpoint fiat_env_to_map (G: lenv): result tenv :=
    match G with
    | nil => Success (map.empty)
    | (n,t)::G' => Gm <- fiat_env_to_map G' ;; 
        match map.get Gm n with None => Success (map.put Gm n t) | Some _ => error:("key" n "already in" G) end
    end.

  Opaque locals.
  Hint Rewrite (map.get_put_diff (map:=tenv)): core.
  Hint Rewrite (map.get_put_same (map:=tenv)): core.
  Hint Rewrite (map.get_empty (map:=tenv)): core.

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

  Hint Unfold ty_fiat_to_pyro ty_list_fiat_to_pyro: core.

  Fixpoint env_fiat_to_pyro (G: list (string * type)): result term :=
    match G with
    | [] => Success {{e#"emp"}}
    | (_,x)::G' => 
        A <- ty_fiat_to_pyro x ;;
        Gp <- env_fiat_to_pyro G' ;;
        Success (con "ext" [A;Gp])
    end.

  Compute env_fiat_to_pyro [("a", TBool); ("b", TRecord([("a",TBool)]))].

  Definition get_fiat_type (e: expr) (Genv: list (string * type)) (Gstore: list (string * type)): result type :=
    fenv <- fiat_env_to_map Genv ;;
    fstore <- fiat_env_to_map Gstore ;;
    '(t,_) <- synthesize_expr fstore fenv e ;; Success t.

  Fixpoint expr_fiat_to_pyro (fe: expr) (Genv: lenv) (Gstore: lenv): result term :=
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
                              | Some ft => A <- ty_fiat_to_pyro ft ;;
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
  | EFilter tag ftb name fp =>
      (* note name is the bound variable for the record in fp *)
      match (lookup_ind name Genv) with Success n => error:("variable" name "bound in" Genv)
      | _ =>
      ty_tb <- get_fiat_type ftb Genv Gstore ;;
      match ty_tb with TList ty_rec =>
      t <- ty_fiat_to_pyro ty_rec ;;
      tb <- expr_fiat_to_pyro ftb Genv Gstore ;; 
      p <- expr_fiat_to_pyro fp ((name, ty_rec) :: Genv) Gstore ;;
      Success (con "filter" [p;tb;t;Gp])
      | _ => error:("table" ftb "of type" ty_tb "not a list of records") end
      end
  | EJoin tag ftb1 ftb2 name1 name2 fp fr =>
      ftl1 <- get_fiat_type ftb1 Genv Gstore ;;
      ftl2 <- get_fiat_type ftb2 Genv Gstore ;;
      match ftl1 with TList ft1 =>
      match ftl2 with TList ft2 =>
      match (lookup_ind name1 Genv) with Success n => error:("variable" name1 "bound in" Genv) 
      | _=>
      match (lookup_ind name2 ((name1,ft1)::Genv)) with Success n => error:("variable" name2 "bound in" Genv)
      | _ =>
      ft3 <- get_fiat_type fr ((name2,ft2)::(name1,ft1)::Genv) Gstore ;;
      t1 <- ty_fiat_to_pyro ft1 ;;
      t2 <- ty_fiat_to_pyro ft2 ;;
      t3 <- ty_fiat_to_pyro ft3 ;;
      tb1 <- expr_fiat_to_pyro ftb1 Genv Gstore ;;
      tb2 <- expr_fiat_to_pyro ftb2 Genv Gstore ;;
      p <- expr_fiat_to_pyro fp ((name2,ft2)::(name1,ft1)::Genv) Gstore ;;
      r <- expr_fiat_to_pyro fr ((name2,ft2)::(name1,ft1)::Genv) Gstore ;;
        Success (con "join" [r;p;tb2;tb1;t3;t2;t1;Gp])
      end end
      | _ => error:("table" ftb2 "of type" ftl2 "not a list of records") end
      | _ => error:("table" ftb1 "of type" ftl1 "not a list of records") end
  | EProj tag fl name fr =>
      tb <- expr_fiat_to_pyro fl Genv Gstore ;; 
      ty_tb <- get_fiat_type fl Genv Gstore ;;
      match ty_tb with TList ty_rec =>
      t1 <- ty_fiat_to_pyro ty_rec ;;
      match (lookup_ind name Genv) with Success n => error:("variable" name "bound in" Genv) 
      | _ =>
      ft2 <- get_fiat_type fr ((name,ty_rec)::Genv) Gstore ;;
      t2 <- ty_fiat_to_pyro ft2 ;;
      r <- expr_fiat_to_pyro fr ((name,ty_rec)::Genv) Gstore ;;
      Success (con "proj" [r;tb;t2;t1;Gp]) end
      | _ => error:("table" fl "of type" ty_tb "not a list of records") end
  | _ => error:("term" fe "not defined")
  end.
  Hint Unfold expr_fiat_to_pyro: core.

  Definition trx := expr_fiat_to_pyro (EAtom (ABool false)) [] [].

  Compute trx.

  (* do post-elab terms... i.e. outputs of trx_derived *)

  (* synthesize type in typesystem.v? *)
  Compute lang.

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

  (* do post-elab terms... i.e. outputs of trx_derived *)

  (* synthesize type in typesystem.v? *)

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

  Fixpoint name_nat (x: nat): string :=
    match x with 0 => "" | S n => " " ++ name_nat n end.

  Definition name_list_ty {T} (l: list T): list (string * T) :=
    (fix f (l: list T) (n: nat) := match l with
                                   | [] => []
                                   | x::l => ((name_nat n), x) :: (f l (S n))
                                   end) l 0.

  Require Import Psatz.

  Lemma name_nat_leb: forall m n,
    (n <= m -> is_true ((name_nat n) <=? (name_nat m))).
  Proof.
    induction m; destruct n; intros; try lia; inj_all.
    assert (n<=m) by lia;
    specialize IHm with n; inj_all.
  Qed.
  Lemma name_nat_inj: forall n m,
    name_nat n = name_nat m -> n = m.
  Proof.
    induction n; destruct m; intros; try lia; inj_all.
    inversion H; inj_all.
  Qed.
  Hint Resolve name_nat_inj name_nat_leb: core.
  Opaque name_nat.

  Lemma name_list_ty_ok: forall {A} l,
    let fl := name_list_ty l in
    StronglySorted (fun p p' : string * A => is_true (record_entry_leb p p')) fl /\
    NoDup (map fst fl) /\
    l = map snd fl.
  Proof.
    intro A.
    set (f := (fix f (l: list A) (n: nat) := match l with
                                             | [] => []
                                             | x::l => ((name_nat n), x) :: (f l (S n))
                                             end)
    ). 
    enough (forall l n,
    StronglySorted (fun p p' : string * A => is_true (record_entry_leb p p')) (f l n) /\
    NoDup (map fst (f l n)) /\
    (forall m a, n<m -> 
    Forall (fun p' : string * A => is_true (record_entry_leb (name_nat n, a) p')) (f l m) /\
    ~In (name_nat n) (map fst (f l m))) /\
    l = map snd (f l n)) by (unfold name_list_ty in *; intros; specialize H with l 0; inj_all).

    induction l; intros; intuition; invert_cons; equality; try constructor; 
    inj_all.
    all: try solve [specialize IHl with (S n); inj_all].
    all: specialize IHl with n; inj_all.
    all: try solve [specialize H1 with (S n) a; assert (n < S n) by lia; inj_all].
    - apply name_nat_leb; lia.
    - eapply H2; lia.
    - destruct H0. 
      + apply name_nat_inj in H0; lia.
      + eapply H3; try apply H0; eauto.
  Qed.

  Opaque name_list_ty.

  Fixpoint list_ty_pyro_to_fiat (t: term): result (list type) :=
    match t with
    | {{e #"empty_list_ty" {A} {l} }} => Success []
    | {{e #"cons_list_ty" {A} {l} }} => 
    ft <- ty_pyro_to_fiat A ;;
    l' <- list_ty_pyro_to_fiat l ;;
    Success (ft :: l')
    | _ => error:("term" t "not a type")
    end
  with ty_pyro_to_fiat (t: term): result type :=
    match t with
    | {{e #"bool"}} => Success TBool
    | {{e #"Trecord" {lty} }} =>
    lty <- list_ty_pyro_to_fiat lty ;;
    Success (TRecord (name_list_ty lty))
    | {{e #"list" {ty} }} => 
    ft <- ty_pyro_to_fiat ty ;;
    Success (TList ft)
    | _ => error:("term" t "not a type")
    end.

  Fixpoint env_pyro_to_fiat (t: term): result lenv :=
    match t with 
    | {{e #"emp"}} => Success [] 
    | {{e #"ext" {Gp} {A} }} =>
      fe <- ty_pyro_to_fiat A ;;
      G <- env_pyro_to_fiat Gp ;;
      Success ((of_nat (length G), fe) :: G) 
    | _ => error:("term" t "not an env") 
    end.

  Definition sub := (prod lenv lenv).

  Fixpoint sub_pyro_to_fiat (t: term): result sub :=
    match t with
    | {{e #"wkn" {Gp} {A} }} =>
      ft <- ty_pyro_to_fiat A ;;
      Gp <- env_pyro_to_fiat Gp ;;
      Success (Gp, ((of_nat (length Gp), ft) :: Gp)) 
    | _ => error:("term" t "not a sub") 
    end. (* TODO *)

  Fixpoint expr_pyro_to_fiat (t: term): result expr := (* * list (string * type)) := *)
    match t with
    | {{e #"true" {Gp} }} => Success (EAtom (ABool true))
    | {{e #"false" {Gp} }} => Success (EAtom (ABool false))
    | {{e #"notb" {Gp} {e} }} => 
    fe <- expr_pyro_to_fiat e ;; 
    Success (EUnop ONot fe)
    | {{e #"andb" {Gp} {e1} {e2} }} => 
    fe1 <- expr_pyro_to_fiat e1 ;; 
    fe2 <- expr_pyro_to_fiat e2 ;; 
    Success (EBinop OAnd fe1 fe2)
    | {{e #"orb" {Gp} {e1} {e2} }} => 
    fe1 <- expr_pyro_to_fiat e1 ;; 
    fe2 <- expr_pyro_to_fiat e2 ;; 
    Success (EBinop OOr fe1 fe2)
    | {{e #"cons" {Gp} {A} {e1} {e2} }} => 
    fe1 <- expr_pyro_to_fiat e1 ;; 
    fe2 <- expr_pyro_to_fiat e2 ;; 
    Success (EBinop OCons fe1 fe2)
    | {{e #"if" {Gp} {cond} {A} {e1} {e2} }} => 
    fcond <- expr_pyro_to_fiat cond ;; 
    fe1 <- expr_pyro_to_fiat e1 ;; 
    fe2 <- expr_pyro_to_fiat e2 ;; 
    Success (EIf fcond fe1 fe2)
    | {{e #"lempty" {Gp} {A} }} => 
    ft <- ty_pyro_to_fiat A ;;
    Success (EAtom (ANil (Some ft)))
    | _ => error:("term" t "not an expr")
    end.

  (*Definition tx := EIf (EAtom (ABool true)) (EAtom (ABool true)) (EAtom (ABool false)).*)
  Definition tx := EBinop OOr (EAtom (ABool false)) (EAtom (ABool false)).
  Definition pytx := match (expr_fiat_to_pyro tx [] []) with Success p => p | Failure _ => var "" end.

  Compute tx.
  Compute pytx.
  Compute expr_pyro_to_fiat pytx.
  Goal (Success tx) = (expr_pyro_to_fiat pytx). Proof. auto. Qed.

End WithMap.
