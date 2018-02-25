(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-20011                            *)
(*                                                                      *)
(************************************************************************)

Require Import List.
Require Import Refl.
Require Import Bool.

Set Implicit Arguments.


  Inductive BFormula (A:Type) : Type :=
  | TT   : BFormula A
  | FF   : BFormula A
  | X : Prop -> BFormula A
  | A : A -> BFormula A
  | Cj  : BFormula A -> BFormula A -> BFormula A
  | D   : BFormula A-> BFormula A -> BFormula A
  | N  : BFormula A -> BFormula A
  | I : BFormula A-> BFormula A-> BFormula A.

  Fixpoint eval_f (A:Type)  (ev:A -> Prop ) (f:BFormula A) {struct f}: Prop :=
    match f with
      | TT _ => True
      | FF _ => False
      | A a =>  ev a
      | X _ p => p
      | Cj e1 e2 => (eval_f  ev e1) /\ (eval_f ev e2)
      | D e1 e2  => (eval_f  ev e1) \/ (eval_f  ev e2)
      | N e     => ~ (eval_f  ev e)
      | I f1 f2 => (eval_f  ev f1) -> (eval_f  ev f2)
    end.

  Lemma eval_f_morph : forall  A (ev ev' : A -> Prop) (f : BFormula A),
    (forall a, ev a <-> ev' a) -> (eval_f ev f <-> eval_f ev' f).
  Proof.
    induction f ; simpl ; try tauto.
    intros.
    assert (H' := H a).
    auto.
  Qed.



  Fixpoint map_bformula (T U : Type) (fct : T -> U) (f : BFormula T) : BFormula U :=
    match f with
      | TT _ => TT _
      | FF _ => FF _
      | X _ p => X _ p
      | A a => A (fct a)
      | Cj f1 f2 => Cj (map_bformula fct f1) (map_bformula fct f2)
      | D f1 f2 => D (map_bformula fct f1) (map_bformula fct f2)
      | N f     => N (map_bformula fct f)
      | I f1 f2 => I (map_bformula fct f1) (map_bformula fct f2)
    end.

  Lemma eval_f_map : forall T U (fct: T-> U) env f ,
    eval_f env  (map_bformula fct f)  = eval_f (fun x => env (fct x)) f.
  Proof.
    induction f ; simpl ; try (rewrite IHf1 ; rewrite IHf2) ; auto.
    rewrite <- IHf.  auto.    
  Qed.



  Lemma map_simpl : forall A B f l, @map A B f l = match l with
                                                 | nil => nil
                                                 | a :: l=> (f a) :: (@map A B f l)
                                               end.
  Proof.
    destruct l ; reflexivity.
  Qed.




  Section S.

    Variable Env   : Type.
    Variable Term  : Type.
    Variable eval  : Env -> Term -> Prop.
    Variable Term' : Type.
    Variable eval'  : Env -> Term' -> Prop.



    Variable no_middle_eval' : forall env d, (eval' env d) \/ ~ (eval' env d).

    Variable unsat : Term'  -> bool.

    Variable unsat_prop : forall t, unsat t  = true ->  
      forall env, eval' env t -> False. 

    Variable deduce : Term' -> Term' -> option Term'.

    Variable deduce_prop : forall env t t' u,
      eval' env t -> eval' env t' -> deduce t t' = Some u -> eval' env u.

    Definition clause := list  Term'.
    Definition cnf := list clause.

    Variable normalise : Term -> cnf.
    Variable negate : Term -> cnf.


    Definition tt : cnf := @nil clause.
    Definition ff : cnf :=  cons (@nil Term') nil.


    Fixpoint add_term (t: Term') (cl : clause) : option clause :=
      match cl with
        | nil => 
          match deduce t t with
            | None =>  Some (t ::nil)
            | Some u => if unsat u then None else Some (t::nil)
          end
        | t'::cl => 
          match deduce t t' with
            | None => 
              match add_term t cl with
                | None => None
                | Some cl' => Some (t' :: cl')
              end
            | Some u => 
              if unsat u then None else 
                match add_term t cl with
                  | None => None
                  | Some cl' => Some (t' :: cl')
                end
          end
      end.

    Fixpoint or_clause (cl1 cl2 : clause) : option clause :=
      match cl1 with
        | nil => Some cl2
        | t::cl => match add_term t cl2 with
                     | None => None
                     | Some cl' => or_clause cl cl'
                   end
      end.

(*    Definition or_clause_cnf (t:clause) (f:cnf) : cnf :=
      List.map (fun x => (t++x)) f. *)

    Definition or_clause_cnf (t:clause) (f:cnf) : cnf :=
      List.fold_right (fun e acc => 
        match or_clause t e with
          | None => acc
          | Some cl => cl :: acc
        end) nil f.


    Fixpoint or_cnf (f : cnf) (f' : cnf) {struct f}: cnf :=
      match f with
        | nil => tt
        | e :: rst => (or_cnf rst f') ++ (or_clause_cnf e f')
      end.


    Definition and_cnf (f1 : cnf) (f2 : cnf) : cnf :=
      f1 ++ f2.

    Fixpoint xcnf (pol : bool) (f : BFormula Term)  {struct f}: cnf :=
      match f with
        | TT _ => if pol then tt else ff
        | FF _ => if pol then ff else tt
        | X _ p => if pol then ff else ff (* This is not complete - cannot negate any proposition *)
        | A x => if pol then normalise x else negate x
        | N e  => xcnf (negb pol) e
        | Cj e1 e2 =>
          (if pol then and_cnf else or_cnf) (xcnf pol e1) (xcnf pol e2)
        | D e1 e2  => (if pol then or_cnf else and_cnf) (xcnf pol e1) (xcnf pol e2)
        | I e1 e2 => (if pol then or_cnf else and_cnf) (xcnf (negb pol) e1) (xcnf pol e2)
      end.

    Definition eval_clause (env : Env) (cl : clause) := ~ make_conj  (eval' env) cl.

    Definition eval_cnf (env : Env) (f:cnf) := make_conj  (eval_clause  env) f.

    
    Lemma eval_cnf_app : forall env x y, eval_cnf env (x++y) -> eval_cnf env x /\ eval_cnf env y.
    Proof.
      unfold eval_cnf.
      intros.
      rewrite make_conj_app in H ; auto.
    Qed.


    Definition eval_opt_clause (env : Env) (cl: option clause) :=
      match cl with
        | None => True
        | Some cl => eval_clause env cl
      end.


    Lemma add_term_correct : forall env t cl , eval_opt_clause env (add_term t cl) -> eval_clause env (t::cl).
    Proof.
      induction cl.
      (* BC *)
      simpl.
      case_eq (deduce t t) ; auto.
      intros *.
      case_eq (unsat t0) ; auto.
      unfold eval_clause.
      rewrite make_conj_cons. 
      intros. intro.
      apply unsat_prop with (1:= H) (env := env).
      apply deduce_prop with (3:= H0) ; tauto.
      (* IC *)
      simpl.
      case_eq (deduce t a).
      intro u.
      case_eq (unsat u).
      simpl. intros.
      unfold eval_clause.
      intro.
      apply unsat_prop  with (1:= H) (env:= env).
      repeat rewrite make_conj_cons in H2.
      apply deduce_prop with (3:= H0); tauto.
      intro.
      case_eq (add_term t cl) ; intros.
      simpl in H2.
      rewrite H0 in IHcl.
      simpl in IHcl.
      unfold eval_clause in *.
      intros.
      repeat rewrite make_conj_cons in *.
      tauto.
      rewrite H0 in IHcl ; simpl in *.
      unfold eval_clause in *.
      intros.
      repeat rewrite make_conj_cons in *.
      tauto.
      case_eq (add_term t cl) ; intros.
      simpl in H1.
      unfold eval_clause in *.
      repeat rewrite make_conj_cons in *.
      rewrite H in IHcl.
      simpl in IHcl.
      tauto.
      simpl in *.
      rewrite H in IHcl.
      simpl in IHcl.
      unfold eval_clause in *.
      repeat rewrite make_conj_cons in *.    
      tauto.
    Qed.


  Lemma or_clause_correct : forall cl cl' env,  eval_opt_clause env (or_clause cl cl') -> eval_clause env cl \/ eval_clause env cl'.
  Proof.
    induction cl.
    simpl. tauto.
    intros *.
    simpl.
    assert (HH := add_term_correct env a cl').
    case_eq (add_term a cl').
    simpl in *.
    intros.
    apply IHcl in H0.
    rewrite H in HH.
    simpl in HH.
    unfold eval_clause in *.
    destruct H0.
    repeat rewrite make_conj_cons in *.
    tauto.
    apply HH in H0.
    apply not_make_conj_cons in H0 ; auto.
    repeat rewrite make_conj_cons in *.
    tauto.
    simpl.
    intros.
    rewrite H in HH.
    simpl in HH.
    unfold eval_clause in *.
    assert (HH' := HH Coq.Init.Logic.I).
    apply not_make_conj_cons in HH'; auto.
    repeat rewrite make_conj_cons in *.
    tauto.
  Qed.
    

  Lemma or_clause_cnf_correct : forall env t f, eval_cnf env (or_clause_cnf t f) -> (eval_clause env t) \/ (eval_cnf env f).
  Proof.
    unfold eval_cnf.
    unfold or_clause_cnf.
    intros until t.
    set (F := (fun (e : clause) (acc : list clause) =>
         match or_clause t e with
         | Some cl => cl :: acc
         | None => acc
         end)).
    induction f.
    auto.
    (**)
    simpl.
    intros.
    destruct f.
    simpl in H.
    simpl in IHf. 
    unfold F in H.
    revert H.
    intros.
    apply or_clause_correct.
    destruct (or_clause t a) ; simpl in * ; auto.
    unfold F in H at 1.
    revert H.
    assert (HH := or_clause_correct t a env).
    destruct (or_clause t a); simpl in HH ;
    rewrite make_conj_cons in * ; intuition.
    rewrite make_conj_cons in *.
    tauto.
  Qed.


 Lemma eval_cnf_cons : forall env a f,  (~ make_conj  (eval' env) a) -> eval_cnf env f -> eval_cnf env (a::f).
 Proof.
   intros.
   unfold eval_cnf in *.
   rewrite make_conj_cons ; eauto.
 Qed.

  Lemma or_cnf_correct : forall env f f', eval_cnf env (or_cnf f f') -> (eval_cnf env  f) \/ (eval_cnf  env f').
  Proof.
    induction f.
    unfold eval_cnf.
    simpl.
    tauto.
    (**)
    intros.
    simpl in H.
    destruct (eval_cnf_app _ _ _ H).
    clear H.
    destruct (IHf _ H0).
    destruct (or_clause_cnf_correct _ _ _ H1).
    left.
    apply eval_cnf_cons ; auto.
    right ; auto.
    right ; auto.
  Qed.

  Variable normalise_correct : forall env t, eval_cnf  env (normalise t) -> eval env t.

  Variable negate_correct : forall env t, eval_cnf env (negate t) -> ~ eval env t.


  Lemma xcnf_correct : forall f pol env, eval_cnf env (xcnf pol f) -> eval_f (eval env) (if pol then f else N f).
  Proof.
    induction f.
    (* TT *)
    unfold eval_cnf.
    simpl.
    destruct pol ; simpl ; auto.
    (* FF *)
    unfold eval_cnf.
    destruct pol; simpl ; auto.
    unfold eval_clause ; simpl.
    tauto.
    (* P *)
    simpl.
    destruct pol ; intros ;simpl.
    unfold eval_cnf in H.
    (* Here I have to drop the proposition *)
    simpl in H.
    unfold eval_clause in H ; simpl in H.
    tauto.
    (* Here, I could store P in the clause *)
    unfold eval_cnf in H;simpl in H.
    unfold eval_clause in H ; simpl in H.
    tauto.
    (* A *)
    simpl.
    destruct pol ; simpl.
    intros.
    apply normalise_correct  ; auto.
    (* A 2 *)
    intros.
    apply  negate_correct ; auto.
    auto.
    (* Cj *)
    destruct pol ; simpl.
    (* pol = true *)
    intros.
    unfold and_cnf in H.
    destruct (eval_cnf_app  _ _ _ H).
    clear H.
    split.
    apply (IHf1 _ _ H0).
    apply (IHf2 _ _ H1).
    (* pol = false *)
    intros.
    destruct (or_cnf_correct _ _ _ H).
    generalize (IHf1 false  env H0).
    simpl.
    tauto.
    generalize (IHf2 false  env H0).
    simpl.
    tauto.
    (* D *)
    simpl.
    destruct pol.
    (* pol = true *)
    intros.
    destruct (or_cnf_correct _ _ _ H).
    generalize (IHf1 _  env H0).
    simpl.
    tauto.
    generalize (IHf2 _  env H0).
    simpl.
    tauto.
    (* pol = true *)
    unfold and_cnf.
    intros.
    destruct (eval_cnf_app  _ _ _ H).
    clear H.
    simpl.
    generalize (IHf1 _ _ H0).
    generalize (IHf2 _ _ H1).
    simpl.
    tauto.
    (**)
    simpl.
    destruct pol ; simpl.
    intros.
    apply (IHf false) ; auto.
    intros.
    generalize (IHf _ _ H).
    tauto.
    (* I *)
    simpl; intros.
    destruct pol.
    simpl.
    intro.
    destruct (or_cnf_correct _ _ _ H).
    generalize (IHf1 _ _ H1).
    simpl in *.
    tauto.
    generalize (IHf2 _ _ H1).
    auto.
    (* pol = false *)
    unfold and_cnf in H.
    simpl in H.
    destruct (eval_cnf_app _ _ _ H).
    generalize (IHf1 _ _ H0).
    generalize (IHf2 _ _ H1).
    simpl.
    tauto.
  Qed.


  Variable Witness : Type.
  Variable checker : list Term' -> Witness -> bool.

  Variable checker_sound : forall t  w, checker t w = true -> forall env, make_impl (eval' env)  t False.

  Fixpoint cnf_checker (f : cnf) (l : list Witness)  {struct f}: bool :=
    match f with
      | nil => true
      | e::f => match l with
                  | nil => false
                  | c::l => match checker e c with
                              | true => cnf_checker f l
                              |   _  => false
                            end
                end
      end.

  Lemma cnf_checker_sound : forall t  w, cnf_checker t w = true -> forall env, eval_cnf  env  t.
  Proof.
    unfold eval_cnf.
    induction t.
    (* bc *)
    simpl.
    auto.
    (* ic *)
    simpl.
    destruct w.
    intros ; discriminate.
    case_eq (checker a w) ; intros ; try discriminate.
    generalize (@checker_sound _ _ H env).
    generalize (IHt _ H0 env) ; intros.
    destruct t.
    red ; intro.
    rewrite <- make_conj_impl in H2.
    tauto.
    rewrite <- make_conj_impl in H2.
    tauto.
  Qed.


  Definition tauto_checker (f:BFormula Term) (w:list Witness) : bool :=
    cnf_checker (xcnf true f) w.

  Lemma tauto_checker_sound : forall t  w, tauto_checker t w = true -> forall env, eval_f  (eval env)  t.
  Proof.
    unfold tauto_checker.
    intros.
    change (eval_f (eval env) t) with (eval_f (eval env) (if true then t else TT Term)).
    apply (xcnf_correct t true).
    eapply cnf_checker_sound ; eauto.
  Qed.



End S.

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
