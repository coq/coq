(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
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
      | TT => True
      | FF => False
      | A a =>  ev a
      | X p => p
      | Cj e1 e2 => (eval_f  ev e1) /\ (eval_f ev e2)
      | D e1 e2  => (eval_f  ev e1) \/ (eval_f  ev e2)
      | N e     => ~ (eval_f  ev e)
      | I f1 f2 => (eval_f  ev f1) -> (eval_f  ev f2)
    end.


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


    Definition clause := list  Term'.
    Definition cnf := list clause.

    Variable normalise : Term -> cnf.
    Variable negate : Term -> cnf.


    Definition tt : cnf := @nil clause.
    Definition ff : cnf :=  cons (@nil Term') nil.


    Definition or_clause_cnf (t:clause) (f:cnf) : cnf :=
      List.map (fun x => (t++x)) f.
    
    Fixpoint or_cnf (f : cnf) (f' : cnf) {struct f}: cnf :=
      match f with
        | nil => tt
        | e :: rst => (or_cnf rst f') ++ (or_clause_cnf e f')
      end.
    

    Definition and_cnf (f1 : cnf) (f2 : cnf) : cnf :=
      f1 ++ f2.
    
    Fixpoint xcnf (pol : bool) (f : BFormula Term)  {struct f}: cnf :=
      match f with
        | TT => if pol then tt else ff
        | FF => if pol then ff else tt
        | X p => if pol then ff else ff (* This is not complete - cannot negate any proposition *)
        | A x => if pol then normalise x else negate x
        | N e  => xcnf (negb pol) e
        | Cj e1 e2 => 
          (if pol then and_cnf else or_cnf) (xcnf pol e1) (xcnf pol e2)
        | D e1 e2  => (if pol then or_cnf else and_cnf) (xcnf pol e1) (xcnf pol e2)
        | I e1 e2 => (if pol then or_cnf else and_cnf) (xcnf (negb pol) e1) (xcnf pol e2)
      end.

  Definition eval_cnf (env : Term' -> Prop) (f:cnf) := make_conj  (fun cl => ~ make_conj  env cl) f.
  

  Lemma eval_cnf_app : forall env x y, eval_cnf (eval' env) (x++y) -> eval_cnf (eval' env) x /\ eval_cnf (eval' env) y.
  Proof.
    unfold eval_cnf.
    intros.
    rewrite make_conj_app in H ; auto.
  Qed.
    

  Lemma or_clause_correct : forall env t f, eval_cnf (eval' env) (or_clause_cnf t f) -> (~ make_conj  (eval' env) t) \/ (eval_cnf (eval' env) f).
  Proof.
    unfold eval_cnf.
    unfold or_clause_cnf.
    induction f.
    simpl.
    intros ; right;auto.
    (**)
    rewrite map_simpl.
    intros.
    rewrite make_conj_cons in H.
    destruct H as [HH1 HH2].
    generalize (IHf HH2) ; clear IHf ; intro.
    destruct H.
    left ; auto.
    rewrite make_conj_cons.
    destruct (not_make_conj_app _ _ _ (no_middle_eval' env) HH1).
    tauto.
    tauto.
  Qed.

 Lemma eval_cnf_cons : forall env a f,  (~ make_conj  (eval' env) a) -> eval_cnf (eval' env) f -> eval_cnf (eval' env) (a::f).
 Proof.
   intros.
   unfold eval_cnf in *.
   rewrite make_conj_cons ; eauto.
 Qed.

  Lemma or_cnf_correct : forall env f f', eval_cnf (eval' env) (or_cnf f f') -> (eval_cnf (eval' env)  f) \/ (eval_cnf (eval' env) f').
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
    destruct (or_clause_correct _ _ _ H1).
    left.
    apply eval_cnf_cons ; auto.
    right ; auto.
    right ; auto.
  Qed.

  Variable normalise_correct : forall env t, eval_cnf (eval' env) (normalise t) -> eval env t.

  Variable negate_correct : forall env t, eval_cnf  (eval' env) (negate t) -> ~ eval env t.


  Lemma xcnf_correct : forall f pol env, eval_cnf (eval' env) (xcnf pol f) -> eval_f (eval env) (if pol then f else N f).
  Proof.
    induction f.
    (* TT *)
    unfold eval_cnf.
    simpl.
    destruct pol ; simpl ; auto.
    (* FF *)
    unfold eval_cnf.
    destruct pol; simpl ; auto.
    (* P *)
    simpl.
    destruct pol ; intros ;simpl.
    unfold eval_cnf in H.
    (* Here I have to drop the proposition *)
    simpl in H.
    tauto.
    (* Here, I could store P in the clause *)
    unfold eval_cnf in H;simpl in H.
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

  Lemma cnf_checker_sound : forall t  w, cnf_checker t w = true -> forall env, eval_cnf  (eval' env)  t.
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

