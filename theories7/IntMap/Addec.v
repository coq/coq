(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(** Equality on adresses *)

Require Bool.
Require Sumbool.
Require ZArith.
Require Addr.

Fixpoint ad_eq_1 [p1,p2:positive] : bool :=
  Cases p1 p2 of
      xH xH => true
    | (xO p'1) (xO p'2) => (ad_eq_1 p'1 p'2)
    | (xI p'1) (xI p'2) => (ad_eq_1 p'1 p'2)
    | _ _ => false
  end.

Definition ad_eq := [a,a':ad]
  Cases a a' of
      ad_z ad_z => true
    | (ad_x p) (ad_x p') => (ad_eq_1 p p')
    | _ _ => false
  end.

Lemma ad_eq_correct : (a:ad) (ad_eq a a)=true.
Proof.
  NewDestruct a; Trivial.
  NewInduction p; Trivial.
Qed.

Lemma ad_eq_complete : (a,a':ad) (ad_eq a a')=true -> a=a'.
Proof.
  NewDestruct a. NewDestruct a'; Trivial. NewDestruct p.
  Discriminate 1.
  Discriminate 1.
  Discriminate 1.
  NewDestruct a'. Intros. Discriminate H.
  Unfold ad_eq. Intros. Cut p=p0. Intros. Rewrite H0. Reflexivity.
  Generalize Dependent p0.
  NewInduction p as [p IHp|p IHp|]. NewDestruct p0; Intro H.
  Rewrite (IHp p0). Reflexivity.
  Exact H.
  Discriminate H.
  Discriminate H.
  NewDestruct p0; Intro H. Discriminate H.
  Rewrite (IHp p0 H). Reflexivity.
  Discriminate H.
  NewDestruct p0; Intro H. Discriminate H.
  Discriminate H.
  Trivial.
Qed.

Lemma ad_eq_comm : (a,a':ad) (ad_eq a a')=(ad_eq a' a).
Proof.
  Intros. Cut (b,b':bool)(ad_eq a a')=b->(ad_eq a' a)=b'->b=b'.
  Intros. Apply H. Reflexivity.
  Reflexivity.
  NewDestruct b. Intros. Cut a=a'.
  Intro. Rewrite H1 in H0. Rewrite (ad_eq_correct a') in H0. Exact H0.
  Apply ad_eq_complete. Exact H.
  NewDestruct b'. Intros. Cut a'=a.
  Intro. Rewrite H1 in H. Rewrite H1 in H0. Rewrite <- H. Exact H0.
  Apply ad_eq_complete. Exact H0.
  Trivial.
Qed.

Lemma ad_xor_eq_true : (a,a':ad) (ad_xor a a')=ad_z -> (ad_eq a a')=true.
Proof.
  Intros. Rewrite (ad_xor_eq a a' H). Apply ad_eq_correct.
Qed.

Lemma ad_xor_eq_false :
    (a,a':ad) (p:positive) (ad_xor a a')=(ad_x p) -> (ad_eq a a')=false.
Proof.
  Intros. Elim (sumbool_of_bool (ad_eq a a')). Intro H0.
  Rewrite (ad_eq_complete a a' H0) in H. Rewrite (ad_xor_nilpotent a') in H. Discriminate H.
  Trivial.
Qed.

Lemma ad_bit_0_1_not_double : (a:ad) (ad_bit_0 a)=true ->
      (a0:ad) (ad_eq (ad_double a0) a)=false.
Proof.
  Intros. Elim (sumbool_of_bool (ad_eq (ad_double a0) a)). Intro H0.
  Rewrite <- (ad_eq_complete ? ? H0) in H. Rewrite (ad_double_bit_0 a0) in H. Discriminate H.
  Trivial.
Qed.

Lemma ad_not_div_2_not_double : (a,a0:ad) (ad_eq (ad_div_2 a) a0)=false ->
      (ad_eq a (ad_double a0))=false.
Proof.
  Intros. Elim (sumbool_of_bool (ad_eq (ad_double a0) a)). Intro H0.
  Rewrite <- (ad_eq_complete ? ? H0) in H. Rewrite (ad_double_div_2 a0) in H.
  Rewrite (ad_eq_correct a0) in H. Discriminate H.
  Intro. Rewrite ad_eq_comm. Assumption.
Qed.

Lemma ad_bit_0_0_not_double_plus_un : (a:ad) (ad_bit_0 a)=false ->
      (a0:ad) (ad_eq (ad_double_plus_un a0) a)=false.
Proof.
  Intros. Elim (sumbool_of_bool (ad_eq (ad_double_plus_un a0) a)). Intro H0.
  Rewrite <- (ad_eq_complete ? ? H0) in H. Rewrite (ad_double_plus_un_bit_0 a0) in H.
  Discriminate H.
  Trivial.
Qed.

Lemma ad_not_div_2_not_double_plus_un : (a,a0:ad) (ad_eq (ad_div_2 a) a0)=false ->
      (ad_eq (ad_double_plus_un a0) a)=false.
Proof.
  Intros. Elim (sumbool_of_bool (ad_eq a (ad_double_plus_un a0))). Intro H0.
  Rewrite (ad_eq_complete ? ? H0) in H. Rewrite (ad_double_plus_un_div_2 a0) in H.
  Rewrite (ad_eq_correct a0) in H. Discriminate H.
  Intro H0. Rewrite ad_eq_comm. Assumption.
Qed.

Lemma ad_bit_0_neq :
    (a,a':ad) (ad_bit_0 a)=false -> (ad_bit_0 a')=true -> (ad_eq a a')=false.
Proof.
  Intros. Elim (sumbool_of_bool (ad_eq a a')). Intro H1. Rewrite (ad_eq_complete ? ? H1) in H.
  Rewrite H in H0. Discriminate H0.
  Trivial.
Qed.

Lemma ad_div_eq :
    (a,a':ad) (ad_eq a a')=true -> (ad_eq (ad_div_2 a) (ad_div_2 a'))=true.
Proof.
  Intros. Cut a=a'. Intros. Rewrite H0. Apply ad_eq_correct.
  Apply ad_eq_complete. Exact H.
Qed.

Lemma ad_div_neq : (a,a':ad) (ad_eq (ad_div_2 a) (ad_div_2 a'))=false -> 
    (ad_eq a a')=false.
Proof.
  Intros. Elim (sumbool_of_bool (ad_eq a a')). Intro H0.
  Rewrite (ad_eq_complete ? ? H0) in H. Rewrite (ad_eq_correct (ad_div_2 a')) in H. Discriminate H.
  Trivial.
Qed.

Lemma ad_div_bit_eq : (a,a':ad) (ad_bit_0 a)=(ad_bit_0 a') ->
    (ad_div_2 a)=(ad_div_2 a') -> a=a'.
Proof.
  Intros. Apply ad_faithful. Unfold eqf. NewDestruct n.
  Rewrite ad_bit_0_correct. Rewrite ad_bit_0_correct. Assumption.
  Rewrite <- ad_div_2_correct. Rewrite <- ad_div_2_correct.
  Rewrite H0. Reflexivity.
Qed.

Lemma ad_div_bit_neq : (a,a':ad) (ad_eq a a')=false -> (ad_bit_0 a)=(ad_bit_0 a') ->
    (ad_eq (ad_div_2 a) (ad_div_2 a'))=false.
Proof.
  Intros. Elim (sumbool_of_bool (ad_eq (ad_div_2 a) (ad_div_2 a'))). Intro H1.
  Rewrite (ad_div_bit_eq ? ? H0 (ad_eq_complete ? ? H1)) in H.
  Rewrite (ad_eq_correct a') in H. Discriminate H.
  Trivial.
Qed.

Lemma ad_neq : (a,a':ad) (ad_eq a a')=false ->
    (ad_bit_0 a)=(negb (ad_bit_0 a')) \/ (ad_eq (ad_div_2 a) (ad_div_2 a'))=false.
Proof.
  Intros. Cut (ad_bit_0 a)=(ad_bit_0 a')\/(ad_bit_0 a)=(negb (ad_bit_0 a')).
  Intros. Elim H0. Intro. Right . Apply ad_div_bit_neq. Assumption.
  Assumption.
  Intro. Left . Assumption.
  Case (ad_bit_0 a); Case (ad_bit_0 a'); Auto.
Qed.

Lemma ad_double_or_double_plus_un : (a:ad)
    {a0:ad | a=(ad_double a0)}+{a1:ad | a=(ad_double_plus_un a1)}.
Proof.
  Intro. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H. Right . Split with (ad_div_2 a).
  Rewrite (ad_div_2_double_plus_un a H). Reflexivity.
  Intro H. Left . Split with (ad_div_2 a). Rewrite (ad_div_2_double a H). Reflexivity.
Qed.
