(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import BinInt.
Require Import Zcompare.
Require Import Old_zorder.
Require Import Bool.
Open Local Scope Z_scope.

(**********************************************************************)
(** Iterators *)

(** [n]th iteration of the function [f] *)
Fixpoint iter_nat (n:nat) (A:Set) (f:A -> A) (x:A) {struct n} : A :=
  match n with
    | O => x
    | S n' => f (iter_nat n' A f x)
  end.

Fixpoint iter_pos (n:positive) (A:Set) (f:A -> A) (x:A) {struct n} : A :=
  match n with
    | xH => f x
    | xO n' => iter_pos n' A f (iter_pos n' A f x)
    | xI n' => f (iter_pos n' A f (iter_pos n' A f x))
  end.

Definition iter (n:Z) (A:Set) (f:A -> A) (x:A) :=
  match n with
    | Z0 => x
    | Zpos p => iter_pos p A f x
    | Zneg p => x
  end.

Theorem iter_nat_plus :
  forall (n m:nat) (A:Set) (f:A -> A) (x:A),
    iter_nat (n + m) A f x = iter_nat n A f (iter_nat m A f x).
Proof.    
  simple induction n;
    [ simpl in |- *; auto with arith
      | intros; simpl in |- *; apply f_equal with (f := f); apply H ].  
Qed.

Theorem iter_nat_of_P :
  forall (p:positive) (A:Set) (f:A -> A) (x:A),
    iter_pos p A f x = iter_nat (nat_of_P p) A f x.
Proof.    
  intro n; induction n as [p H| p H| ];
    [ intros; simpl in |- *; rewrite (H A f x);
      rewrite (H A f (iter_nat (nat_of_P p) A f x)); 
	rewrite (ZL6 p); symmetry  in |- *; apply f_equal with (f := f);
	  apply iter_nat_plus
      | intros; unfold nat_of_P in |- *; simpl in |- *; rewrite (H A f x);
	rewrite (H A f (iter_nat (nat_of_P p) A f x)); 
	  rewrite (ZL6 p); symmetry  in |- *; apply iter_nat_plus
      | simpl in |- *; auto with arith ].
Qed.

Theorem iter_pos_plus :
  forall (p q:positive) (A:Set) (f:A -> A) (x:A),
    iter_pos (p + q) A f x = iter_pos p A f (iter_pos q A f x).
Proof.    
  intros n m; intros.
  rewrite (iter_nat_of_P m A f x).
  rewrite (iter_nat_of_P n A f (iter_nat (nat_of_P m) A f x)).
  rewrite (iter_nat_of_P (n + m) A f x).
  rewrite (nat_of_P_plus_morphism n m).
  apply iter_nat_plus.
Qed.

(** Preservation of invariants : if [f : A->A] preserves the invariant [Inv], 
    then the iterates of [f] also preserve it. *)

Theorem iter_nat_invariant :
  forall (n:nat) (A:Set) (f:A -> A) (Inv:A -> Prop),
    (forall x:A, Inv x -> Inv (f x)) ->
    forall x:A, Inv x -> Inv (iter_nat n A f x).
Proof.    
  simple induction n; intros;
    [ trivial with arith
      | simpl in |- *; apply H0 with (x := iter_nat n0 A f x); apply H;
	trivial with arith ].
Qed.

Theorem iter_pos_invariant :
  forall (p:positive) (A:Set) (f:A -> A) (Inv:A -> Prop),
    (forall x:A, Inv x -> Inv (f x)) ->
    forall x:A, Inv x -> Inv (iter_pos p A f x).
Proof.    
  intros; rewrite iter_nat_of_P; apply iter_nat_invariant; trivial with arith.
Qed.
