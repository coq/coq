(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require BinInt.
Require Zcompare.
Require Zorder.
Require Zsyntax.
Require Bool.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

(**********************************************************************)
(** Iterators *)

(** [n]th iteration of the function [f] *)
Fixpoint iter_nat[n:nat]  : (A:Set)(f:A->A)A->A :=
  [A:Set][f:A->A][x:A]
    Cases n of
      O => x
    | (S n') => (f (iter_nat n' A f x))
    end.

Fixpoint iter_pos[n:positive] : (A:Set)(f:A->A)A->A :=
  [A:Set][f:A->A][x:A]
    Cases n of
     	xH => (f x)
      | (xO n') => (iter_pos n' A f (iter_pos n' A f x))
      | (xI n') => (f (iter_pos n' A f (iter_pos n' A f x)))
    end.

Definition iter :=
  [n:Z][A:Set][f:A->A][x:A]Cases n of
    ZERO => x
  | (POS p) => (iter_pos p A f x)
  | (NEG p) => x
  end.

Theorem iter_nat_plus :
  (n,m:nat)(A:Set)(f:A->A)(x:A)
    (iter_nat (plus n m) A f x)=(iter_nat n A f (iter_nat m A f x)).
Proof.    
Induction n;
[ Simpl; Auto with arith
| Intros; Simpl; Apply f_equal with f:=f; Apply H
].  
Qed.

Theorem iter_convert : (n:positive)(A:Set)(f:A->A)(x:A)
  (iter_pos n A f x) = (iter_nat (convert n) A f x).
Proof.    
Intro n; NewInduction n as [p H|p H|];
[ Intros; Simpl; Rewrite -> (H A f x);
  Rewrite -> (H A f (iter_nat (convert p) A f x));
  Rewrite -> (ZL6 p); Symmetry; Apply f_equal with f:=f;
  Apply iter_nat_plus
| Intros; Unfold convert; Simpl; Rewrite -> (H A f x);
  Rewrite -> (H A f (iter_nat (convert p) A f x));
  Rewrite -> (ZL6 p); Symmetry;
  Apply iter_nat_plus
| Simpl; Auto with arith
].
Qed.

Theorem iter_pos_add :
  (n,m:positive)(A:Set)(f:A->A)(x:A)
    (iter_pos (add n m) A f x)=(iter_pos n A f (iter_pos m A f x)).
Proof.    
Intros n m; Intros.
Rewrite -> (iter_convert m A f x).
Rewrite -> (iter_convert n A f (iter_nat (convert m) A f x)).
Rewrite -> (iter_convert (add n m) A f x).
Rewrite -> (convert_add n m).
Apply iter_nat_plus.
Qed.

(** Preservation of invariants : if [f : A->A] preserves the invariant [Inv], 
    then the iterates of [f] also preserve it. *)

Theorem iter_nat_invariant :
  (n:nat)(A:Set)(f:A->A)(Inv:A->Prop)
  ((x:A)(Inv x)->(Inv (f x)))->(x:A)(Inv x)->(Inv (iter_nat n A f x)).
Proof.    
Induction n; Intros;
[ Trivial with arith
| Simpl; Apply H0 with x:=(iter_nat n0 A f x); Apply H; Trivial with arith].
Qed.

Theorem iter_pos_invariant :
  (n:positive)(A:Set)(f:A->A)(Inv:A->Prop)
  ((x:A)(Inv x)->(Inv (f x)))->(x:A)(Inv x)->(Inv (iter_pos n A f x)).
Proof.    
Intros; Rewrite iter_convert; Apply iter_nat_invariant; Trivial with arith.
Qed.



