(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Equality on natural numbers *)

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n,x,y:nat.

Fixpoint  eq_nat [n:nat] : nat -> Prop :=
  [m:nat]Cases n m of 
                O      O     => True
             |  O     (S _)  => False
             | (S _)   O     => False
             | (S n1) (S m1) => (eq_nat n1 m1)
          end.

Theorem eq_nat_refl : (n:nat)(eq_nat n n).
NewInduction n; Simpl; Auto.
Qed.
Hints Resolve eq_nat_refl : arith v62.

Theorem eq_eq_nat : (n,m:nat)(n=m)->(eq_nat n m).
NewInduction 1; Trivial with arith.
Qed.
Hints Immediate eq_eq_nat : arith v62.

Theorem eq_nat_eq : (n,m:nat)(eq_nat n m)->(n=m).
NewInduction n; NewInduction m; Simpl; Contradiction Orelse Auto with arith.
Qed.
Hints Immediate eq_nat_eq : arith v62.

Theorem eq_nat_elim : (n:nat)(P:nat->Prop)(P n)->(m:nat)(eq_nat n m)->(P m).
Intros; Replace m with n; Auto with arith.
Qed.

Theorem eq_nat_decide : (n,m:nat){(eq_nat n m)}+{~(eq_nat n m)}.
NewInduction n.
NewDestruct m.
Auto with arith.
Intros; Right; Red; Trivial with arith.
NewDestruct m.
Right; Red; Auto with arith.
Intros.
Simpl.
Apply IHn.
Defined.

Fixpoint  beq_nat [n:nat] : nat -> bool :=
  [m:nat]Cases n m of 
                O      O     => true
             |  O     (S _)  => false
             | (S _)   O     => false
             | (S n1) (S m1) => (beq_nat n1 m1)
          end.

Lemma beq_nat_refl : (x:nat)true=(beq_nat x x).
Proof.
  Intro x; NewInduction x; Simpl; Auto.
Qed.

Definition beq_nat_eq : (x,y:nat)true=(beq_nat x y)->x=y.
Proof.
  Double Induction x y; Simpl.
    Reflexivity.
    Intros; Discriminate H0.
    Intros; Discriminate H0.
    Intros; Case (H0 ? H1); Reflexivity.
Defined.

