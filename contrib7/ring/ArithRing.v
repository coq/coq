(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Instantiation of the Ring tactic for the naturals of Arith $*)

Require Export Ring.
Require Export Arith.
Require Eqdep_dec.

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Fixpoint nateq [n,m:nat] : bool :=
  Cases n m of
  | O O => true
  | (S n') (S m') => (nateq n' m')
  | _ _ => false
  end.

Lemma nateq_prop : (n,m:nat)(Is_true (nateq n m))->n==m.
Proof.
  Induction n; Induction m; Intros; Try Contradiction.
  Trivial.
  Unfold Is_true in H1.
  Rewrite (H n1 H1).
  Trivial.
Save.

Hints Resolve nateq_prop eq2eqT : arithring.

Definition NatTheory : (Semi_Ring_Theory plus mult (1) (0) nateq).
  Split; Intros; Auto with arith arithring.
  Apply eq2eqT; Apply simpl_plus_l with n:=n.
  Apply eqT2eq; Trivial.
Defined.


Add Semi Ring nat plus mult (1) (0) nateq NatTheory [O S].

Goal (n:nat)(S n)=(plus (S O) n).
Intro; Reflexivity.
Save S_to_plus_one.

(* Replace all occurrences of (S exp) by (plus (S O) exp), except when
   exp is already O and only for those occurrences than can be reached by going
   down plus and mult operations  *)
Recursive Meta Definition S_to_plus t :=
   Match t With 
   | [(S O)] -> '(S O)
   | [(S ?1)] -> Let t1 = (S_to_plus ?1) In
                 '(plus (S O) t1)
   | [(plus ?1 ?2)] -> Let t1 = (S_to_plus ?1) 
                     And t2 = (S_to_plus ?2) In
                     '(plus t1 t2)
   | [(mult ?1 ?2)] -> Let t1 = (S_to_plus ?1)
                     And t2 = (S_to_plus ?2) In
                     '(mult t1 t2)
   | [?] -> 't.

(* Apply S_to_plus on both sides of an equality *)
Tactic Definition S_to_plus_eq :=
   Match Context With
   | [ |- ?1 = ?2 ] -> 
      (**) Try (**)
      Let t1 = (S_to_plus ?1)
      And t2 = (S_to_plus ?2) In
        Change t1=t2
   | [ |- ?1 == ?2 ] ->
      (**) Try (**)
      Let t1 = (S_to_plus ?1)
      And t2 = (S_to_plus ?2) In
        Change (t1==t2).

Tactic Definition NatRing := S_to_plus_eq;Ring.
