
(* $Id$ *)

(* Instantiation of the Ring tactic for the naturals of Arith $*)

Require Export Ring.
Require Export Arith.
Require Eqdep_dec.

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
  Apply eq2eqT; Apply simpl_plus_l with n.
  Apply eqT2eq; Trivial.
Defined.


Add Semi Ring nat plus mult (1) (0) nateq NatTheory [O S].

Goal (n:nat)(S n)=(plus (S O) n).
Intro; Reflexivity.
Save S_to_plus_one.

Meta Definition NatRing := (Repeat Rewrite S_to_plus_one); Ring.
