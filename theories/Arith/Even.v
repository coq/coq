
(* $Id$ *)

(* Here we define the predicates even and odd by mutual induction
 * and we prove the decidability and the exclusion of those predicates.
 *
 * The main results about parity are proved in the module Div2.
 *)

Inductive even : nat->Prop :=
    even_O : (even O)
  | even_S : (n:nat)(odd n)->(even (S n))
with odd : nat->Prop :=
    odd_S : (n:nat)(even n)->(odd (S n)).

Hint constr_even : arith := Constructors even.
Hint constr_odd : arith := Constructors odd.

Lemma even_or_odd : (n:nat) (even n)\/(odd n).
Proof.
Induction n.
Auto with arith.
Intros n' H. Elim H; Auto with arith.
Save.

Lemma even_odd_dec : (n:nat) { (even n) }+{ (odd n) }.
Proof.
Induction n.
Auto with arith.
Intros n' H. Elim H; Auto with arith.
Save.

Lemma not_even_and_odd : (n:nat) (even n) -> (odd n) -> False.
Proof.
Induction n.
Intros. Inversion H0.
Intros. Inversion H0. Inversion H1. Auto with arith.
Save.

