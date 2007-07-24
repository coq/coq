Require Export ZPairsPlus.

Module NatPairsTimes (Import NTimesModule : NTimesSignature) <: ZTimesSignature.
Module Import ZPlusModule := NatPairsPlus NTimesModule.NPlusModule. (* "NTimesModule." is optional *)
Open Local Scope NatScope.

Definition times (n m : Z) :=
(*  let (n1, n2) := n in
  let (m1, m2) := m in (n1 * m1 + n2 * m2, n1 * m2 + n2 * m1).*)
  ((fst n) * (fst m) + (snd n) * (snd m), (fst n) * (snd m) + (snd n) * (fst m)).

Notation "x * y" := (times x y) : IntScope.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
unfold times, E; intros x1 y1 H1 x2 y2 H2; simpl.
assert ((fst x1) + (fst y1) == (fst y1) + (fst x1)).
ring.


Axiom times_0 : forall n, n * 0 == 0.
Axiom times_S : forall n m, n * (S m) == n * m + n.

(* Here recursion is done on the second argument to conform to the
usual definition of ordinal multiplication in set theory, which is not
commutative. It seems, however, that this definition in set theory is
unfortunate for two reasons. First, multiplication of two ordinals A
and B can be defined as (an order type of) the cartesian product B x A
(not A x B) ordered lexicographically. For example, omega * 2 =
2 x omega = {(0,0) < (0,1) < (0,2) < ... < (1,0) < (1,1) < (1,2) < ...},
while 2 * omega = omega x 2 = {(0,0) < (0,1) < (1,0) < (1,1) < (2,0) <
(2,1) < ...} = omega. Secondly, the way the product 2 * 3 is said in
French (deux fois trois) and Russian (dvazhdy tri) implies 3 + 3, not
2 + 2 + 2. So it would possibly be more reasonable to define multiplication
(here as well as in set theory) by recursion on the first argument. *)

End ZTimesSignature.
