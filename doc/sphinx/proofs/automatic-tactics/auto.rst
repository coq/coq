Here are two examples of ``autorewrite`` use. The first one ( *Ackermann
function*) shows actually a quite basic use where there is no
conditional rewriting. The second one ( *Mac Carthy function*)
involves conditional rewritings and shows how to deal with them using
the optional tactic of the ``Hint Rewrite`` command.


.. example:: Ackermann function

   .. coqtop:: in reset

      Require Import Arith.

   .. coqtop:: in

      Parameter Ack : nat -> nat -> nat.

   .. coqtop:: in

      Axiom Ack0 : forall m:nat, Ack 0 m = S m.
      Axiom Ack1 : forall n:nat, Ack (S n) 0 = Ack n 1.
      Axiom Ack2 : forall n m:nat, Ack (S n) (S m) = Ack n (Ack (S n) m).

   .. coqtop:: in

      Global Hint Rewrite Ack0 Ack1 Ack2 : base0.

   .. coqtop:: all

      Lemma ResAck0 : Ack 3 2 = 29.

   .. coqtop:: all

      autorewrite with base0 using try reflexivity.

.. example:: MacCarthy function

   .. coqtop:: in reset

      Require Import Lia.

   .. coqtop:: in

      Parameter g : nat -> nat -> nat.

   .. coqtop:: in

      Axiom g0 : forall m:nat, g 0 m = m.
      Axiom g1 : forall n m:nat, (n > 0) -> (m > 100) -> g n m = g (pred n) (m - 10).
      Axiom g2 : forall n m:nat, (n > 0) -> (m <= 100) -> g n m = g (S n) (m + 11).

   .. coqtop:: in

      Global Hint Rewrite g0 g1 g2 using lia : base1.

   .. coqtop:: in

      Lemma Resg0 : g 1 110 = 100.

   .. coqtop:: out

      Show.

   .. coqtop:: all

      autorewrite with base1 using reflexivity || simpl.

   .. coqtop:: none

      Qed.

   .. coqtop:: all

      Lemma Resg1 : g 1 95 = 91.

   .. coqtop:: all

      autorewrite with base1 using reflexivity || simpl.

   .. coqtop:: none

      Qed.
