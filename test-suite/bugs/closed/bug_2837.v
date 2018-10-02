Require Import JMeq.

Axiom test : forall n m : nat, JMeq n m.

Goal forall n m : nat, JMeq n m.

(* I) with no intros nor variable hints, this should produce a regular error
      instead of Uncaught exception Failure("nth"). *)
Fail rewrite test.

(* II) with intros but indication of variables, still an error *)
Fail (intros; rewrite test).

(* III) a working variant: *)
intros; rewrite (test n m).
