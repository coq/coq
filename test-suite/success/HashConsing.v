(* make sure HashConsing option can be Set and Unset *)

Unset HashConsing.
Theorem foo : forall x : nat, x = x.
Proof.
  trivial.
Qed.

Set HashConsing.
Theorem bar : forall x : nat, x = x.
Proof.
  apply foo.
Qed.


