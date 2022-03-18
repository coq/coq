Require Import Ltac2.Ltac2.

Definition foo{E: Type}(f: E -> E): nat := 0.

Ltac2 feed_one_to_foo () := constr:(foo 1).

Fail Ltac2 Eval feed_one_to_foo ().

Ltac2 feed_constr_to_foo(x: constr) := constr:(foo $x).

Ltac2 Eval feed_constr_to_foo constr:(fun (a: nat) => a + 1).  (* succeeds *)

Fail Ltac2 Eval feed_constr_to_foo constr:(1).

Definition nat_to_fun (n:nat) : nat -> nat := plus n.
Coercion nat_to_fun : nat >-> Funclass.

Fail Ltac2 Eval feed_constr_to_foo constr:(1).
