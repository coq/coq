Section foo.
  Let k := 1.

  Definition v (x : nat) := k.
  Global Arguments v !_ / .
  Eval simpl in v 1. (* k *)
End foo.
About v.
(* v : nat -> nat

Argument scope is [nat_scope]
The reduction tactics unfold v when the 2nd argument evaluates to a constructor
and
  when applied to 2 arguments
v is transparent
Expands to: Constant Top.v
 *)
Eval simpl in v 1. (* v 1 *)
Goal True.
  let k := (eval simpl in (v 1))
  in constr_eq k 1. (* should succeed *)
Abort.
