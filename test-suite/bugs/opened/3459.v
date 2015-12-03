(* Bad interaction between clear and the typability of ltac constr bindings *)

(* Original report *)

Goal 1 = 2.
Proof.
(* This line used to fail with a Not_found up to some point, and then
   to produce an ill-typed term *)
match goal with
  | [ |- context G[2] ] => let y := constr:(fun x => ltac:(let r := constr:(@eq Set x x) in
                                                       clear x;
                                                       exact r)) in
                           pose y
end.
(* Add extra test for typability (should not fail when bug closed) *)
Fail match goal with P:?c |- _ => try (let x := type of c in idtac) || fail 2 end.
Abort.

(* Second report raising a Not_found at the time of 21 Oct 2014 *)

Section F.

Variable x : nat.

Goal True.
evar (e : Prop).
assert e.
Fail let r := constr:(eq_refl x) in clear x; exact r.
Abort.

End F.
