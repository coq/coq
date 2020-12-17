Inductive box (A : Type) := Box : A -> box A.

Axiom PRED : unit -> Prop.
Axiom FUN : forall (u : unit), box (PRED u).

Axiom U : unit.
Definition V := U.

Goal match FUN U with Box _ _ => True end.
Proof.
repeat match goal with
| [ |- context G[ U ] ] =>
 let e := context G [ V ] in
 change e
end.
set (Z := V).
clearbody Z. (* This fails if change misses the case parameters *)
destruct (FUN Z).
constructor.
Qed.
