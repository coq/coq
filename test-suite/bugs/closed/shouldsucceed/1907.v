(* An example of type inference *)

Axiom A : Type.
Definition f (x y : A) := x.
Axiom g : forall x y : A, f x y = y -> Prop.
Axiom x : A.
Check (g x _ (refl_equal x)).
