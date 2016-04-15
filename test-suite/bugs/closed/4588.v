Set Primitive Projections.

(* This proof was accepted in Coq 8.5 because the subterm specs were not
projected correctly *)
Inductive foo : Prop := mkfoo { proj1 : False -> foo; proj2 : (forall P : Prop, P -> P) }.

Fail Fixpoint loop (x : foo) : False :=
  loop (proj2 x _ x).

Fail Definition bad : False := loop (mkfoo (fun x => match x with end) (fun _ x => x)).
