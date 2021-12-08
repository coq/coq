

Class abstract_term {T} (x : T) := by_abstract_term : T.
Hint Extern 0 (@abstract_term ?T ?x) => change T; abstract (exact x) : typeclass_instances.

Goal True.
  let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let x := match constr:(x) with ?y => y end in
  pose x as v. (* was Error: Variable x should be bound to a term but is bound to a constr. *)
  exact v.
Qed.
