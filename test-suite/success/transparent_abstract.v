Class by_transparent_abstract {T} (x : T) := make_by_transparent_abstract : T.
Hint Extern 0 (@by_transparent_abstract ?T ?x) => change T; transparent_abstract exact_no_check x : typeclass_instances.

Goal True /\ True.
Proof.
  split.
  transparent_abstract exact I using foo.
  let x := (eval hnf in foo) in constr_eq x I.
  let x := constr:(ltac:(constructor) : True) in
  let T := type of x in
  let x := constr:(_ : by_transparent_abstract x) in
  let x := (eval cbv delta [by_transparent_abstract] in (let y : T := x in y)) in
  pose x as x'.
  simpl in x'.
  let v := eval cbv [x'] in x' in tryif constr_eq v I then fail 0 else idtac.
  hnf in x'.
  let v := eval cbv [x'] in x' in tryif constr_eq v I then idtac else fail 0.
  exact x'.
Defined.
Check eq_refl : I = foo.
Eval compute in foo.
