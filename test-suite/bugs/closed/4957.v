Ltac get_value H := eval cbv delta [H] in H.

Goal True.
refine (let X := _ in _).
let e := get_value X in unify e Prop.
Abort.
