Set Primitive Projections.
Record total2 { T: Type } ( P: T -> Type ) := tpair { pr1 : T; pr2 : P pr1 }.
Theorem onefiber' {X : Type} (P : X -> Type) (x : X) : True.
Proof.
set (Q1 := total2 (fun f => pr1 P f = x)).
set (f1:=fun q1 : Q1 => pr2 _ (pr1 _ q1)).
