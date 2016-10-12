Goal True.
let T1 := constr:(Type) in
let T2 := constr:(Type) in
let X := constr:((T1, T2)) in
match X with (?A, ?A) => idtac end.
Abort.

Goal (Type * Type).
match goal with |- (?A * ?A)%type => refine ((Type, Type) : (A * A)) end.
Qed.