Declare Custom Entry stlc.

Module Bug18342.
Definition A (T : True) := 0.
Notation "?" := A.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "'SS' x" := (S x) (in custom stlc at level 89, x custom stlc at level 99).

Check <{SS (? I)}>.
End Bug18342.

Declare Custom Entry qmark.

Module Bug18342VariantWithExplicitCoercions.
Definition A (T : True) := 0.

Notation "?" := A (in custom qmark).
Notation "{{ x }}" := x (x custom qmark).

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "[[ x ]]" := x (in custom stlc at level 0, x constr).
Notation "'SS' x" := (S x) (in custom stlc at level 89, x custom stlc at level 99).

Check <{SS [[{{?}} I]]}>.
End Bug18342VariantWithExplicitCoercions.

Module Bug18342VariantPattern.
Inductive I := C : nat -> I | D : I -> I.

Notation "?" := C (in custom qmark).
Notation "{{ x }}" := x (x custom qmark).

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "[[ x ]]" := x (in custom stlc at level 0, x constr).
Notation "'DD' x" := (D x) (in custom stlc at level 89, x custom stlc at level 99).

Check fun x => match x with <{DD [[{{?}} y]]}> => y | _ => 0 end.
End Bug18342VariantPattern.
