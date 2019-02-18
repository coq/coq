Set Mangle Names.

Inductive TCForall {A} (P : A -> Prop) : list A -> Prop :=
| TCForall_nil : TCForall P nil
| TCForall_cons x xs : P x -> TCForall P xs -> TCForall P (cons x xs).
