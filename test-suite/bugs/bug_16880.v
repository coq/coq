Polymorphic Axiom T@{u} : Prop.

Universe u1 u2.

Definition t1 := T@{u1}.
Definition t2 := T@{u2}.

Constraint u1 = u2.

Check fun P : t1 => P <: t2.
(* Error: In environment
P : t1
The term "P" has type "t1" while it is expected to have type "t2". *)
