
(* variances other than Invariant are forbidden for non-cumul inductives *)
Fail Inductive foo@{+u} : Prop := .
Fail Polymorphic Inductive foo@{*u} : Prop := .
Inductive foo@{=u} : Prop := .

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive force_invariant@{=u} : Prop := .
Fail Definition lift@{u v | u < v} (x:force_invariant@{u}) : force_invariant@{v} := x.

Inductive force_covariant@{+u} : Prop := .
Fail Definition lift@{u v | v < u} (x:force_covariant@{u}) : force_covariant@{v} := x.
Definition lift@{u v | u < v} (x:force_covariant@{u}) : force_covariant@{v} := x.

Fail Inductive not_irrelevant@{*u} : Prop := nirr (_ : Type@{u}).
Inductive check_covariant@{+u} : Prop := cov (_ : Type@{u}).

Fail Inductive not_covariant@{+u} : Prop := ncov (_ : Type@{u} -> nat).
