Lemma f_equal@{a b} : forall (A:Type@{a}) (B : Type@{b}) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof. intros;congruence. Qed.

Register f_equal as core.eq.congr.

Set Universe Polymorphism.

Inductive prod (A B:Type) := pair : A -> B -> prod A B.

Scheme Equality for prod.
(*
Error: Unexpected error during scheme creation: Unsatisfied constraints:
foo.30 <= f_equal.a
foo.30 <= f_equal.b
foo.31 <= f_equal.a
foo.31 <= f_equal.b (maybe a bugged tactic).
*)
