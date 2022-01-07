Class Foo.

Fixpoint test (H : Foo) (n : nat) {A : Type} {struct n} : A.
Admitted.

About test.
(* test : Foo -> nat -> forall A : Type, A
test is universe polymorphic
Argument n is implicit and maximally inserted *)
