Class Foo.

Fixpoint test (H : Foo) (n : nat) {A : Type} {struct n} : A.
Admitted.

Check fun (x:Foo) => test x 0.
