Inductive equal T (x : T) : T -> Type := Equal : equal T x x.

Module bla.

Lemma test n : equal nat n (n + n) -> equal nat (n + n + n) n.
Proof using.
intro H. rewrite <- H. rewrite <- H. exact (Equal nat n).
Qed.

End bla.
