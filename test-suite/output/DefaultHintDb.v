Print Table Default HintDb.

Fail Set Default HintDb "foo".

Goal forall x y, S x = S y -> x = y.
progress auto.
Qed.

Module Foo.

Create HintDb foo.

Set Default HintDb "foo".

Print Table Default HintDb.

Goal forall x y, S x = S y -> x = y.
Fail progress auto.
Abort.

End Foo.

Print Table Default HintDb.

Goal forall x y, S x = S y -> x = y.
progress auto.
Qed.

Unset Default HintDb.

Goal forall x y, S x = S y -> x = y.
Fail progress auto.
Abort.

Set Default HintDb "core".

Definition foo : nat := 5.

Succeed #[local] Hint Resolve foo.

Unset Default HintDb.

Fail #[local] Hint Resolve foo.
