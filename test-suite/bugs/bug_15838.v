Module Type S.

Unset Elimination Schemes.

Inductive T (A : Type) : Type := box : A -> T A.

End S.

Module F (X : S).

Definition unbox {A} (x : X.T A) : A :=
match x with X.box _ x => x end.

End F.

Module M.

Inductive T (A : Type) : Prop := box : A -> T A.

End M.

Fail Module N := F(M).
