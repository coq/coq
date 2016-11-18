(*Suppose we have*)

  Inductive my_if {A B} : bool -> Type :=
  | then_case (_ : A) : my_if true
  | else_case (_ : B) : my_if false.
  Notation "'If' b 'Then' A 'Else' B" := (@my_if A B b) (at level 10).

(*then here are three inductive type declarations that work:*)

  Inductive I1 :=
  | i1 (x : I1).
  Inductive I2 :=
  | i2 (x : nat).
  Inductive I3 :=
  | i3 (b : bool) (x : If b Then I3 Else nat).

(*and here is one that does not, despite being equivalent to [I3]:*)

  Fail Inductive I4 :=
  | i4 (b : bool) (x : if b then I4 else nat). (* Error: Non strictly positive occurrence of "I4" in
   "forall b : bool, (if b then I4 else nat) -> I4". *)

(*I think this one should work.  I believe this is a conservative extension over CIC: Since [match] statements returning types can always be re-encoded as inductive type families, the analysis should be independent of whether the constructor uses an inductive or a [match] statement.*)
