Inductive I : Set :=
  | A : nat -> nat -> I
  | B : nat -> nat -> I.

Definition foo1 (x:I) : nat :=
  match x with
    | A a b | B a b => S b
  end.

Definition foo2 (x:I) : nat :=
  match x with
    | A _ b | B b _ => S b
  end.

Definition foo (x:I) : nat :=
  match x with
    | A a b | B b a => S b
  end.
