#[projections(primitive=yes)]
Inductive AccS [A : Type] (R : A -> A -> Prop) (x : A) : SProp :=
  AccS_intro
    { AccS_inv : forall y : A, R y x -> AccS R y }.

Fail Fixpoint test [A : Type] (R : A -> A -> Prop) (x : A) (H : forall x, R x x) a {struct a} : nat :=
  test R x H (AccS_inv R x a x (H x)).

#[projections(primitive=no)]
Inductive AccS' [A : Type] (R : A -> A -> Prop) (x : A) : SProp :=
  AccS_intro'
    { AccS_inv' : forall y : A, R y x -> AccS' R y }.
