Goal forall A B C (p : forall (x : A) (y : B), C x y) (x : A) (y : B), True.
Proof.
  intros A B C p x y.
  match type of p with
    | forall x y, @?F x y => pose F as C1
  end.
  match type of p with
    | forall x y, @?F y x => pose F as C2
  end.
  assert (C1 x y) as ?.
  assert (C2 y x) as ?.
Abort.

Goal forall A B C D (p : forall (x : A) (y : B) (z : C), D x y) (x : A) (y : B), True.
Proof.
  intros A B C D p x y.
  match type of p with
    | forall x y z, @?F x y => pose F as C1
  end.
  assert (C1 x y) as ?.
Abort.

Goal forall A B C D (p : forall (z : C) (x : A) (y : B), D x y) (x : A) (y : B), True.
Proof.
  intros A B C D p x y.
  match type of p with
    | forall z x y, @?F x y => pose F as C1
  end.
  assert (C1 x y) as ?.
Abort.

(** Those should fail *)

Goal forall A B C (p : forall (x : A) (y : B), C x y) (x : A) (y : B), True.
Proof.
  intros A B C p x y.
  Fail match type of p with
    | forall x, @?F x y => pose F as C1
  end.
  Fail match type of p with
    | forall x y, @?F x x y => pose F as C1
  end.
  Fail match type of p with
    | forall x y, @?F x => pose F as C1
  end.
Abort.

(** This one is badly typed *)

Goal forall A (B : A -> Type) (C : forall x, B x -> Type), (forall x y, C x y) -> True.
Proof.
intros A B C p.
Fail match type of p with
| forall x y, @?F y x => idtac
end.
Abort.

Goal forall A (B : A -> Type) (C : Type) (D : forall x, B x -> Type), (forall x (z : C) y, D x y) -> True.
Proof.
intros A B C D p.
match type of p with
| forall x z y, @?F x y => idtac
end.
Abort.
