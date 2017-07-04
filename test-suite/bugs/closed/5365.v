
Inductive TupleT : nat -> Type :=
| nilT : TupleT 0
| consT {n} A : (A -> TupleT n) -> TupleT (S n).

Inductive Tuple : forall n, TupleT n -> Type :=
  nil : Tuple _ nilT
| cons {n A} (x : A) (F : A -> TupleT n) : Tuple _ (F x) -> Tuple _ (consT A F).

Inductive TupleMap : forall n, TupleT n -> TupleT n -> Type :=
  tmNil : TupleMap _ nilT nilT
| tmCons {n} {A B : Type} (F : A -> TupleT n) (G : B -> TupleT n)
  : (forall x, sigT (fun y => TupleMap _ (F x) (G y))) -> TupleMap _ (consT A F) (consT B G).
