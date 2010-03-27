(* Check injection in presence of dependencies hidden in applicative terms *)

Inductive TupleT : nat -> Type :=
  nilT : TupleT 0
| consT {n} A : (A -> TupleT n) -> TupleT (S n).

Inductive Tuple : forall n, TupleT n -> Type :=
  nil : Tuple _ nilT
| cons {n} A (x : A) (F : A -> TupleT n) : Tuple _ (F x) -> Tuple _ (consT A F).

Goal forall n A F x X n0 A0 x0 F0 H0 (H : existT (fun n0 : nat => {H0 : TupleT
n0 & Tuple n0 H0}) 
         (S n0)
         (existT (fun H0 : TupleT (S n0) => Tuple (S n0) H0) 
            (consT A0 F0) (cons A0 x0 F0 H0)) =
       existT (fun n0 : nat => {H0 : TupleT n0 & Tuple n0 H0}) 
         (S n)
         (existT (fun H0 : TupleT (S n) => Tuple (S n) H0) 
            (consT A F) (cons A x F X))), False.
intros.
injection H.
