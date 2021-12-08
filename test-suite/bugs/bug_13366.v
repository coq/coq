Class Functor (F : Type -> Type) : Type :=
  fmap : F nat.

Fail Definition blah := sum fmap.
(* used to be anomaly not an arity *)
