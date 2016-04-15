Require Import Coq.Bool.Bool Coq.Setoids.Setoid.
Goal forall (P : forall b : bool, b = true -> Type) (x y : bool) (H : andb x y = true) (H' : P _ H), True.
  intros.
  Fail rewrite Bool.andb_true_iff in H.
