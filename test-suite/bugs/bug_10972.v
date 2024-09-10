(* Check rewrite_strat is compatible with Ltac *)
Require Import Stdlib.Setoids.Setoid.
Module foo.
  Definition Foo := True.
  Ltac foo := rewrite_strat eval cbv [Foo].
End foo.
Goal foo.Foo.
  foo.foo.
Abort.
