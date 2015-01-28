Require Import Setoid.
Class C (T : Type) := c : T.
Goal forall T (i : C T) (v : T), True.
setoid_rewrite plus_n_Sm.
