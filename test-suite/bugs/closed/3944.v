Require Import Setoid.
Definition C (T : Type) := T.
Goal forall T (i : C T) (v : T), True.
Proof.
Fail setoid_rewrite plus_n_Sm.
