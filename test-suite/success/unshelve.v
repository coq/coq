Axiom F : forall (b : bool), b = true ->
  forall (i : unit), i = i -> True.

Goal True.
Proof.
unshelve (refine (F _ _ _ _)).
+ exact true.
+ exact tt.
+ exact (@eq_refl bool true).
+ exact (@eq_refl unit tt).
Qed.
