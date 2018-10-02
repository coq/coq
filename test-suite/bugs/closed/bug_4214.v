(* Check that subst uses all equations around *)
Goal forall A (a b c : A), b = a -> b = c -> a = c.
intros.
subst.
reflexivity.
Qed.
