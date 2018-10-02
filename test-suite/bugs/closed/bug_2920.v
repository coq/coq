Fail Definition my_f_equal {A B : Type} (f : A -> B) (a a' : A) (p : a = a') : f a = f a' :=
  eq_ind _ _ (fun a' => f a = f a') _ _ p.
