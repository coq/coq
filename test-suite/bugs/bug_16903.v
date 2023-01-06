Definition pull_match_bool_dep {A B} (P : forall b : bool, A b -> B b) (a : A true) (a' : A false)
           (b : bool)
: P b (if b as b return A b then a else a') =
  if b as b return B b then P _ a else P _ a'
  := match b with true => eq_refl | false => eq_refl end.
