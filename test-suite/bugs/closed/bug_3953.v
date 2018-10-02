(* Checking subst on instances of evars (was bugged in 8.5 beta 1) *)
Goal forall (a b : unit), a = b -> exists c, b = c.
  intros.
  eexists.
  subst.
