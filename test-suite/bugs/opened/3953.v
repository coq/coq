Goal forall (a b : unit), a = b -> exists c, b = c.
intros.
eexists.
Fail subst.
