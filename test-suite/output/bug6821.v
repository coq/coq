(* Was failing at printing time with stack overflow due to an infinite
   eta-expansion *)

Notation "x 'where' y .. z := v " :=
  ((fun y => .. ((fun z => x) v) ..) v)
  (at level 11, v at next level, y binder, z binder).

Check forall f, f x where x := 1.
