
Definition point2d : Type := nat * nat.

(** Error: Destructing let on this type expects 2 variables *)
Definition abs (p: point2d): nat :=
  let (x, y, z) := p in x * x + y * y + z * z.
