(* Destructuring let with the wrong number of variables should name the
   destructured term and its type (#7833). *)

Definition point2d : Type := nat * nat.

Fail Definition abs (p : point2d) : nat :=
  let (x, y, z) := p in x * x + y * y + z * z.

Fail Definition proj1 (p : point2d) : nat :=
  let (x) := p in x.

Inductive box : Type := Box : nat -> box.

Fail Definition unbox (b : box) : nat :=
  let (x, y) := b in x.
