(* Check that the nested inductive types positivity check avoids recursively
   non uniform parameters (at least if these parameters break positivity) *)

Inductive t (A:Type) : Type := c : t (A -> A) -> t A.
Inductive u : Type := d : u | e : t u -> u.
