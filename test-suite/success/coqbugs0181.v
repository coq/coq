
(* test the strength of pretyping unification *)

Require PolyList.
Definition listn := [A,n] {l:(list A)|(length l)=n}.
Definition make_ln [A,n;l:(list A); h:([l](length l)=n l)] :=
  (exist ?? l h).
