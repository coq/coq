(* Check correct handling of unsupported notations *)
Notation "''" := (fun x => x) (at level 20).

(* This fails with a syntax error but it is not caught by Fail
Fail Definition crash_the_rooster f := .
*)
