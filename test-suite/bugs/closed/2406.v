(* Check correct handling of unsupported notations *)
Notation "''" := (fun x => x) (at level 20).
Fail Definition crash_the_rooster f := .
