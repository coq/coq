(* Check correct handling of unsupported notations *)
Notation "''" := (fun x => x) (at level 20).
Definition crash_the_rooster f := .
