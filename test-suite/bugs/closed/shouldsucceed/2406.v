(* Check correct handling of unsupported notations *)
Fail Notation "''" := (fun x => C) (at level 20).
Fail Definition crash_the_rooster f := . 
