(* Test visibility of imported objects *)

Require Import make_local.

(* Check local implicit arguments are not imported *)

Check (f nat 0).

(* Check local arguments scopes are not imported *)

Check (f nat (0*0)).
