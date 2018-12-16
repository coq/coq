(* There was a problem of freshness with Infix choice of vars *)

(* In particular, x and y were special... *)

Infix "#" := (fun x y => x + y) (at level 50, left associativity).
Check (3 # 5).
