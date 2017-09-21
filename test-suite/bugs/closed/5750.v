(* Check printability of the hole of the context *)
Goal 0 = 0.
match goal with |- context c [0] => idtac c end.
