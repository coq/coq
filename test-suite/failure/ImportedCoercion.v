(* Test visibility of coercions *)

Require Import make_local.

(* Local coercion must not be used *)

Check (0 = true).
