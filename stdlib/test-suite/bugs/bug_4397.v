From Stdlib Require Import Equality.
Theorem foo (u : unit) (H : u = u) : True.
dependent destruction H.
Abort.
