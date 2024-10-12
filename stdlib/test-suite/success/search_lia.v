(** The example in the Reference Manual *)

Require Import ZArith.

Search Z.mul Z.add "distr".
Search "+"%Z "*"%Z "distr" -positive -Prop.
Search (?x * _ + ?x * _)%Z outside Lia.
