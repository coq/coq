
(** Test of the different syntaxes of Search *)

Search plus.
Search plus mult.
Search "plus_n".
Search plus "plus_n".
Search "*".
Search "*" "+".

Search plus inside Peano.
Search plus mult inside Peano.
Search "plus_n" inside Peano.
Search plus "plus_n" inside Peano.
Search "*" inside Peano.
Search "*" "+" inside Peano.

Search plus outside Peano Logic.
Search plus mult outside Peano Logic.
Search "plus_n" outside Peano Logic.
Search plus "plus_n" outside Peano Logic.
Search "*" outside Peano Logic.
Search "*" "+" outside Peano Logic.

Search -"*" "+" outside Logic.
Search -"*"%nat "+"%nat outside Logic.


(** The example in the Reference Manual *)

Require Import ZArith.

Search Z.mul Z.add "distr".
Search "+"%Z "*"%Z "distr" -positive -Prop.
Search (?x * _ + ?x * _)%Z outside Lia.
