
(** Test of the different syntaxes of SearchAbout, in particular
    with and without the [ ... ] delimiters *)

SearchAbout plus.
SearchAbout plus mult.
SearchAbout "plus_n".
SearchAbout plus "plus_n".
SearchAbout "*".
SearchAbout "*" "+".

SearchAbout plus inside Peano.
SearchAbout plus mult inside Peano.
SearchAbout "plus_n" inside Peano.
SearchAbout plus "plus_n" inside Peano.
SearchAbout "*" inside Peano.
SearchAbout "*" "+" inside Peano.

SearchAbout plus outside Peano Logic.
SearchAbout plus mult outside Peano Logic.
SearchAbout "plus_n" outside Peano Logic.
SearchAbout plus "plus_n" outside Peano Logic.
SearchAbout "*" outside Peano Logic.
SearchAbout "*" "+" outside Peano Logic.

SearchAbout -"*" "+" outside Logic.
SearchAbout -"*"%nat "+"%nat outside Logic.

SearchAbout [plus].
SearchAbout [plus mult].
SearchAbout ["plus_n"].
SearchAbout [plus "plus_n"].
SearchAbout ["*"].
SearchAbout ["*" "+"].

SearchAbout [plus] inside Peano.
SearchAbout [plus mult] inside Peano.
SearchAbout ["plus_n"] inside Peano.
SearchAbout [plus "plus_n"] inside Peano.
SearchAbout ["*"] inside Peano.
SearchAbout ["*" "+"] inside Peano.

SearchAbout [plus] outside Peano Logic.
SearchAbout [plus mult] outside Peano Logic.
SearchAbout ["plus_n"] outside Peano Logic.
SearchAbout [plus "plus_n"] outside Peano Logic.
SearchAbout ["*"] outside Peano Logic.
SearchAbout ["*" "+"] outside Peano Logic.

SearchAbout [-"*" "+"] outside Logic.
SearchAbout [-"*"%nat "+"%nat] outside Logic.


(** The example in the Reference Manual *)

Require Import ZArith.

SearchAbout Z.mul Z.add "distr".
SearchAbout "+"%Z "*"%Z "distr" -positive -Prop.
SearchAbout (?x * _ + ?x * _)%Z outside OmegaLemmas.
