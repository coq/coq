
(** Test of the different syntaxes of Search *)

Search plus.
Search plus mult.
Search "plus_n".
Search plus "plus_n".
Search "*".
Search "*" "+".

Search plus inside Peano.
Search plus mult in Peano.
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
