(* Used in Notation.v to test import of notations from files in sections *)

Notation "'Z'" := O (at level 9).
Notation plus := plus.
Notation succ := S.
Notation mult := mult (only parsing).
Notation less := le (only parsing).

(* Test bug 2168: ending section of some name was removing objects of the
   same name *)

Notation add2 n:=(S n).
Section add2.
End add2.

