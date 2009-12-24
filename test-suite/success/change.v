(* A few tests of the syntax of clauses and of the interpretation of change *)

Goal let a := 0+0 in a=a.
intro.
change 0 in (value of a).
change ((fun A:Type => A) nat) in (type of a).
Abort.

Goal forall x, 2 + S x = 1 + S x.
intro. 
change (?u + S x) with (S (u + x)). 
Abort.
