Module Test1.

Set Printing Parentheses.

Check (1+2*3,4,5).
Print mult_n_Sm.

End Test1.

Require Import TestSuite.list.

Module Test2.

Set Printing Parentheses.

Import ListNotations.
Check [1;2;3;4].

Check {0=1}+{2<=4+5}.

End Test2.

(* A test with custom entries *)

Module CustomEntry.

Declare Custom Entry myconstr.

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "x + y" := (Nat.add x y) (in custom myconstr at level 5, right associativity).
Notation "( x )" := x (in custom myconstr at level 0).
Notation "x" := x (in custom myconstr at level 0, x ident).

Unset Printing Parentheses.
Check forall x y z : nat, [ (x + y) + z ] = [ x + (y + z) ].
Set Printing Parentheses.
Check forall x y z : nat, [ (x + y) + z ] = [ x + (y + z) ].

End CustomEntry.
