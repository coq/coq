From Stdlib Require Import ssreflect.

Set Printing All.
Set Debug Ssreflect.

Class Class := { sort : Type ; op : sort -> bool }.
Coercion sort : Class >-> Sortclass.
Arguments op [_] _.

Lemma opP (A: Class) (a: A) : reflect True (op a).
Proof. Admitted.

Section Section.
  Context (A B: Class) (a: A).

  Goal is_true (op a).
    by case: opP.
  Abort.

End Section.
