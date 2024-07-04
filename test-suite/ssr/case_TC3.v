From Stdlib Require Import ssreflect.

Set Printing All.
Set Debug Ssreflect.

Class Class sort := { op : sort -> bool }.
Arguments op {_ _}.
#[export] Hint Mode Class !.

Lemma opP A (C: Class A) (a: A) : reflect True (op a).
Proof. Admitted.
Arguments op {_ _}.

Section Section.
  Context A B (CA : Class A) (CB : Class B) (a: A).

  Goal is_true (op a).
    by case: opP.
  Abort.

End Section.
