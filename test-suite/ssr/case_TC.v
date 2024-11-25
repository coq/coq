From Corelib Require Import ssreflect.
From Corelib Require Import ssrbool.

Set Printing All.
Set Debug Ssreflect.

Class Class := { sort : Type ; op : sort -> bool }.
Coercion sort : Class >-> Sortclass.
Arguments op [_] _.

Section Section.
  Context (A B: Class) (a: A).

  Goal op a || ~~ op a.
    by case: op.
  Abort.

End Section.
