Module N.
Definition f:=plus.
Syntax constr level 7: plus [ (f $n $m)] -> [ $n:L "+" $m:E].
Check (f O O).
End N.
Check (N.f O O).
Import N.
Check (N.f O O).
Check (f O O).
Module M:=N.
Check (f O O).
Check (N.f O O).
Import M.
Check (f O O).
Check (N.f O O).
