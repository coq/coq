Mod N.
  Definition f:=plus.
  Syntax constr level 7: plus [ (f $n $m)] -> [ $n:L "+" $m:E].
  Check (f O O).
EndM N.

Check (N.f O O).

Imp N.

Check (N.f O O).

Check (f O O).

Mod M:=N.

Check (f O O).

Check (N.f O O).

Check (M.f O O).

Imp M.

Check (f O O).

Check (N.f O O).
