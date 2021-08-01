Set Primitive Projections.
Record Box (A B:nat) := box { unbox : nat }.
Coercion unbox : nat >-> Funclass.
Check (0 0).
