Class test {y x: nat} : Set := { foo: nat }.
Context (x y:nat) (t1 t2: @ test x y).
Check t1.(foo) = t2.(foo).
Set Printing Projections.
Check t1.(foo) = t2.(foo).
