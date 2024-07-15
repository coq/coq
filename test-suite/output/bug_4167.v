Class test {y x: nat} : Set := { foo: nat }.
Parameter (x y:nat) (t1 t2: @ test x y).
Existing Instance t1.
Existing Instance t2.
Check t1.(foo) = t2.(foo).
Set Printing Projections.
Check t1.(foo) = t2.(foo).
