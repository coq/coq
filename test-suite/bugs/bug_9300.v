Existing Class True.

Instance foo {n : nat} (x := I) : forall {b : bool} (s : nat * nat), True. auto. Defined.

Fail Check foo (n := 3) true (s := (4 , 5)).
Check foo (n := 3) (b := true) (4 , 5).
