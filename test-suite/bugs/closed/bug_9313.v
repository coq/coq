Set Implicit Arguments.
Existing Class True.

Instance foo1 (a : nat) {b : nat} (e : a = b) : True := I.
Check foo1 (a := 3) (b := 4).

Definition foo2 (a : nat) {b : nat} (e : a = b) : True := I.
Check foo2 (a := 3) (b := 4).

Instance foo3 (a : nat) {b : nat} (e : a = b) : True.
exact I.
Qed.
Check foo3 (a := 3) (b := 4).
