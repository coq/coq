
Class E (a b : nat) := e{}.

Class C (a b : nat) := c{}.

Class D (a:nat) := d{}.

Instance d2 : D 2 := {}.

Instance c2 : C 0 2 | 10 := {}.

Instance exy (a b:nat) `{C a b} `{D b} : E a b := {}.

Module Back.
  Instance c0 : C 0 0 | 1 := {}.
  Type _ : E _ _.
End Back.

Module NoBack.
  Type _ : E _ _.
  Instance c0 : C 0 0 ! 1 := {}.
  Fail Type _ : E _ _.
  Type _ : C 0 0.
End NoBack.
