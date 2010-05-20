Inductive V: nat -> Type := VS n: V (S n).
Definition f (e: V 1): nat := match e with VS 0 => 3 end.

