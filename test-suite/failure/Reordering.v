(* Testing that hypothesis order (following a conversion/folding) is checked *)

Goal forall (A:Set) (x:A) (A':=A), True.
intros.
Fail change ((fun (_:A') => Set) x) in (type of A).
