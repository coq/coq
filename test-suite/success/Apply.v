
(* This needs unification on type *)

Goal (n,m:nat)(eq nat (S m) (S n)).
Intros.
Apply f_equal.

(* f_equal : (A,B:Set; f:(A->B); x,y:A)x=y->(f x)=(f y) *)
(* and A cannot be deduced from the goal but only from the type of f, x or y *)