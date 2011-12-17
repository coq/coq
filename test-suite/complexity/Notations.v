(* Last line should not loop, even in the presence of eta-expansion in the *)
(* printing mechanism *)
(* Expected time < 1.00s *)

Notation "'bind' x <- y ; z" :=(y (fun x => z)) (at level 99, x at
  level 0, y at level 0,format "'[hv' 'bind'  x  <-  y ;  '/' z ']'").

Definition f (g : (nat -> nat) -> nat) := g (fun x => 0).

Time Check (fun g => f g).
