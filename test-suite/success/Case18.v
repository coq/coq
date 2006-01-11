(* Check or-patterns *)

Definition g x :=
  match x with ((((1 as x),_) | (_,x)), (_,(2 as y))|(y,_)) => (x,y) end.

Eval compute in (g ((1,2),(3,4))).
(* (1,3) *)

Eval compute in (g ((1,4),(3,2))).
(* (1,2) *)

