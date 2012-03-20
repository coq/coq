(* Test no clash names occur *)
(* see bug #2723 *)

Parameter a : forall x, {y:nat|x=y}.
Fail Definition b y : {x:nat|x=y} := a y.
