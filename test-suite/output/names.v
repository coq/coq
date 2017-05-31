(* Test no clash names occur *)
(* see bug #2723 *)

Parameter a : forall x, {y:nat|x=y}.
Fail Definition b y : {x:nat|x=y} := a y.

Goal (forall n m, n <= m -> m <= n -> n = m) -> True.
intro H; epose proof (H _ 3) as H.
Show.
