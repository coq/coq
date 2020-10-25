(* Support for eta *)

Theorem g (f:nat->nat) : f = fun a => f a.
cbv eta.
match goal with |- f = f => idtac end.
Abort.
