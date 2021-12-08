Module Type Universe.
Parameter U : nat.
End Universe.

Module Univ_prop (Univ : Universe).
Include Univ.
End Univ_prop.

Module Monad (Univ : Universe).
Module UP := (Univ_prop Univ).
End Monad.

Module Rules (Univ:Universe).
Module MP := Monad Univ.
Include MP.
Import UP.
Definition M := UP.U.    (* anomaly here *)
End Rules.
