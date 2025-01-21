Module Type T.
End T.

Module FOO (ARG: T).
 Module INNER := ARG.
End FOO.

Module Type Typ.
  Parameter t : Type.
End Typ.

Module Update (E:Typ).
Include E.
End Update.

(** This module generates a non-trivial domain substitution of the
    δ-resolver associated to FOO. *)
Module Make (X: Typ).
 Module MyX := Update X.
 Module BAR := FOO MyX.
End Make.
