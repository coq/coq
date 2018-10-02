Module Type Interface.
  Parameter error: nat.
End Interface.

Module Implementation <: Interface.
  Definition t := bool.
  Definition error: t := false.
Fail End Implementation.
(* A UserError here is expected, not an uncaught Not_found *)
