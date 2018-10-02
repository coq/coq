(* Check non-error failure in case of unsupported decidability scheme *)
Local Set Decidable Equality Schemes.

Inductive a := A with b := B.

(* But fails with error if explicitly asked for the scheme *)

Fail Scheme Equality for a.
