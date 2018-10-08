(* While waiting for support, check at least that it does not raise an anomaly *)

Inductive ctype :=
| Struct: list ctype -> ctype
| Bot : ctype.

Fail Scheme Equality for ctype.
