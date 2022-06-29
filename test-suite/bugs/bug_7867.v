(* Was a printer anomaly due to an internal lambda with no binders *)

Class class := { foo : nat }.
Fail #[export] Instance : class := { foo := 0 ; bar := 0 }.
