(* Simple let-in's *)
Definition l1 := [P := O]P.
Definition l2 := [P := nat]P.
Definition l3 := [P := True]P.
Definition l4 := [P := Prop]P.
Definition l5 := [P := Type]P.

(* Check casting of let-in *)
Definition l6 := [P := O : nat]P.
Definition l7 := [P := True : Prop]P.
Definition l8 := [P := True : Type]P.
