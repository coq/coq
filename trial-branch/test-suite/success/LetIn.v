(* Simple let-in's *)
Definition l1 := let P := 0 in P.
Definition l2 := let P := nat in P.
Definition l3 := let P := True in P.
Definition l4 := let P := Prop in P.
Definition l5 := let P := Type in P.

(* Check casting of let-in *)
Definition l6 := let P := 0:nat in P.
Definition l7 := let P := True:Prop in P.
Definition l8 := let P := True:Type in P.
