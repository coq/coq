Unset Primitive Projections.

(* Classes *do* support primitive projections. *)
#[projections(primitive)]
Class B := { b : nat ; }.
About B.

(* Structures *do* support primitive projections. *)
#[projections(primitive)]
Structure C := { c : nat ; }.
About C.

(* (negative) CoInductives *do* support primitive projections. *)
#[projections(primitive)]
CoInductive G := { g : G }.
About G.
