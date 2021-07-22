Unset Primitive Projections.

(* Definitional classes *don't* support primitive projections. *)
Fail #[projections(primitive)]
Class A := a : nat.

(* Variants *don't* support primitive projections. *)
Fail #[projections(primitive)]
Variant D := .

(* Inductives *don't* support primitive projections. *)
Fail #[projections(primitive)]
Inductive E := .

(* (positive) CoInductives *don't* support primitive projections. *)
Fail #[projections(primitive)]
CoInductive F := .

(* Mutual inductives *don't* support primitive projections. *)
Fail #[projections(primitive)]
Inductive H :=
with I := .
