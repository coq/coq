From Corelib Require Import Force.

Set Universe Polymorphism.
Set Primitive Projections.

Record Carrier := { carrier_type : Type }.
Definition sensitive_type := 1 + 1 = 2.
Definition concrete_carrier := {| carrier_type := sensitive_type |}.
Definition seal_carrier@{u u1} (C : Carrier@{u}) :
    Blocked@{Type;u1} Type@{u} :=
  __block@{Type;u1} Type@{u} (carrier_type C).

(* Reifying this block used to enter the primitive projection despite its
   identity mode, expose the captured record, and normalize its field. In
   applications with a large concrete BI carrier this exhausted memory.
   The protected payload must retain both the projection and its argument. *)
Goal True.
Proof.
  let c := constr:(seal_carrier concrete_carrier) in
  let reduced := eval lazy head in c in
  let unfolded := eval unfold seal_carrier in c in
  let reference := eval cbv beta in unfolded in
  constr_eq reduced reference.
  exact I.
Qed.
