Fail Fixpoint F (u : unit) : Prop :=
  (fun p : {P : Prop & _} => match p with existT _ _ P => P end)
  (existT (fun P => False -> P) (F tt) _).
(* Anomaly: A universe comparison can only happen between variables.
Please report. *)



Definition g (x : Prop) := x.

Definition h (y : Type) := y.

Definition eq_hf : h = g :> (Prop -> Type) :=
  @eq_refl (Prop -> Type) g.

Set Printing All.
Set Printing Universes.
Fail Definition eq_hf : h = g :> (Prop -> Type) :=
  eq_refl g.
(* Originally an anomaly, now says
Toplevel input, characters 48-57:
Error:
The term "@eq_refl (forall _ : Prop, Prop) g" has type
 "@eq (forall _ : Prop, Prop) g g" while it is expected to have type
 "@eq (forall _ : Prop, Type (* Top.16 *)) (fun y : Prop => h y) g"
(Universe inconsistency: Cannot enforce Prop = Top.16)). *)
