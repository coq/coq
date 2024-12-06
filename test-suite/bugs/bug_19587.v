Require Import Corelib.Setoids.Setoid Corelib.Classes.Morphisms.

Class ring α := { rng_zero : α; }.
Class field := { }.

Parameter lap_eq : forall {α} {r : ring α}, list α -> list α -> Prop.

Declare Instance lap_eq_equiv : forall {α} {r : ring α}, Equivalence lap_eq.

Axiom lap_eq_0 : forall (α : Type) (r : ring α), lap_eq (cons rng_zero nil) nil.

Definition puiseux_series (α : Type) := nat -> α.

Definition ps_zero {α} {r : ring α} : puiseux_series α := fun i => rng_zero.

Definition ps_ring α (R : ring α) (K : field) : ring (puiseux_series α) :=
  {| rng_zero := ps_zero; |}.

Canonical Structure ps_ring.

Theorem glop : forall
  (α : Type) (R : ring α) (K : field),
  @lap_eq (puiseux_series α) (@ps_ring α R K)
     (@cons (puiseux_series α) (@ps_zero α R) (@nil (puiseux_series α)))
     nil.
Proof.
intros.
Check 1%nat.
rewrite lap_eq_0.
Check 1%nat.
Abort.
