Set Universe Polymorphism.

Axiom X : Type.
(* Used to declare [x0@{u1 u2} : X@{u1}] and [x1@{} : X@{u2}] leaving
   the type of x1 with undeclared universes. After PR #891 this should
   error at declaration time. *)
Axiom x₀ x₁ : X.
Axiom Xᵢ : X -> Type.

Check Xᵢ x₁. (* conversion test raised anomaly universe undefined *)
