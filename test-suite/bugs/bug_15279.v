
Require Setoid.
Require Import CMorphisms.

Axiom Formula : Type.

Inductive Hil : (Formula -> Type) -> Type :=
| ax {Γ} : Hil Γ.

Axiom SetEq : (Formula -> Type) -> (Formula -> Type) -> Type.
#[global]
Instance Hil_mor : Proper (SetEq ==> iffT) Hil.
Proof.
Admitted.

Axiom L R : Formula -> Type.
Axiom Union_Add_r : SetEq L R.
Goal Hil L.
  rewrite Union_Add_r.
Admitted.
