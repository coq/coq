From Stdlib Require Import BinInt.
From Stdlib Require Import RelationClasses.

Axiom mod_mod : forall a b : Z, Z.modulo (Z.modulo b a) a = Z.modulo b a.

#[global] Hint Rewrite Z.add_0_r mod_mod : bu.

Definition modEq (d:Z) := fun (a b :Z)=> Z.modulo a d = Z.modulo b d.

#[global] Instance modEqR (d:Z): Reflexive  (modEq d). Admitted.
#[global] Instance modEqT (d:Z): Transitive (modEq d). Admitted.

Lemma foo d a e : (a mod d)%Z = e -> Z.modulo (Z.modulo a d + 0) d = e.
Proof.
  intro H.
  rewrite_strat try (bottomup (hints bu)). (* Should not fail. *)
  exact H.
Qed.
