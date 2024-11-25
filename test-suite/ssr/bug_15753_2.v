Require Import Corelib.ssr.ssreflect.

Class FromPureT (φ : Type) :=
  from_pureT : exists ψ : Prop, φ = ψ.

Lemma into_forall_impl_pure φ : FromPureT φ -> φ -> True.
Proof.
  rewrite /FromPureT => -[φ' ->].
  constructor.
Qed.
