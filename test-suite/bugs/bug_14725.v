From Corelib Require Import Setoid Morphisms.

Axiom T : Type.
Axiom Teq : relation T.
#[local] Declare Instance Teq_Equivalence : Equivalence Teq.

Axiom P : T -> Prop.
Axiom P_Proper : Proper (Teq ==> Basics.flip Basics.impl) P.

(** This is a manually crafted hint which is essentially declaring P_Proper as
    a typeclass instance, except that it builds a proof term that captures the
    marker variable of type [apply_subrelation]. If that variable were to
    escape, the call to rewrite below would fail with a type error. *)
Ltac manual_P_proper :=
match goal with
| [ H : apply_subrelation |- Proper (Teq ==> Basics.flip Basics.impl) P ] =>
  case H; apply P_Proper
end.

#[local] Hint Extern 1 => manual_P_proper : typeclass_instances.

Lemma foo : forall x y : T, Teq x y -> P y -> P x.
Proof.
intros m n e h.
rewrite e.
exact h.
Qed.
