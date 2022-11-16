Set Universe Polymorphism.

Axiom F : False. (* This is just used to cut the below proof short while still being able to write Qed *)

Theorem test : forall (U1 U2 : Type) (eq1 eq2 : U1 = U2), eq1 = eq2.
Proof.
    intros U1 U2 eq1 eq2.
    subst U2.
    destruct F.
Qed.
