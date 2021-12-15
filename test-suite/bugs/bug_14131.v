Set Implicit Arguments.
Unset Elimination Schemes.

Inductive JMeq (A:Type) (x:A) : forall B:Type, B -> Prop :=
    JMeq_refl : JMeq x x.

Set Elimination Schemes.

Register JMeq as core.JMeq.type.

Axiom JMeq_ind : forall (A:Type) (x:A) (P:A -> Prop),
  P x -> forall y, JMeq x y -> P y.

Register JMeq_ind as core.JMeq.ind.

Lemma JMeq_ind_r : forall (A:Type) (x:A) (P:A -> Prop),
   P x -> forall y, JMeq y x -> P y.
Proof. intros. try rewrite H0.
Abort.
