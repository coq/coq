(* Tauto bug initially due to wrong test for binary connective *)

Parameter A B : Type.

Axiom P : A -> B ->  Prop.

Inductive IP (a  : A) (b: B) : Prop :=
| IP_def : P a b ->   IP a b.


Goal forall (a : A) (b : B), IP a b ->  ~ IP a b -> False.
Proof.
  intros.
  tauto.
Qed.


