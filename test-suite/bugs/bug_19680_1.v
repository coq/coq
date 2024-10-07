Axiom admit : False.

Record CSetoid : Type := makeCSetoid {cs_crr :> Type}.

Inductive QposInf : Set :=
| Qpos2QposInf : QposInf
| QposInfinity : QposInf.

Axiom is_RegularFunction : forall {X:Type} (x:QposInf -> X), Prop.

Record Complete (X:Type) : Type := {approximate : QposInf -> X ;regFun_prf : is_RegularFunction approximate }.

Axiom Q_as_MetricSpace : Type.

Definition CR : Type := Complete Q_as_MetricSpace.

Axiom inject_Q_CR : CR.
Definition CRasCSetoid : CSetoid := makeCSetoid CR.

Goal forall (f : nat -> CRasCSetoid) (Hf : nat), Complete (Complete Q_as_MetricSpace).
Proof.
intros f Hf.
exists (fun e:QposInf => match e with | QposInfinity => inject_Q_CR
 | Qpos2QposInf => let n := Hf in f n end).
elim admit.
Qed. (* Anomaly here *)
