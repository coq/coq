Set Definitional UIP.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive eqn {A : Type} (x : A) : A -> SProp := refl : @eqn A x x.

Definition Rw {A B : Type} (e : eqn A B) (x : A) : B := match e with | refl _ => x end.

Definition F (A : Type) (P : A -> Type) (Q1 : forall x, P x): SProp.
Proof.
refine (eqn Q1 _).
intro a.
refine (Rw _ (Q1 a)).
reflexivity.
Defined.

Record BTy : Type := {
  typL : Type;
  typP : typL -> Type;
  typQ : forall x, typP x;
  eps : @F typL typP typQ;
}.
(* Anomaly "Uncaught exception Invalid_argument("index out of bounds")." *)
