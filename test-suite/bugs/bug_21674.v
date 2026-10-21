Polymorphic Axiom foo@{u} : nat -> Prop.

Axiom bar : forall n, foo n.

Goal foo 0.
  Succeed simple apply bar.
  apply bar.
Qed.


Require Import Corelib.Array.PrimArray.


Axiom P : forall A t i (a:A), get t i = a.
Axiom Q : forall A a i, @length@{length.u0} A a = i.

Lemma test : forall A a i, @length@{P.u0} A a = i.
Proof.
  intros A a i.
  Succeed refine (Q _ _ _).
  Succeed simple eapply Q.
  eapply Q.
Qed.

(* With irrelevance, this succeeds *)
Definition should_work@{u v|} : length@{u} [| | 0 |] = length@{v} [| | 0 |]
  := eq_refl.
(* Universe constraints are not implied by the ones declared: u = v *)
