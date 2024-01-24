Require Import Ltac2.Ltac2.

#[projections(primitive)]
Record r (n : nat) := { w : Prop -> Prop -> Prop }.

Class C (P : Prop) := {}.

Goal forall (v : r 0) (Q P : Prop), C (v.(w _) P Q).
Proof.
  intros.

  #[local] Opaque w.

  lazy_match! goal with
  | [ |- ?g ] =>
      let t := constr:(w 0) in
      let t := constr:(C ($t v P Q)) in
      Unification.unify (TransparentState.current ()) g t
  end.
Abort.
