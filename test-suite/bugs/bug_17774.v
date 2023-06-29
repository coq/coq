Require Import Ltac2.Ltac2.

#[projections(primitive)]
Record r (n : nat) := { w : Prop -> Prop -> Prop }.

Class C (P : Prop) := {}.

Import Printf.
Set Printing Primitive Projection Parameters.

Goal forall (v : r 0) (Q P : Prop), C (v.(w _) P Q).
Proof.
  intros.

  (* Succeeds before and after #17788. *)
  Succeed lazy_match! goal with
  | [ |- ?g ] =>
      let t := open_constr:(C (v.(w _) _ _)) in
      Unification.unify (TransparentState.current ()) g t
  end.

  #[local] Opaque w.

  (* Succeeds only after #17788. *)
  Succeed lazy_match! goal with
  | [ |- ?g ] =>
      let t := open_constr:(C (v.(w _) _ _)) in
      Unification.unify (TransparentState.current ()) g t
  end.

  (* Succeeds only after #17788. *)
  Succeed lazy_match! goal with
  | [ |- ?g ] =>
      let t := open_constr:(w _) in
      let t := open_constr:(C ($t v _ _)) in
      (*printf "Term: %t" t;*)
      Unification.unify (TransparentState.current ()) g t
  end.

  (* Succeeds only after #17788. *)
  Succeed lazy_match! goal with
  | [ |- ?g ] =>
      let t := open_constr:(w _) in
      let t := open_constr:(C ($t v _ _)) in
      (*printf "Term: %t" t;*)
      Unification.unify (TransparentState.current ()) g t
  end.
Abort.
