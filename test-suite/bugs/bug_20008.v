Set Primitive Projections.

Record R A := mk { p : A -> A -> A }.

Arguments mk {_} _.
Arguments p {_} _ !_ !_.

(* using nat *)

Goal forall x, p (mk (fun _ _ => 2)) x x = 0.
Proof.
  Fail progress cbn.
Abort.

Goal forall x, p (mk (fun _ _ => 2)) 3 x = 0.
Proof.
  Fail progress cbn.
Abort.

Goal p (mk (fun _ _ => 2)) 3 4 = 0.
Proof.
  progress cbn.
Abort.

Arguments p {_} _ !_ _.

Goal forall x, p (mk (fun _ _ => 2)) x x = 0.
Proof.
  Fail progress cbn.
Abort.

Goal forall x, p (mk (fun _ _ => 2)) 3 x = 0.
Proof.
  progress cbn.
Abort.

Goal forall x, p (mk (fun _ _ => 2)) x 4 = 0.
Proof.
  Fail progress cbn.
Abort.

Goal p (mk (fun _ _ => 2)) 3 4 = 0.
Proof.
  progress cbn.
Abort.

(* using prim int *)
Require Import PrimInt63.

Open Scope int63_scope.

Arguments p {_} _ !_ !_.

Goal forall x, p (mk (fun _ _ => 2)) x x = 0.
Proof.
  intros x. Check x : int. (* sanity check that the scope is correct *)
  Fail progress cbn.
Abort.

Goal forall x, p (mk (fun _ _ => 2)) 3 x = 0.
Proof.
  Fail progress cbn.
Abort.

Goal p (mk (fun _ _ => 2)) 3 4 = 0.
Proof.
  progress cbn.
Abort.

Arguments p {_} _ !_ _.

Goal forall x, p (mk (fun _ _ => 2)) x x = 0.
Proof.
  Fail progress cbn.
Abort.

Goal forall x, p (mk (fun _ _ => 2)) 3 x = 0.
Proof.
  progress cbn.
Abort.

Goal forall x, p (mk (fun _ _ => 2)) x 4 = 0.
Proof.
  Fail progress cbn.
Abort.

Goal p (mk (fun _ _ => 2)) 3 4 = 0.
Proof.
  progress cbn.
Abort.
