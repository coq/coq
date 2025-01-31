Require Import PrimArray.
Require Import PrimInt63.
Axiom F : unit -> unit.

Goal forall g1, exists st, get (make 1 (F g1)) 0 = F st.
Proof.
  intros.
  eexists _.
  Succeed lazy [make]; reflexivity.
  Succeed lazy [make]; refine eq_refl.
Abort.

Goal forall g1, exists st, get (make 1 (F g1)) 0 = F st.
Proof.
  intros.
  eexists _.
  Succeed reflexivity.
  Succeed refine eq_refl.
Abort.
