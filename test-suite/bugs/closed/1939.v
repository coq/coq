Require Import Setoid Program.Basics.

 Parameter P : nat -> Prop.
 Parameter R : nat -> nat -> Prop.

 Add Parametric Morphism : P
   with signature R ++> impl as PM1.
 Admitted.

 Add Parametric Morphism : P
   with signature R --> impl as PM2.
 Admitted.

 Goal forall x y, R x y -> P y -> P x.
 Proof.
   intros x y H1 H2.
   rewrite H1.
   auto.
 Qed.
