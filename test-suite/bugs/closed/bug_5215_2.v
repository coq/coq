Require Import Coq.Program.Tactics.
Set Universe Polymorphism.
Set Printing Universes.
Definition typ := Type.

Program Definition foo : typ := _ -> _.
Next Obligation. Admitted.
Next Obligation. exact typ. Show Proof. Show Universes. Defined.
