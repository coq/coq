Require Import Corelib.Program.Tactics.
Set Universe Polymorphism.
Set Printing Universes.
Definition typ := Type.
Set Debug "univMinim".
Program Definition foo : typ := _ -> _.
Next Obligation. Show Universes. Admitted.
Next Obligation. exact typ. Show Proof. Show Universes. Defined.
