Set Universe Polymorphism.
Set Printing Universes.

Class Wrap A := wrap : A.

Instance bar@{u} : Wrap@{u} Set. Proof. exact nat. Qed.
Print bar.
