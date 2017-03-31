Set Universe Polymorphism.
Set Printing Universes.

Class Wrap A := wrap : A.

Instance bar@{u} : Wrap@{u} Set. Proof nat.
Print bar.
