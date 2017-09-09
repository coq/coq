Set Universe Polymorphism.
Set Printing Universes.
Unset Strict Universe Declaration.

Class Wrap A := wrap : A.

Instance bar@{u} : Wrap@{u} Set. Proof nat.
Print bar.

(* The universes in the binder come first, then the extra universes in
   order of appearance. *)
Definition foo@{u +} := Type -> Type@{v} -> Type@{u}.
Print foo.
