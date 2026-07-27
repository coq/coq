(* Printing Sort Quality Variables Anonymously: sort quality variables
   that have no name print as "_" (which parses back, denoting a fresh
   quality variable) instead of their raw α-names (which do not). *)
Set Universe Polymorphism.
Definition idT@{s;u} (A : Type@{s;u}) (a : A) := a.

(* Under Printing Universes, the fresh quality variable of the
   instance (and of the displayed sort) prints as a raw α-name by
   default... *)
Set Printing Universes.
Check idT.
(* ...and as _ under the flag. *)
Set Printing Sort Quality Variables Anonymously.
Check idT.
Unset Printing Universes.

(* Named quality variables are unaffected: the binder name is kept. *)
Print idT.
About idT.

Unset Printing Sort Quality Variables Anonymously.

(* The anonymous form parses back: "_" is accepted as the sort quality
   of a sort annotation (it was already accepted in universe
   instances), denoting a fresh quality variable. *)
Check Type@{_ ; Set}.
Check idT@{_ ; Set}.
