(* Printing Unnamed Universes Anonymously: sort quality variables and
   universe levels that have no name print as "_" (which parses back,
   denoting a fresh variable) instead of their raw forms (which do
   not). *)
Set Universe Polymorphism.
Definition idT@{s;u} (A : Type@{s;u}) (a : A) := a.

(* Under Printing Universes, the fresh quality variable and the fresh
   level of the instance (and of the displayed sort) print in raw form
   by default... *)
Set Printing Universes.
Check idT.
(* ...and as _ under the flag. *)
Set Printing Unnamed Universes Anonymously.
Check idT.
(* Named levels are unaffected, whether declared or derived from a
   monomorphic definition. *)
Unset Universe Polymorphism.
Universe u.
Check Type@{u}.
Definition foo := Type.
Check foo.
(* A max mixing named and unnamed levels has no "_" for one component,
   so the whole sort prints as _. *)
Check (Type@{u} * Type)%type.
Set Universe Polymorphism.
Unset Printing Universes.

(* Named quality variables are unaffected: the binder name is kept. *)
Print idT.
About idT.

Unset Printing Unnamed Universes Anonymously.

(* The anonymous form parses back: "_" is accepted as the sort quality
   of a sort annotation (it was already accepted in universe
   instances), denoting a fresh quality variable. *)
Check Type@{_ ; Set}.
Check idT@{_ ; Set}.
