
Class Equiv A := equiv: A -> A -> Prop.
Hint Mode Equiv ! : typeclass_instances.

Class Lookup (K A M : Type) := lookup: K -> M -> option A.
Hint Mode Lookup ! - - : typeclass_instances.
Hint Mode Lookup - - ! : typeclass_instances.

Parameter list_equiv : forall A, Equiv A -> Equiv (list A).
Parameter option_equiv : forall A, Equiv A -> Equiv (option A).
Parameter list_lookup : forall A, Lookup nat A (list A).

Existing Instance list_equiv.
Existing Instance option_equiv.
Existing Instance list_lookup.

Lemma list_equiv_lookup {A} `{Equiv A} (l k : list A) :
  equiv l k <-> forall i, equiv (lookup i l) (lookup i k).
Proof. Admitted.
(*
?Equiv : "Equiv (option ?A)"

?Lookup : "Lookup ?K ?A (list A)"

?Lookup0 : "Lookup ?K ?A (list A)"
*)
