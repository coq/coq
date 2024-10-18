Class Equiv A := equiv: A -> A -> Prop.
#[export] Hint Mode Equiv ! : typeclass_instances.

Class Lookup (K A M : Type) := lookup: K -> M -> option A.
#[export] Hint Mode Lookup ! - - : typeclass_instances.
#[export] Hint Mode Lookup - - ! : typeclass_instances.

Parameter list_equiv : forall A, Equiv A -> Equiv (list A).
Parameter option_equiv : forall A, Equiv A -> Equiv (option A).
Parameter list_lookup : forall A, Lookup nat A (list A).

#[export] Existing Instance list_equiv.
#[export] Existing Instance option_equiv.
#[export] Existing Instance list_lookup.

Set Typeclasses Debug.
(* fails *)
Lemma list_equiv_lookup {A} `{Equiv A} (l k : list A) :
  equiv l k <-> forall i, equiv (lookup i l) (lookup i k).
Admitted.
(*
?Equiv : "Equiv (option ?A)"

?Lookup : "Lookup ?K ?A (list A)"

?Lookup0 : "Lookup ?K ?A (list A)"
*)
