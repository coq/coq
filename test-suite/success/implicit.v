(* Implicit on section variables *)

Set Implicit Arguments.

(* Example submitted by David Nowak *)

Section Spec.
Variable A:Set.
Variable op : (A:Set)A->A->Set.
Infix 6 "#" op V8only (at level 70).
Check (x:A)(x # x).

(* Example submitted by Christine *)
Record stack : Type := {type : Set; elt : type; 
                        empty : type -> bool; proof : (empty elt)=true }.

Check (type:Set; elt:type; empty:(type->bool))(empty elt)=true->stack.

End Spec.
