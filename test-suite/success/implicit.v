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

(* Example submitted by Frédéric (interesting in v8 syntax) *)

Parameter f : nat -> nat * nat.
Notation lhs := fst.
Check [x](lhs ? ? (f x)).
Check [x](!lhs ? ? (f x)).
Notation "'rhs'" := snd.
Check [x](rhs ? ? (f x)).
(* V8 seulement 
Check (fun x => @ rhs ? ? (f x)).
*)
