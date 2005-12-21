(* Implicit on section variables *)

Set Implicit Arguments.
Unset Strict Implicit.

(* Example submitted by David Nowak *)

Section Spec.
Variable A : Set.
Variable op : forall A : Set, A -> A -> Set.
Infix "#" := op (at level 70).
Check (forall x : A, x # x).

(* Example submitted by Christine *)
Record stack : Type := 
  {type : Set; elt : type; empty : type -> bool; proof : empty elt = true}.

Check
  (forall (type : Set) (elt : type) (empty : type -> bool),
   empty elt = true -> stack).

End Spec.

(* Example submitted by Frédéric (interesting in v8 syntax) *)

Parameter f : nat -> nat * nat.
Notation lhs := fst.
Check (fun x => fst (f x)).
Check (fun x => fst (f x)).
Notation rhs := snd.
Check (fun x => snd (f x)).
(* V8 seulement 
Check (fun x => @ rhs ? ? (f x)).
*)
