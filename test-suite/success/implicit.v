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
Check (fun x => @ rhs _ _ (f x)).

(* Implicit arguments in fixpoints and inductive declarations *)

Fixpoint g n := match n with O => true | S n => g n end.

Inductive P n : nat -> Prop := c : P n n.

(* Avoid evars in the computation of implicit arguments (cf r9827) *)

Require Import List.

Fixpoint plus n m {struct n} :=
  match n with 
  | 0 => m
  | S p => S (plus p m)
  end.
