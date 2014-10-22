(* There used to be an evar leak in the to_nat example *)

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint Idx {A:Type} (l:list A) : Type :=
  match l with
  | [] => False
  | _::l => True + Idx l
  end.

Fixpoint to_nat {A:Type} (l:list A) (i:Idx l) : nat :=
  match l,i with
  |  [] , i => match i with end
  | _::_, inl _ => 0
  | _::l, inr i => S (to_nat l i)
  end.
