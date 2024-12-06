(* There used to be an evar leak in the to_nat example *)

Fixpoint Idx {A:Type} (l:list A) : Type :=
  match l with
  | nil => False
  | cons _ l => True + Idx l
  end.

Fixpoint to_nat {A:Type} (l:list A) (i:Idx l) : nat :=
  match l,i with
  | nil , i => match i with end
  | cons _ _, inl _ => 0
  | cons _ l, inr i => S (to_nat l i)
  end.
