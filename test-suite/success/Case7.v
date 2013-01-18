Inductive List (A : Set) : Set :=
  | Nil : List A
  | Cons : A -> List A -> List A.

Inductive Empty (A : Set) : List A -> Prop :=
    intro_Empty : Empty A (Nil A).

Parameter
  inv_Empty : forall (A : Set) (a : A) (x : List A), ~ Empty A (Cons A a x).


Type
  (fun (A : Set) (l : List A) =>
   match l return (Empty A l \/ ~ Empty A l) with
   | Nil _ => or_introl (~ Empty A (Nil A)) (intro_Empty A)
   | Cons _ a y as b => or_intror (Empty A b) (inv_Empty A a y)
   end).
