Module Single.

Inductive bexp : Set :=
  | b_true : bexp
  | b_false : bexp
  | b_eq : bexp -> bexp -> bexp.

Class ContainsFalse (A : Set) :=
  contains_false : A -> bool.

Fixpoint bexp_CF : ContainsFalse bexp := fun b =>
  match b with
  | b_true => false
  | b_false => true
  | b_eq a1 a2 => orb (contains_false a1) (contains_false a2)
  end.
Existing Instance bexp_CF.

End Single.

Module Mutual.

Inductive bexp : Set :=
  | b_true : bexp
  | b_false : bexp
  | b_eq : aexp -> aexp -> bexp
with aexp : Set :=
     | a_of_bool : bexp -> aexp.

Class ContainsFalse (A : Set) :=
  contains_false : A -> bool.

Fixpoint bexp_ContainsFalse : ContainsFalse bexp := fun b =>
  match b with
  | b_true => false
  | b_false => true
  | b_eq a1 a2 => orb (contains_false a1) (contains_false a2)
  end with
aexp_ContainsFalse : ContainsFalse aexp := fun a =>
  match a with
  | a_of_bool b => contains_false b
  end.

Existing Instance bexp_ContainsFalse.
Existing Instance aexp_ContainsFalse.

End Mutual.
