Primitive int := #int63_type.

Module bad1.
Polymorphic Inductive badcarry1 (A:Type) : Type :=
| C0: A -> badcarry1 A
| C1: A -> badcarry1 A.

Fail Register badcarry1 as kernel.ind_carry.

End bad1.

Module bad2.

Inductive badcarry2 (A:Set) : Set :=
| C0: A -> badcarry2 A
| C1: A -> badcarry2 A.

Fail Register badcarry2 as kernel.ind_carry.

End bad2.

Module bad3.

Inductive badcarry3 : Type -> Type  :=
| C0: forall A, A -> badcarry3 A
| C1: forall A, A -> badcarry3 A.

Fail Register badcarry3 as kernel.ind_carry.

End bad3.
