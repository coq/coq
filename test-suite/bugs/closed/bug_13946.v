Succeed Inductive Foo (A:Prop) : Prop := foo : _ tt.

Class ElemOf A B := elem_of: A -> B -> Prop.
Infix "∈" := elem_of (at level 70) .
Inductive Types := tnil: Types | tcons: Type -> Types -> Types.
Implicit Type As: Types.
Infix "^::" := tcons (at level 60, right associativity).
Notation "^[ ]" := tnil (at level 5, format "^[ ]").

Inductive hlist F : Types -> Type :=
| hnil: hlist F ^[]
| hcons {A As} : F A -> hlist F As -> hlist F (A ^:: As).
Infix "+::" := (hcons _) (at level 60, right associativity).

Fail Inductive elem_of_hlist  {F A As} : ElemOf (F A) (hlist F As) :=
  | elem_of_hlist_here F A As (x : F A) (l : hlist F As) : x ∈ (x +:: l)
  | elem_of_list_further F A As (x y : F A) (l : hlist F As) : x ∈ l -> x ∈ (y +:: l).

Fail Inductive elem_of_hlist  {F A As} : ElemOf (F A) (hlist F As) :=
  | elem_of_hlist_here (x : F A) (l : hlist F As) : x ∈ (x +:: l)
  | elem_of_list_further (x y : F A) (l : hlist F As) : x ∈ l -> x ∈ (y +:: l).
