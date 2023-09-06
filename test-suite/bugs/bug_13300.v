Polymorphic Definition type := Type.

Inductive bad : type := .

Fail Check bad : Prop.
Fail Check bad : Set.
(* nothing to trigger minimization to set so we get a floating univ,
   and it's monomorphic so > Set *)
