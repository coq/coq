Polymorphic Definition type := Type.

Inductive bad : type := .

Fail Check bad : Prop.
Check bad : Set.
(* lowered as much as possible *)
