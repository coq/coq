Polymorphic Definition type := Type.

Inductive bad : type := .

Fail Check bad : Prop.
Fail Check bad : Set.
(* nothing to trigger minimization to set so we get a floating univ,
   and it's monomorphic so > Set *)

Module withcumul.

#[universes(cumulative)]
Polymorphic Definition type := Type.

#[universes(polymorphic,cumulative)]
Inductive bad : type := .

Fail Check bad : Prop.
Check bad : Set.
(* Here Set is the principal type of bad *)

End withcumul.
