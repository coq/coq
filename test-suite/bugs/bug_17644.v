
Module Import A1. Polymorphic Axiom nd1 : Type. End A1.
Module Import B1. Notation nd1 := nd1@{Set}. End B1.

Definition x := nd1. (* A.nd1: implicit generated instance forced > Set by univ mono of "x" *)
Check x : Set.

Definition y := B1.nd1.
Check y : Set.
