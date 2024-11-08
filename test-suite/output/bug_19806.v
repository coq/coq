Require Extraction.

Parameter X : Set.
Parameter x : X.

Extract Constant X => "X".
Extract Inlined Constant x => "test".

Definition y := x.

Extraction Language Scheme.
Extraction y.
