Set Primitive Projections.
Require Import Coq.Init.Specif Coq.Init.Datatypes Coq.Init.Logic.

Parameters A B : Prop.
Parameter P : A -> Prop.

Fail Check fun x : sigT P => (eq_refl : x = existT P (projT1 x) (projT2 x)).
Fail Check fun x : sig P => (eq_refl : x = exist P (proj1_sig x) (proj2_sig x)).
Fail Check fun x : A * B => (eq_refl : x = (fst x, snd x)).
Fail Check fun x : A /\ B => (eq_refl : x = conj (proj1 x) (proj2 x)).
