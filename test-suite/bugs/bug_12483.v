Require Import PrimFloat FloatAxioms.

Goal False.
Proof.
cut (false = true).
{ intro H; discriminate H. }
change false with (1 <=? 0)%float.
rewrite leb_spec.
Fail reflexivity.
Abort.
