(*i $Id$ i*)

Require Export DiscrAxioms.
Require Export LtProps.

(*s Properties of a discrete order *)

Lemma lt_le_Sx_y : (x,y:N)(x<y) -> ((S x)<=y).
EAuto with num.
Save.
Hints Resolve lt_le_Sx_y : num.