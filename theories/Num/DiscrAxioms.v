(*i $Id$ i*)

Require Export Definitions.
Require Export NSyntax.

(*s Axiom for a discrete set *)

Axiom lt_x_Sy_le : (x,y:N)(x<(S y))->(x<=y).
Hints Resolve lt_x_Sy_le : num.
