(*i $Id: i*)

(*s Axioms for equality *)
Require Export Params.
Require Export EqParams.
Require Export NSyntax.

(*s Basic Axioms for [eq] *)

Axiom eq_refl : (x:N)(x=x).
Axiom eq_sym : (x,y:N)(x=y)->(y=x).
Axiom eq_trans : (x,y,z:N)(x=y)->(y=z)->(x=z).

(*s Axioms for [eq] and [add] *)
Axiom add_eq_compat : (x1,x2,y1,y2:N)(x1=x2)->(y1=y2)->(x1+y1)=(x2+y2).

(*s Axioms for [eq] and [S] *)
Axiom S_eq_compat : (x,y:N)(x=y)->(S x)=(S y).

(*s Axioms for [eq] and [<] *)
Axiom lt_eq_compat : (x1,x2,y1,y2:N)(x1=y1)->(x2=y2)->(x1<x2)->(y1<y2).

Hints Resolve eq_refl eq_trans add_eq_compat S_eq_compat lt_eq_compat : num.
Hints Immediate eq_sym : num.
