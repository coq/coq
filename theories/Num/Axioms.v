(*i $Id: i*)

(*s Axioms for the basic numerical operations *)
Require Export Definitions.
Require Export NSyntax.

(*s Axioms for [eq] *)

Axiom eq_refl : (x:N)(x=x).
Axiom eq_sym : (x,y:N)(x=y)->(y=x).
Axiom eq_trans : (x,y,z:N)(x=y)->(y=z)->(x=z).

(*s Axioms for [add] *)

Axiom add_sym : (x,y:N)(x+y)=(y+x).
Axiom add_eq_compat : (x1,x2,y1,y2:N)(x1=x2)->(y1=y2)->(x1+y1)=(x2+y2).
Axiom add_assoc_l : (x,y,z:N)((x+y)+z)=(x+(y+z)).
Axiom add_x_0 : (x:N)(x+zero)=x.

(*s Axioms for [S] *)
Axiom S_eq_compat : (x,y:N)(x=y)->(S x)=(S y).
Axiom add_Sx_y : (x,y:N)((S x)+y)=(S (x+y)).

(*s Axioms for [one] *)
Axiom S_0_1 : (S zero)=one.

(*s Axioms for [<], 
    properties of [>], [<=] and [>=] will be derived from [<] *)

Axiom lt_trans : (x,y,z:N)x<y->y<z->x<z.
Axiom lt_anti_sym : (x,y:N)x<y->~(y<x).

Axiom lt_x_Sx : (x:N)x<(S x).
Axiom lt_S_compat : (x,y:N)(x<y)->(S x)<(S y).

Axiom lt_eq_compat : (x1,x2,y1,y2:N)(x1=y1)->(x2=y2)->(x1<x2)->(y1<y2).
Axiom lt_add_compat_l : (x,y,z:N)(x<y)->((x+z)<(y+z)).

Hints Resolve eq_refl eq_trans add_sym add_eq_compat add_assoc_l add_x_0 
	      S_eq_compat add_Sx_y S_0_1 lt_x_Sx lt_S_compat
              lt_trans lt_anti_sym lt_eq_compat lt_add_compat_l : num.
Hints Immediate eq_sym : num.
  