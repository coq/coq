Require Export Axioms.
Require Export AddProps.

(*s This file contains basic properties of the less than relation *)

Lemma lt_anti_refl : (x:N)~(x<x).
Red; Intros x H; Exact (lt_anti_sym x x H H).
Save.
Hints Resolve lt_anti_refl : num.

Lemma eq_not_lt : (x,y:N)(x=y)->~(x<y).
Red; Intros x y eq1 lt1; Apply (lt_anti_refl x); EAuto with num.
Save.
Hints Resolve eq_not_lt : num.

Lemma lt_0_1 : (zero<one).
EAuto with num.
Save.
Hints Resolve lt_0_1 : num.


Lemma eq_lt_x_Sy : (x,y:N)(x=y)->(x<(S y)).
EAuto with num.
Save.
Hints Resolve eq_lt_x_Sy : num.

Lemma lt_lt_x_Sy : (x,y:N)(x<y)->(x<(S y)).
EAuto with num.
Save.
Hints Immediate lt_lt_x_Sy : num.

Lemma lt_Sx_y_lt : (x,y:N)((S x)<y)->(x<y).
EAuto with num.
Save.
Hints Immediate lt_Sx_y_lt : num.

(*s Relating [<] and [=] *)

Lemma lt_neq : (x,y:N)(x<y)->(x<>y).
Red; Intros x y lt1 eq1; Apply (lt_anti_refl x); EAuto with num.
Save.
Hints Immediate lt_neq : num.

Lemma lt_neq_sym : (x,y:N)(y<x)->(x<>y).
Intros x y lt1 ; Apply neq_sym; Auto with num.
Save.
Hints Immediate lt_neq_sym : num.

(*s Application to inequalities properties *)

Lemma neq_x_Sx : (x:N)x<>(S x).
Auto with num.
Save.
Hints Resolve neq_x_Sx : num.

Lemma neq_0_1 : zero<>one.
Auto with num.
Save.
Hints Resolve neq_0_1 : num.

(*s Relating [<] and [+] *)

Lemma lt_add_compat_r : (x,y,z:N)(x<y)->((z+x)<(z+y)).
Intros x y z H; Apply lt_eq_compat with (x+z) (y+z); Auto with num.
Save.
Hints Resolve lt_add_compat_r : num.


