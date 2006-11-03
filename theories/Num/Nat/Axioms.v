(*i $Id$ i*)

(*s Axioms for the basic numerical operations *)
Require Export Params.
Require Export EqAxioms.
Require NSyntax.

(*s Lemmas for [add] *)

Lemma add_Sx_y : (x,y:N)((S x)+y)=(S (x+y)).
Induction y; Simpl; Auto with nat.
Save.
Hints Resolve add_Sx_y : nat.

(*s Lemmas for [add] *)

Lemma add_0_x : (x:N)(zero+x)=x.
Induction x; Simpl; Auto with nat.
Save.
Hints Resolve add_0_x : nat.

Lemma add_sym : (x,y:N)(x+y)=(y+x).
Intros x y; Elim y; Simpl; Intros; Auto with nat.
Rewrite H; Elim x; Simpl; Intros; Auto with nat.
Save.
Hints Resolve add_sym : nat.

Lemma add_eq_compat : (x1,x2,y1,y2:N)(x1=x2)->(y1=y2)->(x1+y1)=(x2+y2).
Intros x1 x2 y1 y2 eq1 eq2; Rewrite eq1; Rewrite eq2; Auto.
Save.
Hints Resolve add_eq_compat : nat.

Lemma add_assoc_l : (x,y,z:N)((x+y)+z)=(x+(y+z)).
Intros x y z; Elim z; Simpl; Intros; Auto with nat.
Save.



(*s Lemmas for [one] *)
Lemma S_0_1 : (S zero)=one.
Auto.
Save.

(*s Lemmas for [<], 
    properties of [>], [<=] and [>=] will be derived from [<] *)

Lemma lt_trans : (x,y,z:N)x<y->y<z->x<z.
Intros x y z lt1 lt2; Elim lt2; Unfold lt; Auto with nat.
Save.
Hints Resolve lt_trans : nat.

Lemma lt_x_Sx : (x:N)x<(S x).
Unfold lt; Auto with nat.
Save.
Hints Resolve lt_x_Sx : nat.

Lemma lt_S_compat : (x,y:N)(x<y)->(S x)<(S y).
Intros x y lt1; Elim lt1; Unfold lt; Auto with nat.
Save.
Hints Resolve lt_S_compat : nat.

Lemma lt_eq_compat : (x1,x2,y1,y2:N)(x1=y1)->(x2=y2)->(x1<x2)->(y1<y2).
Intros x1 x2 y1 y2 eq1 eq2; Rewrite eq1; Rewrite eq2; Trivial.
Save.

Lemma lt_add_compat_l : (x,y,z:N)(x<y)->((x+z)<(y+z)).
Intros x y z lt1; Elim z; Simpl; Auto with nat.
Save.

Lemma lt_Sx_Sy_lt : (x,y:N)((S x)<(S y))->(x<y).
Intros x y lt1; Inversion lt1; EAuto with nat.
Save.
Hints Immediate lt_Sx_Sy_lt : nat.

Lemma lt_anti_refl : (x:N)~(x<x).
Induction x; Red; Intros.
Inversion H.
Auto with nat.
Save.



  