
(*s Instantiating [eqN] with Leibniz equality *)

Require NSyntax.

Definition eqN [x,y:N] := (x==y).
Hints Unfold eqN : num.

Grammar constr constr1 :=
eq_impl [ constr0($c) "=" constr0($c2) ] -> [ (eqN $c $c2) ].

Syntax constr
  level 1:
    equal [ (eqN $t1 $t2) ] -> [ [<hov 0> $t1:E [0 1]  "=" $t2:E ] ].

(*s Lemmas for [eqN] *)

Lemma eq_refl : (x:N)(x=x).
Auto with num.
Save.

Lemma eq_sym : (x,y:N)(x=y)->(y=x).
Unfold eqN; Auto.
Save.

Lemma eq_trans : (x,y,z:N)(x=y)->(y=z)->(x=z).
Intros; Red; Transitivity y; Auto.
Save.

Hints Resolve eq_refl eq_trans : num.
Hints Immediate eq_sym : num.

(*s Compatibility lemmas for [S], [add], [lt] *)
Lemma S_eq_compat : (x,y:N)(x=y)->(S x)=(S y).
Intros x y eq1; Unfold eqN; Rewrite eq1; Auto.
Save.
Hints Resolve S_eq_compat : nat.

Lemma add_eq_compat : (x1,x2,y1,y2:N)(x1=x2)->(y1=y2)->(x1+y1)=(x2+y2).
Intros x1 x2 y1 y2 eq1 eq2;Unfold eqN;  Rewrite eq1; Rewrite eq2; Auto.
Save.
Hints Resolve add_eq_compat : nat.

Lemma lt_eq_compat : (x1,x2,y1,y2:N)(x1=y1)->(x2=y2)->(x1<x2)->(y1<y2).
Intros x1 x2 y1 y2 eq1 eq2; Unfold eqN; Rewrite eq1; Rewrite eq2; Trivial.
Save.

Hints Resolve add_eq_compat S_eq_compat lt_eq_compat : num.

 