Require Export LtProps.
Require Export LeAxioms.

(*s Properties of the relation [<=] *)

Lemma lt_le : (x,y:N)(x<y)->(x<=y).
Auto with num.
Save.

Lemma eq_le : (x,y:N)(x=y)->(x<=y).
Auto with num.
Save.

Lemma le_eq_compat : (x1,x2,y1,y2:N)(x1=y1)->(x2=y2)->(x1<=x2)->(y1<=y2).
Intros x1 x2 y1 y2 eq1 eq2 le1; Case le_lt_or_eq with 1:=le1; Intro.
EAuto with num.
Apply eq_le; Apply eq_trans with x1; EAuto with num.
Save.
Hints Resolve le_eq_compat : num.

Lemma le_trans : (x,y,z:N)(x<=y)->(y<=z)->(x<=z).
Intros x y z le1 le2.
Case le_lt_or_eq with 1:=le1; Intro.
Case le_lt_or_eq with 1:=le2; EAuto with num.
EAuto with num.
Save.
Hints Resolve le_trans : num.

(*s compatibility with equality, addition and successor *)
Lemma le_add_compat_l : (x,y,z:N)(x<=y)->((x+z)<=(y+z)).
Intros x y z le1.
Case le_lt_or_eq with 1:=le1; EAuto with num.
Save.
Hints Resolve le_add_compat_l : num.

Lemma le_add_compat_r : (x,y,z:N)(x<=y)->((z+x)<=(z+y)).
Intros x y z H; Apply le_eq_compat with (x+z) (y+z); Auto with num.
Save.
Hints Resolve le_add_compat_r : num.

Lemma le_S_compat : (x,y:N)(x<=y)->((S x)<=(S y)).
Intros x y le1.
Case le_lt_or_eq with 1:=le1; EAuto with num.
Save.
Hints Resolve le_S_compat : num.

Lemma le_lt_x_Sy : (x,y:N)(x<=y)->(x<(S y)).
Intros x y le1.
Case le_lt_or_eq with 1:=le1; Auto with num.
Save.
Hints Immediate le_lt_x_Sy : num.

Lemma le_Sx_y_lt : (x,y:N)((S x)<=y)->(x<y).
Intros x y le1.
Case le_lt_or_eq with 1:=le1; EAuto with num.
Save.
Hints Immediate le_Sx_y_lt : num.

Lemma lt_le_trans : (x,y,z:N)(x<y)->(y<=z)->(x<z).
Intros x y z lt1 le1; Case le_lt_or_eq with 1:= le1; EAuto with num.
Save.

Lemma le_lt_trans : (x,y,z:N)(x<=y)->(y<z)->(x<=z).
Intros x y z le1 lt1; Case le_lt_or_eq with 1:= le1; EAuto with num.
Save.
Hints Immediate lt_le_trans le_lt_trans : num.

