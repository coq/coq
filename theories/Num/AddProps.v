
Require Export Axioms.

(*s This file contains basic properties of addition with respect to equality *)

(*s Properties of inequalities *)
Lemma neq_sym : (x,y:N)(x<>y)->(y<>x).
Unfold neq; Auto with num.
Save.

Hints Resolve neq_sym : num.

Lemma neq_eq_compat : (x1,x2,y1,y2:N)(x1=y1)->(x2=y2)->(x1<>x2)->(y1<>y2).
Red; EAuto with num.
Save.
Hints Resolve neq_eq_compat : num.

(*s Properties of Addition *)
Lemma add_x_0 : (x:N)(x+zero)=x.
EAuto 3 with num.
Save.
Hints Resolve add_x_0 : num.

Lemma add_x_Sy : (x,y:N)(x+(S y))=(S (x+y)).
Intros x y; Apply eq_trans with (S y)+x; EAuto with num.
Save.

Hints Resolve add_x_Sy : num.

Lemma add_x_Sy_swap : (x,y:N)(x+(S y))=((S x)+y).
EAuto with num.
Save.
Hints Resolve add_x_Sy_swap : num.

Lemma add_Sx_y_swap : (x,y:N)((S x)+y)=(x+(S y)).
Auto with num.
Save.
Hints Resolve add_Sx_y_swap : num.


Lemma add_assoc_r : (x,y,z:N)(x+(y+z))=((x+y)+z).
Auto with num.
Save.
Hints Resolve add_assoc_r : num.

Lemma add_x_y_z_perm : (x,y,z:N)((x+y)+z)=(y+(x+z)).
EAuto with num.
Save.
Hints Resolve add_x_y_z_perm : num.

Lemma add_x_one_S : (x:N)(x+one)=(S x).
Intros; Apply eq_trans with (x+(S zero)); EAuto with num.
Save.
Hints Resolve add_x_one_S : num.

Lemma add_one_x_S : (x:N)(one+x)=(S x).
Intros; Apply eq_trans with (x+one); Auto with num.
Save.
Hints Resolve add_one_x_S : num.



