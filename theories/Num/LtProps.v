(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Axioms.
Require Export AddProps.
Require Export NeqProps.

(** This file contains basic properties of the less than relation *)


Lemma lt_anti_sym : (x,y:N)x<y->~(y<x).
Red; Intros x y lt1 lt2; Apply (lt_anti_refl x); EAuto with num.
Qed.
Hints Resolve lt_anti_refl : num.

Lemma eq_not_lt : (x,y:N)(x=y)->~(x<y).
Red; Intros x y eq1 lt1; Apply (lt_anti_refl x); EAuto with num.
Qed.
Hints Resolve eq_not_lt : num.

Lemma lt_0_1 : (zero<one).
EAuto with num.
Qed.
Hints Resolve lt_0_1 : num.


Lemma eq_lt_x_Sy : (x,y:N)(x=y)->(x<(S y)).
EAuto with num.
Qed.
Hints Resolve eq_lt_x_Sy : num.

Lemma lt_lt_x_Sy : (x,y:N)(x<y)->(x<(S y)).
EAuto with num.
Qed.
Hints Immediate lt_lt_x_Sy : num.

Lemma lt_Sx_y_lt : (x,y:N)((S x)<y)->(x<y).
EAuto with num.
Qed.
Hints Immediate lt_Sx_y_lt : num.

(** Relating [<] and [=] *)

Lemma lt_neq : (x,y:N)(x<y)->(x<>y).
Red; Intros x y lt1 eq1; Apply (lt_anti_refl x); EAuto with num.
Qed.
Hints Immediate lt_neq : num.

Lemma lt_neq_sym : (x,y:N)(y<x)->(x<>y).
Intros x y lt1 ; Apply neq_sym; Auto with num.
Qed.
Hints Immediate lt_neq_sym : num.

(** Application to inequalities properties *)

Lemma neq_x_Sx : (x:N)x<>(S x).
Auto with num.
Qed.
Hints Resolve neq_x_Sx : num.

Lemma neq_0_1 : zero<>one.
Auto with num.
Qed.
Hints Resolve neq_0_1 : num.

(** Relating [<] and [+] *)

Lemma lt_add_compat_r : (x,y,z:N)(x<y)->((z+x)<(z+y)).
Intros x y z H; Apply lt_eq_compat with (x+z) (y+z); Auto with num.
Qed.
Hints Resolve lt_add_compat_r : num.

Lemma lt_add_compat : (x1,x2,y1,y2:N)(x1<x2)->(y1<y2)->((x1+y1)<(x2+y2)).
Intros; Apply lt_trans with (x1+y2); Auto with num.
Qed.
Hints Immediate lt_add_compat : num.

