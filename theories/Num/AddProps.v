(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Axioms.
Require Export EqAxioms.

(** This file contains basic properties of addition with respect to equality *)

(** Properties of Addition *)
Lemma add_x_0 : (x:N)(x+zero)=x.
EAuto 3 with num.
Qed.
Hints Resolve add_x_0 : num.

Lemma add_x_Sy : (x,y:N)(x+(S y))=(S (x+y)).
Intros x y; Apply eq_trans with (S y)+x; EAuto with num.
Qed.

Hints Resolve add_x_Sy : num.

Lemma add_x_Sy_swap : (x,y:N)(x+(S y))=((S x)+y).
EAuto with num.
Qed.
Hints Resolve add_x_Sy_swap : num.

Lemma add_Sx_y_swap : (x,y:N)((S x)+y)=(x+(S y)).
Auto with num.
Qed.
Hints Resolve add_Sx_y_swap : num.


Lemma add_assoc_r : (x,y,z:N)(x+(y+z))=((x+y)+z).
Auto with num.
Qed.
Hints Resolve add_assoc_r : num.

Lemma add_x_y_z_perm : (x,y,z:N)((x+y)+z)=(y+(x+z)).
EAuto with num.
Qed.
Hints Resolve add_x_y_z_perm : num.

Lemma add_x_one_S : (x:N)(x+one)=(S x).
Intros; Apply eq_trans with (x+(S zero)); EAuto with num.
Qed.
Hints Resolve add_x_one_S : num.

Lemma add_one_x_S : (x:N)(one+x)=(S x).
Intros; Apply eq_trans with (x+one); Auto with num.
Qed.
Hints Resolve add_one_x_S : num.


