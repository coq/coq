(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Axioms for the basic numerical operations *)
Require Export Params.
Require Export EqParams.
Require Export NSyntax.

(** Axioms for [eq] *)

Axiom eq_refl : (x:N)(x=x).
Axiom eq_sym : (x,y:N)(x=y)->(y=x).
Axiom eq_trans : (x,y,z:N)(x=y)->(y=z)->(x=z).

(** Axioms for [add] *)

Axiom add_sym : (x,y:N)(x+y)=(y+x).
Axiom add_assoc_l : (x,y,z:N)((x+y)+z)=(x+(y+z)).
Axiom add_0_x : (x:N)(zero+x)=x.

(** Axioms for [S] *)
Axiom add_Sx_y : (x,y:N)((S x)+y)=(S (x+y)).

(** Axioms for [one] *)
Axiom S_0_1 : (S zero)=one.

(** Axioms for [<], 
    properties of [>], [<=] and [>=] will be derived from [<] *)

Axiom lt_trans : (x,y,z:N)x<y->y<z->x<z.
Axiom lt_anti_refl : (x:N)~(x<x).

Axiom lt_x_Sx : (x:N)x<(S x).
Axiom lt_S_compat : (x,y:N)(x<y)->(S x)<(S y).

Axiom lt_add_compat_l : (x,y,z:N)(x<y)->((x+z)<(y+z)).

Hints Resolve add_sym add_assoc_l add_0_x add_Sx_y S_0_1 lt_x_Sx lt_S_compat
              lt_trans lt_anti_refl lt_add_compat_l : num.
