(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** InEquality is introduced as an independant parameter, it could be 
    instantiated with the negation of equality *)

Require Export EqParams.
Require Export NeqParams.

Axiom eq_not_neq : (x,y:N)x=y->~(x<>y).
Hints Immediate eq_not_neq : num.

Axiom neq_sym : (x,y:N)(x<>y)->(y<>x).
Hints Resolve neq_sym : num.

Axiom neq_not_neq_trans : (x,y,z:N)(x<>y)->~(y<>z)->(x<>z).
Hints Resolve neq_not_neq_trans : num.









