(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Axioms.
Require Export LtProps.

(** Axiomatizing [<=] from [<] *)

Axiom lt_or_eq_le : (x,y:N)((x<y)\/(x=y))->(x<=y).
Axiom le_lt_or_eq : (x,y:N)(x<=y)->(x<y)\/(x=y).

Hints Resolve lt_or_eq_le : num.
Hints Immediate le_lt_or_eq : num.
