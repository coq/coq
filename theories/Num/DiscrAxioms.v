(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Params.
Require Export NSyntax.

(** Axiom for a discrete set *)

Axiom lt_x_Sy_le : (x,y:N)(x<(S y))->(x<=y).
Hints Resolve lt_x_Sy_le : num.
