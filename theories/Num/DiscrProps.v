(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export DiscrAxioms.
Require Export LtProps.

(** Properties of a discrete order *)

Lemma lt_le_Sx_y : (x,y:N)(x<y) -> ((S x)<=y).
EAuto with num.
Qed.
Hints Resolve lt_le_Sx_y : num.