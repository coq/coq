(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Axioms.
Require Export LeProps.

(** Axiomatizing [>] from [<] *)

Axiom not_le_gt : (x,y:N)~(x<=y)->(x>y).
Axiom gt_not_le : (x,y:N)(x>y)->~(x<=y).

Hints Resolve not_le_gt : num.

Hints Immediate gt_not_le : num.
