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

Require Export Params.

Parameter neq : N -> N -> Prop.

Infix 6 "<>" neq V8only 70.







