(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export ZAxioms ZMulOrder.

(** This functor summarizes all known facts about Z.
    For the moment it is only an alias to [ZMulOrderPropFunct], which
    subsumes all others.
*)

Module ZPropFunct := ZMulOrderPropFunct.
