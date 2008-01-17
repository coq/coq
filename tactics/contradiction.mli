(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Rawterm
open Genarg
(*i*)

(*arnaud: trucs factices *)
type tactic = Tacticals.tactic
(*arnaud: /trucs factices *)

val absurd                      : constr -> tactic
val contradiction               : constr with_ebindings option -> tactic
