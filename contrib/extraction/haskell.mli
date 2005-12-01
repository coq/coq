(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Names
open Miniml

val keywords : Idset.t

val preamble : 
  extraction_params -> module_path list -> bool*bool*bool -> bool -> std_ppcmds

module Make : functor(P : Mlpp_param) -> Mlpp
