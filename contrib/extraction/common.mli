(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Miniml
open Mlutil
open Names

module ToplevelPp : Mlpp

val module_of_r : global_reference -> identifier

val extract_to_file : 
  string -> extraction_params -> ml_decl list -> unit

