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
open Nametab

module ToplevelPp : Mlpp

val sp_of_r : global_reference -> section_path

val long_module : global_reference -> dir_path

val is_long_module : dir_path -> global_reference -> bool

val short_module : global_reference -> identifier

val extract_to_file : 
  string -> extraction_params -> ml_decl list -> unit

