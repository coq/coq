(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Miniml
open Mlutil
open Names
open Nametab

module ToplevelPp : Mlpp
module OcamlMonoPp : Mlpp
module HaskellMonoPp : Mlpp

val is_long_module : dir_path -> global_reference -> bool

val short_module : global_reference -> identifier

val pp_logical_ind : global_reference -> std_ppcmds

val pp_singleton_ind : global_reference -> std_ppcmds

val extract_to_file : 
  string option -> extraction_params -> ml_decl list -> unit


