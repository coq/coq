(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Names
open Libnames
open Miniml
open Mlutil

val long_module : global_reference -> dir_path

val create_mono_renamings : ml_decl list -> unit
val set_keywords : unit -> unit

val pp_decl : unit -> ml_decl -> std_ppcmds

val segment_contents : Lib.library_segment -> global_reference list

val module_contents : dir_path -> global_reference list 

val extract_to_file : 
  string option -> extraction_params -> ml_decl list -> unit
