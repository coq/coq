(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Term
open Environ
(*i*)

val reset : unit -> unit
val get_env : unit -> env

(* exporting and importing modules *)
type compiled_library

val set_engagement : Declarations.engagement -> unit
val import         :
  System.physical_path -> compiled_library -> Digest.t -> unit
val unsafe_import  :
  System.physical_path -> compiled_library -> Digest.t -> unit

module LightenLibrary :
sig
  type table 
  type lighten_compiled_library 
  val save : compiled_library -> lighten_compiled_library * table
  val load : load_proof:bool -> (unit -> table) -> lighten_compiled_library -> compiled_library
end
