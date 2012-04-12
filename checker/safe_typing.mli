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

val get_env : unit -> env

(* exporting and importing modules *)
type compiled_library

val set_engagement : Declarations.engagement -> unit
val import         :
  CUnix.physical_path -> compiled_library -> Digest.t -> unit
val unsafe_import  :
  CUnix.physical_path -> compiled_library -> Digest.t -> unit

(** Store the body of modules' opaque constants inside a table. 

    This module is used during the serialization and deserialization
    of vo files. 
*)
module LightenLibrary :
sig
  type table 
  type lightened_compiled_library 

  (** [load table lcl] builds a compiled library from a
      lightened library [lcl] by remplacing every index by its related
      opaque terms inside [table]. *)
  val load : table -> lightened_compiled_library -> compiled_library
end
