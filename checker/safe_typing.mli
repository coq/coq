(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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
  CUnix.physical_path -> compiled_library -> constr array -> Digest.t -> unit
val unsafe_import  :
  CUnix.physical_path -> compiled_library -> Digest.t -> unit
