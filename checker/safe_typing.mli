(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Cic
open Environ
(*i*)

val get_env : unit -> env

val set_engagement : engagement -> unit
val import         :
  CUnix.physical_path -> compiled_library -> Univ.constraints -> Cic.vodigest -> unit
val unsafe_import  :
  CUnix.physical_path -> compiled_library -> Univ.constraints -> Cic.vodigest -> unit
