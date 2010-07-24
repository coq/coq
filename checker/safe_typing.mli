(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: safe_typing.mli 9821 2007-05-11 17:00:58Z aspiwack $ i*)

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
