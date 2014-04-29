(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Names
open Declarations
open Environ
open Nativecode

(** This file implements separate compilation for libraries in the native
compiler *)

val dump_library : module_path -> dir_path -> env -> module_signature ->
  global list * symbol array
