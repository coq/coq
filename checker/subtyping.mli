(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: subtyping.mli 5920 2004-07-16 20:01:26Z herbelin $ i*)

(*i*)
open Univ
open Term
open Declarations
open Environ
(*i*)

val check_subtypes : env -> module_type_body -> module_type_body -> unit
val check_equal : env -> module_type_body -> module_type_body -> unit


