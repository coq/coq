(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Evd
open Environ
open Rawterm
open Evarutil
(*i*)

(* Compilation of pattern-matching. *)

val compile_multcase :
  (trad_constraint -> env -> rawconstr -> unsafe_judgment)
  * 'a evar_defs -> trad_constraint -> env ->
    rawconstr option * rawconstr list *
    (identifier list * pattern list * rawconstr) list ->
    unsafe_judgment
