(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Coqast
open Ast
open Pcoq
open Extend
(*i*)

type frozen_t

val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit
val init : unit -> unit

val extend_grammar : grammar_command -> unit

val remove_rule : (string * gram_universe) -> typed_entry -> grammar_rule ->
  unit
val remove_entry : (string * gram_universe) -> grammar_entry -> unit
val remove_grammar : grammar_command -> unit
