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
open Tacmach
(*i*)

(* Programmable destruction of hypotheses and conclusions. *)

val set_extern_interp : (Tacexpr.raw_tactic_expr -> tactic) -> unit

(*
val dHyp : identifier -> tactic
val dConcl : tactic
*)
val h_destructHyp : bool -> identifier -> tactic
val h_destructConcl : tactic
val h_auto_tdb : int option -> tactic

val add_destructor_hint :
  identifier -> (bool,unit) Tacexpr.location ->
    Genarg.constr_ast -> int -> Tacexpr.raw_tactic_expr -> unit
