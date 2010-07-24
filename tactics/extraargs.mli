(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tacexpr
open Term
open Names
open Proof_type
open Topconstr
open Termops
open Rawterm

val rawwit_orient : bool raw_abstract_argument_type
val wit_orient : bool typed_abstract_argument_type
val orient : bool Pcoq.Gram.entry

val occurrences : (int list or_var) Pcoq.Gram.entry
val rawwit_occurrences : (int list or_var) raw_abstract_argument_type
val wit_occurrences : (int list) typed_abstract_argument_type

val rawwit_raw : constr_expr raw_abstract_argument_type
val wit_raw : (Tacinterp.interp_sign * rawconstr) typed_abstract_argument_type
val raw : constr_expr Pcoq.Gram.entry

type 'id gen_place= ('id * hyp_location_flag,unit) location

type loc_place = identifier Util.located gen_place
type place = identifier gen_place

val rawwit_hloc : loc_place raw_abstract_argument_type
val wit_hloc : place typed_abstract_argument_type
val hloc : loc_place Pcoq.Gram.entry


val in_arg_hyp:  (Names.identifier Util.located list option * bool)  Pcoq.Gram.entry
val rawwit_in_arg_hyp : (Names.identifier Util.located list option * bool) raw_abstract_argument_type
val wit_in_arg_hyp : (Names.identifier list option * bool) typed_abstract_argument_type
val raw_in_arg_hyp_to_clause : (Names.identifier Util.located list option * bool) -> Tacticals.clause
val glob_in_arg_hyp_to_clause :  (Names.identifier list option * bool)  -> Tacticals.clause


val by_arg_tac : Tacexpr.raw_tactic_expr option Pcoq.Gram.entry
val rawwit_by_arg_tac :  raw_tactic_expr option raw_abstract_argument_type
val wit_by_arg_tac : glob_tactic_expr option typed_abstract_argument_type



(** Spiwack: Primitive for retroknowledge registration *)

val retroknowledge_field : Retroknowledge.field Pcoq.Gram.entry
val rawwit_retroknowledge_field :  Retroknowledge.field raw_abstract_argument_type
val wit_retroknowledge_field : Retroknowledge.field typed_abstract_argument_type
