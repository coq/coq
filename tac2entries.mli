(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Libnames
open Tac2expr

(** {5 Toplevel definitions} *)

val register_ltac : ?local:bool -> rec_flag ->
  (Name.t located * raw_tacexpr) list -> unit

val register_type : ?local:bool -> rec_flag ->
  (qualid located * redef_flag * raw_quant_typedef) list -> unit

val register_primitive : ?local:bool ->
  Id.t located -> raw_typexpr -> ml_tactic_name -> unit

val register_struct : ?local:bool -> strexpr -> unit

val register_notation : ?local:bool -> sexpr list -> int option ->
  raw_tacexpr -> unit

(** {5 Notations} *)

type scope_rule =
| ScopeRule : (raw_tacexpr, 'a) Extend.symbol * ('a -> raw_tacexpr) -> scope_rule

type scope_interpretation = sexpr list -> scope_rule

val register_scope : Id.t -> scope_interpretation -> unit
(** Create a new scope with the provided name *)

val parse_scope : sexpr -> scope_rule
(** Use this to interpret the subscopes for interpretation functions *)

(** {5 Inspecting} *)

val print_ltac : Libnames.reference -> unit

(** {5 Eval loop} *)

(** Evaluate a tactic expression in the current environment *)
val call : default:bool -> raw_tacexpr -> unit

(** {5 Parsing entries} *)

module Pltac :
sig
val tac2expr : raw_tacexpr Pcoq.Gram.entry
end
