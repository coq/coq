(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Util
open Pp
open Bignat
open Names
open Nametab
open Rawterm
open Topconstr
open Ppextend
(*i*)

(*s A numeral interpreter is the pair of an interpreter for _integer_
   numbers in terms and an optional interpreter in pattern, if
   negative numbers are not supported, the interpreter must fail with
   an appropriate error message *)

type numeral_interpreter_name = string
type numeral_interpreter =
    (loc -> bigint -> rawconstr)
    * (loc -> bigint -> name -> cases_pattern) option

(* A scope is a set of interpreters for symbols + optional
   interpreter and printers for integers + optional delimiters *)

type level = precedence * precedence list
type delimiters = string * string
type scope
type scopes = scope_name list

val default_scope : scope_name
val current_scopes : unit -> scopes
val open_scope : scope_name -> unit
val declare_scope : scope_name -> unit

(* Declare delimiters for printing *)
val declare_delimiters : scope_name -> delimiters -> unit

(* Declare, interpret, and look for a printer for numeral *)
val declare_numeral_interpreter :
  numeral_interpreter_name -> numeral_interpreter -> unit
val interp_numeral : loc -> bigint -> scopes -> rawconstr
val interp_numeral_as_pattern : loc -> bigint -> name -> scopes ->cases_pattern
val find_numeral_printer : string -> scopes ->
  (delimiters option * scopes) option

(* Declare, interpret, and look for a printer for symbolic notations *)
val declare_notation : notation -> scope_name -> aconstr * level -> unit
val interp_notation : notation -> scopes -> aconstr
val find_notation : scope_name -> notation -> scopes -> 
  (delimiters option * scopes) option
val exists_notation_in_scope : 
  scope_name -> level -> notation -> aconstr -> bool
val exists_notation : level -> notation -> bool

(* Declare and look for scopes associated to arguments of a global ref *)
open Libnames
val declare_arguments_scope: global_reference -> scope_name option list -> unit
val find_arguments_scope : global_reference -> scope_name option list

(* Printing scopes *)
val pr_scope : (aconstr -> std_ppcmds) -> scope_name -> std_ppcmds
val pr_scopes : (aconstr -> std_ppcmds) -> std_ppcmds


val declare_printing_rule : notation -> unparsing list * precedence -> unit
val find_notation_printing_rule : notation -> unparsing list * precedence

