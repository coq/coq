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
open Libnames
open Rawterm
open Topconstr
open Ppextend

(*i*)

(**********************************************************************)
(* Scopes *)

(*s A scope is a set of interpreters for symbols + optional
   interpreter and printers for integers + optional delimiters *)

type level = precedence * tolerability list
type delimiters = string
type scope
type scopes = scope_name list

val default_scope : scope_name
val type_scope : scope_name
val declare_scope : scope_name -> unit

(* Open scope *)

val current_scopes : unit -> scopes
val open_scope : bool * scope_name -> unit

(* Declare delimiters for printing *)

val declare_delimiters : scope_name -> delimiters -> unit
val find_delimiters_scope : loc -> delimiters -> scope_name

(*s Declare and uses back and forth a numeral interpretation *)

(* A numeral interpreter is the pair of an interpreter for _integer_
   numbers in terms and an optional interpreter in pattern, if
   negative numbers are not supported, the interpreter must fail with
   an appropriate error message *)

type num_interpreter =
    (loc -> bigint -> rawconstr)
    * (loc -> bigint -> name -> cases_pattern) option

type num_uninterpreter =
    rawconstr list * (rawconstr -> bigint option)
    * (cases_pattern -> bigint option) option

type required_module = string list 
val declare_numeral_interpreter : scope_name -> required_module ->
  num_interpreter -> num_uninterpreter -> unit

(* Returns the term/cases_pattern bound to a numeral in a given scope context*)
val interp_numeral : loc -> bigint -> scopes -> rawconstr
val interp_numeral_as_pattern : loc -> bigint -> name -> scopes ->cases_pattern

(* Returns the numeral bound to a term/cases_pattern; raises No_match if no *)
(* such numeral *)
val uninterp_numeral : rawconstr -> scope_name * bigint
val uninterp_cases_numeral : cases_pattern -> scope_name * bigint

val availability_of_numeral : scope_name -> scopes -> delimiters option option

(*s Declare and interpret back and forth a notation *)

(* Binds a notation in a given scope to an interpretation *)
type interp_rule =
  | NotationRule of scope_name * notation
  | SynDefRule of kernel_name
val declare_notation_interpretation : notation -> scope_name ->
      interpretation -> string -> unit

val declare_uninterpretation : interp_rule -> interpretation -> unit

(* Returns the interpretation bound to a notation *)
val interp_notation : notation -> scopes -> interpretation

(* Returns the possible notations for a given term *)
val uninterp_notations : rawconstr ->
      (interp_rule * interpretation * int option) list

(* Test if a notation is available in the scopes *)
(* context [scopes] if available, the result is not None; the first *)
(* argument is itself not None if a delimiters is needed; the second *)
(* argument is a numeral printer if the *)
val availability_of_notation : scope_name * notation -> scopes -> 
  (scope_name option * delimiters option) option

(*s Declare and test the level of a (possibly uninterpreted) notation *)

val declare_notation_level : notation -> level -> unit
val level_of_notation : notation -> level (* [Not_found] if no level *)

(*s** Miscellaneous *)

(* Checks for already existing notations *)
val exists_notation_in_scope : scope_name -> notation ->
      interpretation-> bool

(* Declares and looks for scopes associated to arguments of a global ref *)
val declare_arguments_scope: global_reference -> scope_name option list -> unit
val find_arguments_scope : global_reference -> scope_name option list

val declare_class_scope : scope_name -> Classops.cl_typ -> unit
val declare_ref_arguments_scope : global_reference -> unit

(* Analysing notation *)
type symbol_token = WhiteSpace of int | String of string
val split : notation -> symbol_token list

(* Prints scopes (expect a pure aconstr printer *)
val pr_scope : (rawconstr -> std_ppcmds) -> scope_name -> std_ppcmds
val pr_scopes : (rawconstr -> std_ppcmds) -> std_ppcmds
val locate_notation : (rawconstr -> std_ppcmds) -> notation -> std_ppcmds

(**********************************************************************)
(*s Printing rules for notations *)

(* Declare and look for the printing rule for symbolic notations *)
type unparsing_rule = unparsing list * precedence
val declare_notation_printing_rule : notation -> unparsing_rule -> unit
val find_notation_printing_rule : notation -> unparsing_rule

(**********************************************************************)
(* Rem: printing rules for numerals are trivial *)

