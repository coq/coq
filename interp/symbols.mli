(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
type scopes (* = scope_name list*)

val type_scope : scope_name
val declare_scope : scope_name -> unit

(* Open scope *)

val current_scopes : unit -> scopes
val open_close_scope : 
  (* locality *) bool * (* open *) bool * scope_name -> unit

(* Extend a list of scopes *)
val empty_scope_stack : scopes
val push_scope : scope_name -> scopes -> scopes

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

type required_module = global_reference * string list 
val declare_numeral_interpreter : scope_name -> required_module ->
  num_interpreter -> num_uninterpreter -> unit

(* Returns the term/cases_pattern bound to a numeral in a given scope context*)
val interp_numeral : loc -> bigint -> scope_name list -> rawconstr
val interp_numeral_as_pattern : loc -> bigint -> name -> scope_name list ->
  cases_pattern

(* Returns the numeral bound to a term/cases_pattern; raises No_match if no *)
(* such numeral *)
val uninterp_numeral : rawconstr -> scope_name * bigint
val uninterp_cases_numeral : cases_pattern -> scope_name * bigint

val availability_of_numeral : scope_name -> scopes -> delimiters option option

(*s Declare and interpret back and forth a notation *)

(* Binds a notation in a given scope to an interpretation *)
type interp_rule =
  | NotationRule of scope_name option * notation
  | SynDefRule of kernel_name
val declare_notation_interpretation : notation -> scope_name option ->
      interpretation -> dir_path * string -> bool -> unit

val declare_uninterpretation : interp_rule -> interpretation -> unit

(* Returns the interpretation bound to a notation *)
val interp_notation : loc -> notation -> scope_name list -> 
      interpretation * ((dir_path * string) * scope_name option)

(* Returns the possible notations for a given term *)
val uninterp_notations : rawconstr ->
      (interp_rule * interpretation * int option) list
val uninterp_cases_pattern_notations : cases_pattern ->
      (interp_rule * interpretation * int option) list

(* Test if a notation is available in the scopes *)
(* context [scopes] if available, the result is not None; the first *)
(* argument is itself not None if a delimiters is needed; the second *)
(* argument is a numeral printer if the *)
val availability_of_notation : scope_name option * notation -> scopes -> 
  (scope_name option * delimiters option) option

(*s Declare and test the level of a (possibly uninterpreted) notation *)

val declare_notation_level : notation -> level option * level -> unit
val level_of_notation : notation -> level option * level 
      (* raise [Not_found] if no level *)

(*s** Miscellaneous *)

(* Checks for already existing notations *)
val exists_notation_in_scope : scope_name option -> notation ->
      interpretation -> bool * bool

(* Declares and looks for scopes associated to arguments of a global ref *)
val declare_arguments_scope: global_reference -> scope_name option list -> unit
val find_arguments_scope : global_reference -> scope_name option list

val declare_class_scope : scope_name -> Classops.cl_typ -> unit
val declare_ref_arguments_scope : global_reference -> unit

val compute_arguments_scope : Term.types -> scope_name option list

(* Building notation key *)

type symbol =
  | Terminal of string
  | NonTerminal of identifier
  | SProdList of identifier * symbol list
  | Break of int

val make_notation_key : symbol list -> notation
val decompose_notation_key : notation -> symbol list

(* Prints scopes (expect a pure aconstr printer *)
val pr_scope : (rawconstr -> std_ppcmds) -> scope_name -> std_ppcmds
val pr_scopes : (rawconstr -> std_ppcmds) -> std_ppcmds
val locate_notation : (rawconstr -> std_ppcmds) -> notation -> std_ppcmds

val pr_visibility: (rawconstr -> std_ppcmds) -> scope_name option -> std_ppcmds

(**********************************************************************)
(*s Printing rules for notations *)

(* Declare and look for the printing rule for symbolic notations *)
type unparsing_rule = unparsing list * precedence
val declare_notation_printing_rule : notation -> unparsing_rule -> unit
val find_notation_printing_rule : notation -> unparsing_rule

(**********************************************************************)
(* Rem: printing rules for numerals are trivial *)
