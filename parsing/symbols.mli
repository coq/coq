open Names
open Util
open Nametab
open Rawterm
open Bignat

(* A numeral interpreter is the pair of an interpreter for _integer_
   numbers in terms and an optional interpreter in pattern, if
   negative numbers are not supported, the interpreter must fail with
   an appropriate error message *)

type numeral_interpreter_name = string
type numeral_interpreter =
    (loc -> bigint -> rawconstr)
    * (loc -> bigint -> name -> cases_pattern) option

(* A scope is a set of interpreters for symbols + optional
   interpreter and printers for integers + optional delimiters *)

type scope_name = string
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
val interp_numeral_as_pattern: loc -> bigint -> name -> scopes -> cases_pattern
val find_numeral_printer : string -> scopes ->
  (delimiters option * scopes) option

(* Declare, interpret, and look for a printer for symbolic notations *)
type notation = string
val declare_notation : notation -> rawconstr -> scope_name -> unit
val interp_notation : notation -> scopes -> rawconstr  list -> rawconstr
val find_notation : scope_name -> notation -> scopes -> 
  (delimiters option * scopes) option
val exists_notation_in_scope : scope_name -> notation -> bool
val exists_notation : notation -> bool
