(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Bigint
open Names
open Libnames
open Globnames
open Constrexpr
open Glob_term
open Notation_term
open Ppextend

(** Notations *)

(** {6 Scopes } *)
(** A scope is a set of interpreters for symbols + optional
   interpreter and printers for integers + optional delimiters *)

type delimiters = string
type scope
type scopes (** = [scope_name list] *)

val declare_scope : scope_name -> unit

val current_scopes : unit -> scopes

val notation_entry_eq : notation_entry -> notation_entry -> bool
(** Equality on [notation_entry]. *)

val notation_eq : notation -> notation -> bool
(** Equality on [notation]. *)

val level_eq : level -> level -> bool

(** Check where a scope is opened or not in a scope list, or in
 * the current opened scopes *)
val scope_is_open_in_scopes : scope_name -> scopes -> bool
val scope_is_open : scope_name -> bool

(** Open scope *)

val open_close_scope :
  (** locality *) bool * (* open *) bool * scope_name -> unit

(** Extend a list of scopes *)
val empty_scope_stack : scopes
val push_scope : scope_name -> scopes -> scopes

val find_scope : scope_name -> scope

(** Declare delimiters for printing *)

val declare_delimiters : scope_name -> delimiters -> unit
val remove_delimiters : scope_name -> unit
val find_delimiters_scope : ?loc:Loc.t -> delimiters -> scope_name

(** {6 Declare and uses back and forth an interpretation of primitive token } *)

(** A numeral interpreter is the pair of an interpreter for **integer**
   numbers in terms and an optional interpreter in pattern, if
   negative numbers are not supported, the interpreter must fail with
   an appropriate error message *)

type notation_location = (DirPath.t * DirPath.t) * string
type required_module = full_path * string list
type cases_pattern_status = bool (** true = use prim token in patterns *)

type 'a prim_token_interpreter =
    ?loc:Loc.t -> 'a -> glob_constr

type 'a prim_token_uninterpreter =
    glob_constr list * (any_glob_constr -> 'a option) * cases_pattern_status

type rawnum = Constrexpr.raw_natural_number * Constrexpr.sign

val declare_rawnumeral_interpreter : scope_name -> required_module ->
  rawnum prim_token_interpreter -> rawnum prim_token_uninterpreter -> unit

val declare_numeral_interpreter : scope_name -> required_module ->
  bigint prim_token_interpreter -> bigint prim_token_uninterpreter -> unit

val declare_string_interpreter : scope_name -> required_module ->
  string prim_token_interpreter -> string prim_token_uninterpreter -> unit

(** Return the [term]/[cases_pattern] bound to a primitive token in a
   given scope context*)

val interp_prim_token : ?loc:Loc.t -> prim_token -> subscopes ->
  glob_constr * (notation_location * scope_name option)
(* This function returns a glob_const representing a pattern *)
val interp_prim_token_cases_pattern_expr : ?loc:Loc.t -> (global_reference -> unit) -> prim_token ->
  subscopes -> glob_constr * (notation_location * scope_name option)

(** Return the primitive token associated to a [term]/[cases_pattern];
   raise [No_match] if no such token *)

val uninterp_prim_token :
  'a glob_constr_g -> scope_name * prim_token
val uninterp_prim_token_cases_pattern :
  'a cases_pattern_g -> Name.t * scope_name * prim_token
val uninterp_prim_token_ind_pattern :
 inductive -> cases_pattern list -> scope_name * prim_token

val availability_of_prim_token :
  prim_token -> scope_name -> subscopes -> delimiters option option

(** {6 Declare and interpret back and forth a notation } *)

(** Binds a notation in a given scope to an interpretation *)
type interp_rule =
  | NotationRule of scope_name option * notation
  | SynDefRule of KerName.t

val declare_notation_interpretation : notation -> scope_name option ->
      interpretation -> notation_location -> onlyprint:bool -> unit

val declare_uninterpretation : interp_rule -> interpretation -> unit

(** Return the interpretation bound to a notation *)
val interp_notation : ?loc:Loc.t -> notation -> subscopes ->
      interpretation * (notation_location * scope_name option)

type notation_rule_core =
    interp_rule (* kind of notation *)
  * interpretation (* pattern associated to the notation *)
  * int option (* number of expected arguments *)

type notation_rule =
    notation_rule_core
  * delimiters option (* delimiter to possibly add *)

(** Return the possible notations for a given term *)
val uninterp_notations : Notation_term.subscopes -> 'a glob_constr_g -> notation_rule list
val uninterp_cases_pattern_notations : Notation_term.subscopes -> 'a cases_pattern_g -> notation_rule list
val uninterp_ind_pattern_notations : Notation_term.subscopes -> inductive -> notation_rule list

(*
(** Test if a notation is available in the scopes 
   context [scopes]; if available, the result is not None; the first 
   argument is itself not None if a delimiters is needed *)
val availability_of_notation : scope_name option * notation -> subscopes ->
  (scope_name option * delimiters option) option
 *)

(** {6 Declare and test the level of a (possibly uninterpreted) notation } *)

val declare_notation_level : notation -> level -> unit
val level_of_notation : notation -> level (** raise [Not_found] if no level *)

(** {6 Miscellaneous} *)

val interp_notation_as_global_reference : ?loc:Loc.t -> (global_reference -> bool) ->
      notation_key -> delimiters option -> global_reference

(** Checks for already existing notations *)
val exists_notation_in_scope : scope_name option -> notation ->
      bool -> interpretation -> bool

(** Checks for already existing notations *)
val exists_notation_interpretation_in_scope : scope_name option -> notation -> bool

(** Declares and looks for scopes associated to arguments of a global ref *)
val declare_arguments_scope :
  bool (** true=local *) -> global_reference -> scope_name option list -> unit

val find_arguments_scope : global_reference -> scope_name option list

type scope_class

(** Comparison of scope_class *)
val scope_class_compare : scope_class -> scope_class -> int

val subst_scope_class :
  Mod_subst.substitution -> scope_class -> scope_class option

val declare_scope_class : scope_name -> scope_class -> unit
val declare_ref_arguments_scope : Evd.evar_map -> global_reference -> unit

val compute_arguments_scope : Evd.evar_map -> EConstr.types -> scope_name option list
val compute_type_scope : Evd.evar_map -> EConstr.types -> scope_name option

(** Get the current scope bound to Sortclass, if it exists *)
val current_type_scope_name : unit -> scope_name option

val scope_class_of_class : Classops.cl_typ -> scope_class

(** Building notation key *)

type symbol =
  | Terminal of string              (* an expression including symbols or a simply-quoted ident, e.g. "'U'" or "!" *)
  | NonTerminal of Id.t             (* an identifier "x" *)
  | SProdList of Id.t * symbol list (* an expression "x sep .. sep y", remembering x (or y) and sep *)
  | Break of int                    (* a sequence of blanks > 1, e.g. "   " *)

val symbol_eq : symbol -> symbol -> bool

(** Make/decompose a notation of the form "_ U _" *)
val make_notation_key : notation_entry -> symbol list -> notation
val decompose_notation_key : notation -> notation_entry * symbol list

(** Decompose a notation of the form "a 'U' b" *)
val decompose_raw_notation : string -> symbol list

(** Prints scopes (expects a pure aconstr printer) *)
val pr_scope_class : scope_class -> Pp.t
val pr_scope : (glob_constr -> Pp.t) -> scope_name -> Pp.t
val pr_scopes : (glob_constr -> Pp.t) -> Pp.t
val locate_notation : (glob_constr -> Pp.t) -> notation_key ->
      scope_name option -> Pp.t

val pr_visibility: (glob_constr -> Pp.t) -> scope_name option -> Pp.t

val pr_notation : notation -> Pp.t

(** {6 Printing rules for notations} *)

(** Declare and look for the printing rule for symbolic notations *)
type unparsing_rule = unparsing list * precedence
type extra_unparsing_rules = (string * string) list
val declare_notation_rule :
  notation -> extra:extra_unparsing_rules -> unparsing_rule -> notation_grammar -> unit
val find_notation_printing_rule : notation -> unparsing_rule
val find_notation_extra_printing_rules : notation -> extra_unparsing_rules
val find_notation_parsing_rules : notation -> notation_grammar
val add_notation_extra_printing_rule : notation -> string -> string -> unit

type entry_coercion = notation list
val declare_entry_coercion : notation -> notation_entry -> unit
val availability_of_entry_coercion : notation_entry -> notation_entry -> entry_coercion option

(** Returns notations with defined parsing/printing rules *)
val get_defined_notations : unit -> notation list

(** Rem: printing rules for primitive token are canonical *)

val with_notation_protection : ('a -> 'b) -> 'a -> 'b
