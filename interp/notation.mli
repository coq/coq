(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames
open Constrexpr
open Glob_term
open Notation_term
open Notationextern
open Globnames

(** Notations *)

val notation_cat : Libobject.category

val pr_notation : notation -> Pp.t
(** Printing *)

module NotationSet : CSet.ExtS with type elt = notation
module NotationMap : CMap.ExtS with type key = notation and module Set := NotationSet
module SpecificNotationSet : CSet.ExtS with type elt = specific_notation
module SpecificNotationMap : CMap.ExtS with type key = specific_notation and module Set := SpecificNotationSet

(** {6 Scopes } *)
(** A scope is a set of interpreters for symbols + optional
   interpreter and printers for integers + optional delimiters *)

type delimiters = string
type scope
type scopes (** = [scope_name list] *)

val declare_scope : scope_name -> unit

(* To be removed after deprecation phase *)
val ensure_scope : scope_name -> unit

val current_scopes : unit -> scopes

(** Check where a scope is opened or not in a scope list, or in
 * the current opened scopes *)
val scope_is_open_in_scopes : scope_name -> scopes -> bool
val scope_is_open : scope_name -> bool

(** Open scope *)
val open_scope : scope_name -> unit
val close_scope : scope_name -> unit

(** Return a scope taking either a scope name or delimiter *)
val normalize_scope : string -> scope_name

(** Extend a list of scopes *)
val empty_scope_stack : scopes
val push_scope : scope_name -> scopes -> scopes

val find_scope : scope_name -> scope

val scope_delimiters : scope -> delimiters option

(** Declare delimiters for printing *)

val declare_delimiters : scope_name -> delimiters -> unit
val remove_delimiters : scope_name -> unit
val find_delimiters_scope : ?loc:Loc.t -> delimiters -> scope_name

(** {6 Declare and uses back and forth an interpretation of primitive token } *)

(** A number interpreter is the pair of an interpreter for **(hexa)decimal**
   numbers in terms and an optional interpreter in pattern, if
   non integer or negative numbers are not supported, the interpreter
   must fail with an appropriate error message *)

type notation_location = (DirPath.t * DirPath.t * Loc.t option) * string
(** 1st dirpath: dirpath of the library
    2nd dirpath: module and section-only dirpath (ie [Lib.current_dirpath true])
    location: The location. Presumably you can recover the dirpaths from that but I don't know how.
    string: string used to generate the notation

    dirpaths are used for dumpglob, the location for Locate, and string for printing (pr_notation_info)
*)

type required_module = full_path * string list

type prim_token_infos = {
  pt_local : bool; (** Is this interpretation local? *)
  pt_scope : scope_name; (** Concerned scope *)
  pt_interp_info : PrimNotations.prim_token_interp_info; (** Unique id "pointing" to (un)interp functions, OR a number notation object describing (un)interp functions *)
  pt_required : required_module; (** Module that should be loaded first *)
  pt_refs : GlobRef.t list; (** Entry points during uninterpretation *)
  pt_in_match : bool (** Is this prim token legal in match patterns ? *)
}

(** Note: most of the time, the [pt_refs] field above will contain
    inductive constructors (e.g. O and S for nat). But it could also be
    injection functions such as IZR for reals. *)

(** Activate a prim token interpretation whose unique id and functions
    have already been registered. *)

val enable_prim_token_interpretation : prim_token_infos -> unit

(** Return the [term]/[cases_pattern] bound to a primitive token in a
   given scope context*)

val interp_prim_token : ?loc:Loc.t -> prim_token -> subscopes ->
  glob_constr
(* This function returns a glob_const representing a pattern *)
val interp_prim_token_cases_pattern_expr : ?loc:Loc.t -> (Glob_term.glob_constr -> unit) -> prim_token ->
  subscopes -> glob_constr

(** Return the primitive token associated to a [term]/[cases_pattern];
   raise [No_match] if no such token *)

val uninterp_prim_token :
  print_float:bool -> 'a glob_constr_g -> subscopes -> prim_token * delimiters option
val uninterp_prim_token_cases_pattern :
  print_float:bool -> 'a cases_pattern_g -> subscopes -> Name.t * prim_token * delimiters option

val availability_of_prim_token :
  prim_token -> scope_name -> subscopes -> delimiters option option

(** {6 Declare and interpret back and forth a notation } *)

val warning_overridden_name : string

type entry_coercion_kind =
  | IsEntryCoercion of notation_entry_level * notation_entry_relative_level
  | IsEntryGlobal of CustomName.t * int
  | IsEntryIdent of CustomName.t * int

val declare_notation : notation_with_optional_scope * notation ->
  interpretation -> notation_location -> use:notation_use ->
  entry_coercion_kind option ->
  UserWarn.t option -> unit


(** Return the interpretation bound to a notation *)
val interp_notation : ?loc:Loc.t -> notation -> subscopes ->
      interpretation * (notation_location * scope_name option)

(** Test if a notation is available in the scopes
   context [scopes]; if available, the result is not None; the first
   argument is itself not None if a delimiters is needed *)
val availability_of_notation : specific_notation -> subscopes ->
  (scope_name option * delimiters option) option

val is_printing_inactive_rule : Notationextern.interp_rule -> interpretation -> bool

type 'a notation_query_pattern_gen = {
    notation_entry_pattern : notation_entry list;
    interp_rule_key_pattern : (notation_key, 'a) Util.union option;
    use_pattern : notation_use;
    scope_pattern : notation_with_optional_scope option;
    interpretation_pattern : interpretation option;
  }

type notation_query_pattern = qualid notation_query_pattern_gen

val toggle_notations : on:bool -> all:bool -> ?verbose:bool -> (glob_constr -> Pp.t) -> notation_query_pattern -> unit

(** {6 Miscellaneous} *)

(** Take a notation string and turn it into a notation key. eg. ["x +  y"] becomes ["_ + _"]. *)
val interpret_notation_string : string -> string

type notation_as_reference_error =
  | AmbiguousNotationAsReference of notation_key
  | NotationNotReference of Environ.env * Evd.evar_map * notation_key * (notation_key * notation_constr) list

exception NotationAsReferenceError of notation_as_reference_error

(** If head is true, also allows applied global references.
    Raise NotationAsReferenceError if not resolvable as a global reference *)
val interp_notation_as_global_reference : ?loc:Loc.t -> head:bool ->
      (GlobRef.t -> bool) -> notation_key -> delimiters option -> GlobRef.t

(** Same together with the full notation *)
val interp_notation_as_global_reference_expanded : ?loc:Loc.t -> head:bool ->
      (GlobRef.t -> bool) -> notation_key -> delimiters option ->
  notation * notation_key * notation_with_optional_scope * interpretation * GlobRef.t

(** Declares and looks for scopes associated to arguments of a global ref *)
val declare_arguments_scope :
  bool (** true=local *) -> GlobRef.t -> scope_name list list -> unit

val find_arguments_scope : Environ.env -> GlobRef.t -> scope_name list list

type scope_class

(** Comparison of scope_class *)
val scope_class_compare : scope_class -> scope_class -> int

val subst_scope_class :
  Environ.env -> Mod_subst.substitution -> scope_class -> scope_class option

type add_scope_where = AddScopeTop | AddScopeBottom
(** add new scope at top or bottom of existing stack (default is reset) *)
val declare_scope_class : (* local: *) bool -> scope_name -> ?where:add_scope_where -> scope_class -> unit
val declare_ref_arguments_scope : GlobRef.t -> unit

val compute_arguments_scope : Environ.env -> Evd.evar_map -> EConstr.types -> scope_name list list
val compute_type_scope : Environ.env -> Evd.evar_map -> EConstr.types -> scope_name list
val compute_glob_type_scope : 'a Glob_term.glob_constr_g -> scope_name list

(** Get the current scopes bound to Sortclass *)
val current_type_scope_names : unit -> scope_name list

val scope_class_of_class : Coercionops.cl_typ -> scope_class

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

(** This is the output of decomposing a notation declaration:
    [mainvars] include all notation variables, keeping only one for
      each pair (typically the first one) in case of a recursive pattern
      (e.g. in ``Notation "[ x ; y ; .. ; z ]" := ...'', the mainvars
      are [x;y]);
    [maintypes] describes the structure of the pattern, e.g.,
      for the same notation, it is
      [[NtnRawTypeVar "x"; NtnRawTypeVarList (NtnRawTypeVar ("y", "z"))]]
    [symbols] describes the parsing rule, e.g. for the same notation, it is
      [[Terminal "["; NonTerminal "x"; SProdList ("y",[Terminal ";"]); Terminal "]"]] *)
type notation_symbols = {
  mainvars : Id.t list; (* names of "toplevel" non-terminals *)
  maintypes : Id.t notation_raw_type list; (* types of "toplevel" non-terminals *)
  symbols : symbol list; (* the decomposition of the notation into terminals and nonterminals; there, recursive patterns refer to the left-hand variable *)
}

val is_prim_token_constant_in_constr : notation_entry * symbol list -> bool

(** Decompose a notation of the form "a 'U' b" together with the lists
    of pairs of recursive variables and the list of all variables
    binding in the notation *)
val decompose_raw_notation : string -> notation_symbols

(** Prints scopes (expects a pure aconstr printer) *)
val pr_scope_class : scope_class -> Pp.t
val pr_scope : (glob_constr -> Pp.t) -> scope_name -> Pp.t
val pr_scopes : (glob_constr -> Pp.t) -> Pp.t
val locate_notation : (glob_constr -> Pp.t) -> notation_key ->
      scope_name option -> Pp.t

val pr_visibility: (glob_constr -> Pp.t) -> scope_name option -> Pp.t

(** Coercions between entries *)

val is_coercion : notation_entry_level -> notation_entry_relative_level -> bool
  (** For a rule of the form
      "Notation string := x (in some-entry, x at some-relative-entry)",
      tell if going from some-entry to some-relative-entry is coercing *)

val declare_entry_coercion : specific_notation -> notation_entry_level -> notation_entry_relative_level -> unit
  (** Add a coercion from some-entry to some-relative-entry *)

type entry_coercion = (notation_with_optional_scope * notation) list
val availability_of_entry_coercion : ?non_included:bool -> notation_entry_relative_level -> notation_entry_level -> entry_coercion option
  (** Return a coercion path from some-relative-entry to some-entry if there is one *)

(** Special properties of entries *)

val declare_custom_entry_has_global : CustomName.t -> int -> unit
val declare_custom_entry_has_ident : CustomName.t -> int -> unit

val entry_has_global : notation_entry_relative_level -> bool
val entry_has_ident : notation_entry_relative_level -> bool

val app_level : int

val prec_less : entry_level -> entry_relative_level -> bool
val may_capture_cont_after : entry_level option -> entry_relative_level -> bool

(** {6 Declare and test the level of a (possibly uninterpreted) notation } *)

val declare_notation_level : notation -> level -> unit
val level_of_notation : notation -> level
  (** raise [Not_found] if not declared *)

(** Rem: printing rules for primitive token are canonical *)

val with_notation_protection : ('a -> 'b) -> 'a -> 'b


val declare_ntn_gram_loc : notation -> Loc.t option -> unit
