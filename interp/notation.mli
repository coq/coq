(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

(** Notations *)

val pr_notation : notation -> Pp.t
(** Printing *)

val notation_entry_eq : notation_entry -> notation_entry -> bool
(** Equality on [notation_entry]. *)

val notation_entry_level_eq : notation_entry_level -> notation_entry_level -> bool
(** Equality on [notation_entry_level]. *)

val notation_eq : notation -> notation -> bool
(** Equality on [notation]. *)

module NotationSet : Set.S with type elt = notation
module NotationMap : CMap.ExtS with type key = notation and module Set := NotationSet

(** {6 Scopes } *)
(** A scope is a set of interpreters for symbols + optional
   interpreter and printers for integers + optional delimiters *)

type delimiters = string
type scope
type scopes (** = [scope_name list] *)

val declare_scope : scope_name -> unit

val current_scopes : unit -> scopes

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
type rawnum = Constrexpr.raw_natural_number * Constrexpr.sign

(** The unique id string below will be used to refer to a particular
    registered interpreter/uninterpreter of numeral or string notation.
    Using the same uid for different (un)interpreters will fail.
    If at most one interpretation of prim token is used per scope,
    then the scope name could be used as unique id. *)

type prim_token_uid = string

type 'a prim_token_interpreter = ?loc:Loc.t -> 'a -> glob_constr
type 'a prim_token_uninterpreter = any_glob_constr -> 'a option

type 'a prim_token_interpretation =
  'a prim_token_interpreter * 'a prim_token_uninterpreter

val register_rawnumeral_interpretation :
  ?allow_overwrite:bool -> prim_token_uid -> rawnum prim_token_interpretation -> unit

val register_bignumeral_interpretation :
  ?allow_overwrite:bool -> prim_token_uid -> Bigint.bigint prim_token_interpretation -> unit

val register_string_interpretation :
  ?allow_overwrite:bool -> prim_token_uid -> string prim_token_interpretation -> unit

(** * Numeral notation *)

type numeral_notation_error =
  | UnexpectedTerm of Constr.t
  | UnexpectedNonOptionTerm of Constr.t

exception NumeralNotationError of Environ.env * Evd.evar_map * numeral_notation_error

type numnot_option =
  | Nop
  | Warning of raw_natural_number
  | Abstract of raw_natural_number

type int_ty =
  { uint : Names.inductive;
    int : Names.inductive }

type z_pos_ty =
  { z_ty : Names.inductive;
    pos_ty : Names.inductive }

type target_kind =
  | Int of int_ty (* Coq.Init.Decimal.int + uint *)
  | UInt of Names.inductive (* Coq.Init.Decimal.uint *)
  | Z of z_pos_ty (* Coq.Numbers.BinNums.Z and positive *)

type option_kind = Option | Direct
type conversion_kind = target_kind * option_kind

type numeral_notation_obj =
  { to_kind : conversion_kind;
    to_ty : GlobRef.t;
    of_kind : conversion_kind;
    of_ty : GlobRef.t;
    num_ty : Libnames.qualid; (* for warnings / error messages *)
    warning : numnot_option }

type prim_token_interp_info =
    Uid of prim_token_uid
  | NumeralNotation of numeral_notation_obj

type prim_token_infos = {
  pt_local : bool; (** Is this interpretation local? *)
  pt_scope : scope_name; (** Concerned scope *)
  pt_interp_info : prim_token_interp_info; (** Unique id "pointing" to (un)interp functions, OR a numeral notation object describing (un)interp functions *)
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

(** Compatibility.
    Avoid the next two functions, they will now store unnecessary
    objects in the library segment. Instead, combine
    [register_*_interpretation] and [enable_prim_token_interpretation]
    (the latter inside a [Mltop.declare_cache_obj]).
*)

val declare_numeral_interpreter : ?local:bool -> scope_name -> required_module ->
  Bigint.bigint prim_token_interpreter ->
  glob_constr list * Bigint.bigint prim_token_uninterpreter * bool -> unit
val declare_string_interpreter : ?local:bool -> scope_name -> required_module ->
  string prim_token_interpreter ->
  glob_constr list * string prim_token_uninterpreter * bool -> unit

(** Return the [term]/[cases_pattern] bound to a primitive token in a
   given scope context*)

val interp_prim_token : ?loc:Loc.t -> prim_token -> subscopes ->
  glob_constr * (notation_location * scope_name option)
(* This function returns a glob_const representing a pattern *)
val interp_prim_token_cases_pattern_expr : ?loc:Loc.t -> (GlobRef.t -> unit) -> prim_token ->
  subscopes -> glob_constr * (notation_location * scope_name option)

(** Return the primitive token associated to a [term]/[cases_pattern];
   raise [No_match] if no such token *)

val uninterp_prim_token :
  'a glob_constr_g -> scope_name * prim_token
val uninterp_prim_token_cases_pattern :
  'a cases_pattern_g -> Name.t * scope_name * prim_token

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

type notation_rule = interp_rule * interpretation * int option

(** Return the possible notations for a given term *)
val uninterp_notations : 'a glob_constr_g -> notation_rule list
val uninterp_cases_pattern_notations : 'a cases_pattern_g -> notation_rule list
val uninterp_ind_pattern_notations : inductive -> notation_rule list

(** Test if a notation is available in the scopes 
   context [scopes]; if available, the result is not None; the first 
   argument is itself not None if a delimiters is needed *)
val availability_of_notation : scope_name option * notation -> subscopes ->
  (scope_name option * delimiters option) option

(** {6 Miscellaneous} *)

val interp_notation_as_global_reference : ?loc:Loc.t -> (GlobRef.t -> bool) ->
      notation_key -> delimiters option -> GlobRef.t

(** Checks for already existing notations *)
val exists_notation_in_scope : scope_name option -> notation ->
      bool -> interpretation -> bool

(** Declares and looks for scopes associated to arguments of a global ref *)
val declare_arguments_scope :
  bool (** true=local *) -> GlobRef.t -> scope_name option list -> unit

val find_arguments_scope : GlobRef.t -> scope_name option list

type scope_class

(** Comparison of scope_class *)
val scope_class_compare : scope_class -> scope_class -> int

val subst_scope_class :
  Mod_subst.substitution -> scope_class -> scope_class option

val declare_scope_class : scope_name -> scope_class -> unit
val declare_ref_arguments_scope : Evd.evar_map -> GlobRef.t -> unit

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
val make_notation_key : notation_entry_level -> symbol list -> notation
val decompose_notation_key : notation -> notation_entry_level * symbol list

(** Decompose a notation of the form "a 'U' b" *)
val decompose_raw_notation : string -> symbol list

(** Prints scopes (expects a pure aconstr printer) *)
val pr_scope_class : scope_class -> Pp.t
val pr_scope : (glob_constr -> Pp.t) -> scope_name -> Pp.t
val pr_scopes : (glob_constr -> Pp.t) -> Pp.t
val locate_notation : (glob_constr -> Pp.t) -> notation_key ->
      scope_name option -> Pp.t

val pr_visibility: (glob_constr -> Pp.t) -> scope_name option -> Pp.t

type entry_coercion = notation list
val declare_entry_coercion : notation -> notation_entry_level -> unit
val availability_of_entry_coercion : notation_entry_level -> notation_entry_level -> entry_coercion option

val declare_custom_entry_has_global : string -> int -> unit
val declare_custom_entry_has_ident : string -> int -> unit

val entry_has_global : notation_entry_level -> bool
val entry_has_ident : notation_entry_level -> bool

(** Rem: printing rules for primitive token are canonical *)

val with_notation_protection : ('a -> 'b) -> 'a -> 'b
