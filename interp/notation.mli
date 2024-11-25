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

type notation_location = (DirPath.t * DirPath.t) * string
(** 1st dirpath: dirpath of the library
    2nd dirpath: module and section-only dirpath (ie [Lib.current_dirpath true])
    string: string used to generate the notation

    dirpaths are used for dumpglob, string for printing (pr_notation_info)
*)

type required_module = full_path * string list
type rawnum = NumTok.Signed.t

(** The unique id string below will be used to refer to a particular
    registered interpreter/uninterpreter of number or string notation.
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
  ?allow_overwrite:bool -> prim_token_uid -> Z.t prim_token_interpretation -> unit

val register_string_interpretation :
  ?allow_overwrite:bool -> prim_token_uid -> string prim_token_interpretation -> unit

(** * Number notation *)

type prim_token_notation_error =
  | UnexpectedTerm of Constr.t
  | UnexpectedNonOptionTerm of Constr.t

exception PrimTokenNotationError of string * Environ.env * Evd.evar_map * prim_token_notation_error

type numnot_option =
  | Nop
  | Warning of NumTok.UnsignedNat.t
  | Abstract of NumTok.UnsignedNat.t

type int_ty =
  { dec_uint : Names.inductive;
    dec_int : Names.inductive;
    hex_uint : Names.inductive;
    hex_int : Names.inductive;
    uint : Names.inductive;
    int : Names.inductive }

type z_pos_ty =
  { z_ty : Names.inductive;
    pos_ty : Names.inductive }

type number_ty =
  { int : int_ty;
    decimal : Names.inductive;
    hexadecimal : Names.inductive;
    number : Names.inductive }

type pos_neg_int63_ty =
  { pos_neg_int63_ty : Names.inductive }

type target_kind =
  | Int of int_ty (* Corelib.Init.Number.int + uint *)
  | UInt of int_ty (* Corelib.Init.Number.uint *)
  | Z of z_pos_ty (* Corelib.Numbers.BinNums.Z and positive *)
  | Int63 of pos_neg_int63_ty (* Corelib.Numbers.Cyclic.Int63.PrimInt63.pos_neg_int63 *)
  | Float64 (* Corelib.Floats.PrimFloat.float *)
  | Number of number_ty (* Corelib.Init.Number.number + uint + int *)

type string_target_kind =
  | ListByte
  | Byte
  | PString

type option_kind = Option | Direct
type 'target conversion_kind = 'target * option_kind

(** A postprocessing translation [to_post] can be done after execution
   of the [to_ty] interpreter. The reverse translation is performed
   before the [of_ty] uninterpreter.

   [to_post] is an array of [n] lists [l_i] of tuples [(f, t,
   args)]. When the head symbol of the translated term matches one of
   the [f] in the list [l_0] it is replaced by [t] and its arguments
   are translated acording to [args] where [ToPostCopy] means that the
   argument is kept unchanged and [ToPostAs k] means that the
   argument is recursively translated according to [l_k].
   [ToPostHole] introduces an additional implicit argument hole
   (in the reverse translation, the corresponding argument is removed).
   [ToPostCheck r] behaves as [ToPostCopy] except in the reverse
   translation which fails if the copied term is not [r].
   When [n] is null, no translation is performed. *)
type to_post_arg = ToPostCopy | ToPostAs of int | ToPostHole | ToPostCheck of Constr.t
type ('target, 'warning) prim_token_notation_obj =
  { to_kind : 'target conversion_kind;
    to_ty : GlobRef.t;
    to_post : ((GlobRef.t * GlobRef.t * to_post_arg list) list) array;
    of_kind : 'target conversion_kind;
    of_ty : GlobRef.t;
    ty_name : Libnames.qualid; (* for warnings / error messages *)
    warning : 'warning }

type number_notation_obj = (target_kind, numnot_option) prim_token_notation_obj
type string_notation_obj = (string_target_kind, unit) prim_token_notation_obj

type prim_token_interp_info =
    Uid of prim_token_uid
  | NumberNotation of number_notation_obj
  | StringNotation of string_notation_obj

type prim_token_infos = {
  pt_local : bool; (** Is this interpretation local? *)
  pt_scope : scope_name; (** Concerned scope *)
  pt_interp_info : prim_token_interp_info; (** Unique id "pointing" to (un)interp functions, OR a number notation object describing (un)interp functions *)
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
  glob_constr * scope_name option
(* This function returns a glob_const representing a pattern *)
val interp_prim_token_cases_pattern_expr : ?loc:Loc.t -> (Glob_term.glob_constr -> unit) -> prim_token ->
  subscopes -> glob_constr * scope_name option

(** Return the primitive token associated to a [term]/[cases_pattern];
   raise [No_match] if no such token *)

val uninterp_prim_token :
  'a glob_constr_g -> subscopes -> prim_token * delimiters option
val uninterp_prim_token_cases_pattern :
  'a cases_pattern_g -> subscopes -> Name.t * prim_token * delimiters option

val availability_of_prim_token :
  prim_token -> scope_name -> subscopes -> delimiters option option

(** {6 Declare and interpret back and forth a notation } *)

val warning_overridden_name : string

type entry_coercion_kind =
  | IsEntryCoercion of notation_entry_level * notation_entry_relative_level
  | IsEntryGlobal of string * int
  | IsEntryIdent of string * int

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
  (notation_entry * notation_key) * notation_key * notation_with_optional_scope * interpretation * GlobRef.t

(** Declares and looks for scopes associated to arguments of a global ref *)
val declare_arguments_scope :
  bool (** true=local *) -> GlobRef.t -> scope_name list list -> unit

val find_arguments_scope : GlobRef.t -> scope_name list list

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

type notation_symbols = {
  recvars : (Id.t * Id.t) list; (* pairs (x,y) as in [ x ; .. ; y ] *)
  mainvars : Id.t list; (* variables non involved in a recursive pattern *)
  symbols : symbol list; (* the decomposition of the notation into terminals and nonterminals *)
}

val is_prim_token_constant_in_constr :
  notation_entry * symbol list -> bool

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

val declare_custom_entry_has_global : string -> int -> unit
val declare_custom_entry_has_ident : string -> int -> unit

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

(** Conversion from bigint to int63 *)
val int63_of_pos_bigint : Z.t -> Uint63.t
