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
open Constr
open Environ
open Declarations
open Mod_declarations
open Entries
open Mod_subst

(** {6 Various operations on modules and module types } *)

(** Functors *)

val is_functor : ('ty,'a) functorize -> bool

val destr_functor : ('ty,'a) functorize -> MBId.t * 'ty * ('ty,'a) functorize

val destr_nofunctor : ModPath.t -> ('ty,'a) functorize -> 'a

val check_modpath_equiv : env -> ModPath.t -> ModPath.t -> unit

val annotate_module_expression : module_expression -> module_signature ->
  (module_type_body, (constr * UVars.AbstractContext.t option) module_alg_expr) functorize

val annotate_struct_body : structure_body -> module_signature -> module_signature

(** {6 Substitutions } *)

val subst_signature : substitution -> ModPath.t -> module_signature -> module_signature
val subst_structure : substitution -> ModPath.t -> structure_body -> structure_body

(** {6 Adding to an environment } *)

val add_structure :
  ModPath.t -> structure_body -> delta_resolver -> env -> env

(** adds a module and its components, but not the constraints *)
val add_module : ModPath.t -> module_body -> env -> env

(** same as add_module, but for a module whose native code has been linked by
the native compiler. The linking information is updated. *)
val add_linked_module : ModPath.t -> module_body -> link_info -> env -> env

(** add an abstract module parameter to the environment *)
val add_module_parameter : MBId.t -> module_type_body -> env -> env

val add_retroknowledge : Retroknowledge.action list -> env -> env

(** {6 Strengthening } *)

val strengthen : module_type_body -> ModPath.t -> module_type_body

(** Strengthening of a single constant field [l] of the module [mp], w.r.t.
    the delta resolver of that module. Used to strengthen fields on demand
    instead of strengthening a whole signature eagerly. *)
val strengthen_const :
  ModPath.t -> Id.t -> constant_body -> delta_resolver -> constant_body

(** Strengthening of a single module field of a signature, as performed on
    submodules by [strengthen]. *)
val strengthen_module : ModPath.t -> module_body -> module_body

val strengthen_and_subst_module_body : ModPath.t -> module_body -> ModPath.t -> bool -> module_body

val subst_modtype_signature_and_resolver : ModPath.t -> ModPath.t ->
  module_signature -> delta_resolver -> module_signature * delta_resolver

(** {6 Building map of constants to inline } *)

val inline_delta_resolver :
  env -> inline -> ModPath.t -> MBId.t -> module_type_body ->
  delta_resolver -> delta_resolver

(** {6 Cleaning a module expression from bounded parts }

     For instance:
       functor(X:T)->struct module M:=X end)
     becomes:
       functor(X:T)->struct module M:=<content of T> end)
*)

val clean_bounded_mod_expr : module_signature -> module_signature

(** {6 Errors } *)

type signature_mismatch_error =
  | InductiveFieldExpected of mutual_inductive_body
  | DefinitionFieldExpected
  | ModuleFieldExpected
  | ModuleTypeFieldExpected
  | NotConvertibleInductiveField of Id.t * (env * types * types) option
  | NotConvertibleConstructorField of Id.t * (env * types * types) option
  | NotConvertibleBodyField of (env * constr * constr) option
  | NotConvertibleTypeField of env * types * types
  | CumulativeStatusExpected of bool
  | PolymorphicStatusExpected of bool
  | NotSameConstructorNamesField of Id.t array * Id.t array
  | NotSameInductiveNameInBlockField of Id.t * Id.t
  | FiniteInductiveFieldExpected of bool
  | InductiveNumbersFieldExpected of { got : int; expected : int }
  | InductiveParams of { env : Environ.env; got : rel_context; expected : rel_context }
  | RecordFieldExpected of bool
  | RecordProjectionsExpected of { expected : Name.t list; got : Name.t list }
  | NotEqualInductiveAliases of MutInd.t * MutInd.t
  | IncompatibleUniverses of { err : UGraph.univ_inconsistency; env : env; t1 : types; t2 : types }
  | IncompatibleQualities of { err : QGraph.elimination_error; env : env; t1 : types; t2 : types }
  | IncompatiblePolymorphism of env * types * types
  | IncompatibleUnivConstraints of { env : env; got : UVars.AbstractContext.t; expect : UVars.AbstractContext.t }
  | IncompatibleVariance
  | NoRewriteRulesSubtyping

type with_constraint_error =
  | WithSignatureMismatch of signature_mismatch_error
  | WithCannotConstrainPrimitive
  | WithCannotConstrainSymbol

type subtyping_trace_elt =
  | Submodule of Id.t
  | FunctorArgument of int

type module_typing_error =
  | SignatureMismatch of subtyping_trace_elt list * Id.t * signature_mismatch_error
  | LabelAlreadyDeclared of Id.t
  | NotAFunctor
  | IsAFunctor of ModPath.t
  | IncompatibleModuleTypes of module_type_body * module_type_body
  | NotEqualModulePaths of ModPath.t * ModPath.t
  | NoSuchLabel of Id.t * ModPath.t
  | NotAModuleLabel of Id.t
  | NotAConstant of Id.t
  | IncorrectWithConstraint of Id.t * with_constraint_error
  | GenerativeModuleExpected of Id.t
  | LabelMissing of Id.t * string
  | IncludeRestrictedFunctor of ModPath.t

exception ModuleTypingError of module_typing_error

val error_existing_label : Id.t -> 'a

val error_incompatible_modtypes :
  module_type_body -> module_type_body -> 'a

val error_signature_mismatch :
  subtyping_trace_elt list -> Id.t -> signature_mismatch_error -> 'a

val error_no_such_label : Id.t -> ModPath.t -> 'a

val error_not_a_module_label : Id.t -> 'a

val error_not_a_constant : Id.t -> 'a

val error_incorrect_with_constraint : Id.t -> with_constraint_error -> 'a

val error_generative_module_expected : Id.t -> 'a

val error_no_such_label_sub : Id.t -> string -> 'a

val error_include_restricted_functor : ModPath.t -> 'a
