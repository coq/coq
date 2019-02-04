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
open Constr
open Environ
open Declarations
open Entries
open Mod_subst

(** {6 Various operations on modules and module types } *)

(** Functors *)

val is_functor : ('ty,'a) functorize -> bool

val destr_functor : ('ty,'a) functorize -> MBId.t * 'ty * ('ty,'a) functorize

val destr_nofunctor : ('ty,'a) functorize -> 'a

(** Conversions between [module_body] and [module_type_body] *)

val module_type_of_module : module_body -> module_type_body
val module_body_of_type : ModPath.t -> module_type_body -> module_body

val check_modpath_equiv : env -> ModPath.t -> ModPath.t -> unit

val implem_smartmap :
  (module_signature -> module_signature) ->
  (module_expression -> module_expression) ->
  (module_implementation -> module_implementation)

(** {6 Substitutions } *)

val subst_signature : substitution -> module_signature -> module_signature
val subst_structure : substitution -> structure_body -> structure_body

(** {6 Adding to an environment } *)

val add_structure :
  ModPath.t -> structure_body -> delta_resolver -> env -> env

(** adds a module and its components, but not the constraints *)
val add_module : module_body -> env -> env

(** same as add_module, but for a module whose native code has been linked by
the native compiler. The linking information is updated. *)
val add_linked_module : module_body -> link_info -> env -> env

(** same, for a module type *)
val add_module_type : ModPath.t -> module_type_body -> env -> env

val add_retroknowledge : module_implementation module_retroknowledge -> env -> env

(** {6 Strengthening } *)

val strengthen : module_type_body -> ModPath.t -> module_type_body

val inline_delta_resolver :
  env -> inline -> ModPath.t -> MBId.t -> module_type_body ->
  delta_resolver -> delta_resolver

val strengthen_and_subst_mb : module_body -> ModPath.t -> bool -> module_body

val subst_modtype_and_resolver : module_type_body -> ModPath.t ->
  module_type_body

(** {6 Cleaning a module expression from bounded parts }

     For instance:
       functor(X:T)->struct module M:=X end)
     becomes:
       functor(X:T)->struct module M:=<content of T> end)
*)

val clean_bounded_mod_expr : module_signature -> module_signature

(** {6 Stm machinery } *)

val join_structure :
  Future.UUIDSet.t -> Opaqueproof.opaquetab -> structure_body -> unit

(** {6 Errors } *)

type signature_mismatch_error =
  | InductiveFieldExpected of mutual_inductive_body
  | DefinitionFieldExpected
  | ModuleFieldExpected
  | ModuleTypeFieldExpected
  | NotConvertibleInductiveField of Id.t
  | NotConvertibleConstructorField of Id.t
  | NotConvertibleBodyField
  | NotConvertibleTypeField of env * types * types
  | CumulativeStatusExpected of bool
  | PolymorphicStatusExpected of bool
  | NotSameConstructorNamesField
  | NotSameInductiveNameInBlockField
  | FiniteInductiveFieldExpected of bool
  | InductiveNumbersFieldExpected of int
  | InductiveParamsNumberField of int
  | RecordFieldExpected of bool
  | RecordProjectionsExpected of Name.t list
  | NotEqualInductiveAliases
  | IncompatibleUniverses of Univ.univ_inconsistency
  | IncompatiblePolymorphism of env * types * types
  | IncompatibleConstraints of { got : Univ.AUContext.t; expect : Univ.AUContext.t }

type module_typing_error =
  | SignatureMismatch of
      Label.t * structure_field_body * signature_mismatch_error
  | LabelAlreadyDeclared of Label.t
  | ApplicationToNotPath of module_struct_entry
  | NotAFunctor
  | IsAFunctor
  | IncompatibleModuleTypes of module_type_body * module_type_body
  | NotEqualModulePaths of ModPath.t * ModPath.t
  | NoSuchLabel of Label.t
  | IncompatibleLabels of Label.t * Label.t
  | NotAModule of string
  | NotAModuleType of string
  | NotAConstant of Label.t
  | IncorrectWithConstraint of Label.t
  | GenerativeModuleExpected of Label.t
  | LabelMissing of Label.t * string
  | IncludeRestrictedFunctor of ModPath.t

exception ModuleTypingError of module_typing_error

val error_existing_label : Label.t -> 'a

val error_incompatible_modtypes :
  module_type_body -> module_type_body -> 'a

val error_signature_mismatch :
  Label.t -> structure_field_body -> signature_mismatch_error -> 'a

val error_incompatible_labels : Label.t -> Label.t -> 'a

val error_no_such_label : Label.t -> 'a

val error_not_a_module : string -> 'a

val error_not_a_constant : Label.t -> 'a

val error_incorrect_with_constraint : Label.t -> 'a

val error_generative_module_expected : Label.t -> 'a

val error_no_such_label_sub : Label.t->string->'a

val error_include_restricted_functor : ModPath.t -> 'a
