(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

type vodigest =
  | Dvo_or_vi of Digest.t        (* The digest of the seg_lib part *)
  | Dvivo of Digest.t * Digest.t (* The digest of the seg_lib + seg_univ part *)

val digest_match : actual:vodigest -> required:vodigest -> bool

(** {6 Safe environments } *)

(** Since we are now able to type terms, we can define an abstract type
    of safe environments, where objects are typed before being added.

    We also provide functionality for modules : [start_module], [end_module],
    etc.
*)

type safe_environment

val empty_environment : safe_environment

val is_initial : safe_environment -> bool

val env_of_safe_env : safe_environment -> Environ.env

(** The safe_environment state monad *)

type safe_transformer0 = safe_environment -> safe_environment
type 'a safe_transformer = safe_environment -> 'a * safe_environment


(** {6 Stm machinery } *)

val sideff_of_con : safe_environment -> constant -> Declarations.side_effect
val sideff_of_scheme :
  string -> safe_environment -> (inductive * constant) list ->
    Declarations.side_effect

val is_curmod_library : safe_environment -> bool

(* safe_environment has functional data affected by lazy computations,
 * thus this function returns a new safe_environment *)
val join_safe_environment :
  ?except:Future.UUIDSet.t -> safe_environment -> safe_environment

(** {6 Enriching a safe environment } *)

(** Insertion of local declarations (Local or Variables) *)

val push_named_assum :
  (Id.t * Term.types) Univ.in_universe_context_set -> safe_transformer0
val push_named_def :
  Id.t * Entries.definition_entry -> safe_transformer0

(** Insertion of global axioms or definitions *)

type global_declaration =
  | ConstantEntry of Entries.constant_entry
  | GlobalRecipe of Cooking.recipe

val add_constant :
  DirPath.t -> Label.t -> global_declaration -> constant safe_transformer

(** Adding an inductive type *)

val add_mind :
  DirPath.t -> Label.t -> Entries.mutual_inductive_entry ->
    mutual_inductive safe_transformer

(** Adding a module or a module type *)

val add_module :
  Label.t -> Entries.module_entry -> Declarations.inline ->
    (module_path * Mod_subst.delta_resolver) safe_transformer
val add_modtype :
  Label.t -> Entries.module_type_entry -> Declarations.inline ->
    module_path safe_transformer

(** Adding universe constraints *)

val push_context_set :
  Univ.universe_context_set -> safe_transformer0

val push_context :
  Univ.universe_context -> safe_transformer0

val add_constraints :
  Univ.constraints -> safe_transformer0

(* (\** Generator of universes *\) *)
(* val next_universe : int safe_transformer *)

(** Setting the strongly constructive or classical logical engagement *)
val set_engagement : Declarations.engagement -> safe_transformer0

(** Collapsing the type hierarchy *)
val set_type_in_type : safe_transformer0

(** {6 Interactive module functions } *)

val start_module : Label.t -> module_path safe_transformer

val start_modtype : Label.t -> module_path safe_transformer

val add_module_parameter :
  MBId.t -> Entries.module_struct_entry -> Declarations.inline ->
    Mod_subst.delta_resolver safe_transformer

(** The optional result type is given without its functorial part *)

val end_module :
  Label.t -> (Entries.module_struct_entry * Declarations.inline) option ->
    (module_path * MBId.t list * Mod_subst.delta_resolver) safe_transformer

val end_modtype : Label.t -> (module_path * MBId.t list) safe_transformer

val add_include :
  Entries.module_struct_entry -> bool -> Declarations.inline ->
   Mod_subst.delta_resolver safe_transformer

val current_modpath : safe_environment -> module_path

val current_dirpath : safe_environment -> dir_path

(** {6 Libraries : loading and saving compilation units } *)

type compiled_library

type native_library = Nativecode.global list

val start_library : DirPath.t -> module_path safe_transformer

val export :
  ?except:Future.UUIDSet.t ->
  safe_environment -> DirPath.t ->
    module_path * compiled_library * native_library

(* Constraints are non empty iff the file is a vi2vo *)
val import : compiled_library -> Univ.universe_context_set -> vodigest ->
  (module_path * Nativecode.symbol array) safe_transformer

(** {6 Safe typing judgments } *)

type judgment

val j_val : judgment -> Term.constr
val j_type : judgment -> Term.constr

(** The safe typing of a term returns a typing judgment. *)
val typing : safe_environment -> Term.constr -> judgment

(** {6 Queries } *)

val exists_objlabel : Label.t -> safe_environment -> bool

val delta_of_senv :
  safe_environment -> Mod_subst.delta_resolver * Mod_subst.delta_resolver

(** {6 Retroknowledge / Native compiler } *)

open Retroknowledge

val retroknowledge : (retroknowledge-> 'a) -> safe_environment -> 'a

val register :
  field -> Retroknowledge.entry -> Term.constr -> safe_transformer0

val register_inline : constant -> safe_transformer0

val set_strategy :
  safe_environment -> Names.constant Names.tableKey -> Conv_oracle.level -> safe_environment
