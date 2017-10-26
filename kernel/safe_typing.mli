(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
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

type private_constant
type private_constants

type private_constant_role =
  | Subproof
  | Schema of inductive * string

val side_effects_of_private_constants :
  private_constants -> Entries.side_effect list
(** Return the list of individual side-effects in the order of their
    creation. *)

val empty_private_constants : private_constants
val add_private : private_constant -> private_constants -> private_constants
(** Add a constant to a list of private constants. The former must be more
    recent than all constants appearing in the latter, i.e. one should not
    create a dependency cycle. *)
val concat_private : private_constants -> private_constants -> private_constants
(** [concat_private e1 e2] adds the constants of [e1] to [e2], i.e. constants in
    [e1] must be more recent than those of [e2]. *)

val private_con_of_con : safe_environment -> constant -> private_constant
val private_con_of_scheme : kind:string -> safe_environment -> (inductive * constant) list -> private_constant

val mk_pure_proof : Constr.constr -> private_constants Entries.proof_output
val inline_private_constants_in_constr :
  Environ.env -> Constr.constr -> private_constants -> Constr.constr
val inline_private_constants_in_definition_entry :
  Environ.env -> private_constants Entries.definition_entry -> unit Entries.definition_entry

val universes_of_private : private_constants -> Univ.universe_context_set list

val is_curmod_library : safe_environment -> bool

(* safe_environment has functional data affected by lazy computations,
 * thus this function returns a new safe_environment *)
val join_safe_environment :
  ?except:Future.UUIDSet.t -> safe_environment -> safe_environment

val is_joined_environment : safe_environment -> bool
(** {6 Enriching a safe environment } *)

(** Insertion of local declarations (Local or Variables) *)

val push_named_assum :
  (Id.t * Term.types * bool (* polymorphic *))
    Univ.in_universe_context_set -> safe_transformer0

(** Returns the full universe context necessary to typecheck the definition
  (futures are forced) *)
val push_named_def :
  Id.t * private_constants Entries.definition_entry -> Univ.universe_context_set safe_transformer

(** Insertion of global axioms or definitions *)

type 'a effect_entry =
| EffectEntry : private_constants effect_entry
| PureEntry : unit effect_entry

type global_declaration =
  | ConstantEntry : 'a effect_entry * 'a Entries.constant_entry -> global_declaration
  | GlobalRecipe of Cooking.recipe

type exported_private_constant = 
  constant * private_constant_role

val export_private_constants : in_section:bool ->
  private_constants Entries.constant_entry ->
  (unit Entries.constant_entry * exported_private_constant list) safe_transformer

(** returns the main constant plus a list of auxiliary constants (empty
    unless one requires the side effects to be exported) *)
val add_constant :
  DirPath.t -> Label.t -> global_declaration ->
    constant safe_transformer

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
  bool -> Univ.universe_context_set -> safe_transformer0

val push_context :
  bool -> Univ.universe_context -> safe_transformer0

val add_constraints :
  Univ.constraints -> safe_transformer0

(* (\** Generator of universes *\) *)
(* val next_universe : int safe_transformer *)

(** Setting the type theory flavor *)
val set_engagement : Declarations.engagement -> safe_transformer0
val set_typing_flags : Declarations.typing_flags -> safe_transformer0

(** {6 Interactive module functions } *)

val start_module : Label.t -> module_path safe_transformer

val start_modtype : Label.t -> module_path safe_transformer

val add_module_parameter :
  MBId.t -> Entries.module_struct_entry -> Declarations.inline ->
    Mod_subst.delta_resolver safe_transformer

(** Traditional mode: check at end of module that no future was
    created. *)
val allow_delayed_constants : bool ref

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

val get_library_native_symbols : safe_environment -> DirPath.t -> Nativecode.symbols

val start_library : DirPath.t -> module_path safe_transformer

val export :
  ?except:Future.UUIDSet.t ->
  safe_environment -> DirPath.t ->
    module_path * compiled_library * native_library

(* Constraints are non empty iff the file is a vi2vo *)
val import : compiled_library -> Univ.universe_context_set -> vodigest ->
  module_path safe_transformer

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
