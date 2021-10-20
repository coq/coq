(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

type section_data

val empty_environment : safe_environment

val is_initial : safe_environment -> bool

val env_of_safe_env : safe_environment -> Environ.env

val sections_of_safe_env : safe_environment -> section_data Section.t option

val structure_body_of_safe_env : safe_environment -> Declarations.structure_body

(** The safe_environment state monad *)

type safe_transformer0 = safe_environment -> safe_environment
type 'a safe_transformer = safe_environment -> 'a * safe_environment


(** {6 Stm machinery } *)

type private_constants

val empty_private_constants : private_constants
val is_empty_private_constants : private_constants -> bool

val concat_private : private_constants -> private_constants -> private_constants
(** [concat_private e1 e2] adds the constants of [e1] to [e2], i.e. constants in
    [e1] must be more recent than those of [e2]. *)

val inline_private_constants :
  Environ.env -> private_constants Entries.proof_output -> Constr.constr Univ.in_universe_context_set

val push_private_constants : Environ.env -> private_constants -> Environ.env
(** Push the constants in the environment if not already there. *)

val universes_of_private : private_constants -> Univ.ContextSet.t

val is_curmod_library : safe_environment -> bool

val is_joined_environment : safe_environment -> bool
(** {6 Enriching a safe environment } *)

(** Insertion of global axioms or definitions *)

type global_declaration =
| ConstantEntry : Entries.constant_entry -> global_declaration
| OpaqueEntry : unit Entries.opaque_entry -> global_declaration

type side_effect_declaration =
| DefinitionEff : Entries.definition_entry -> side_effect_declaration
| OpaqueEff : Constr.constr Entries.opaque_entry -> side_effect_declaration

type exported_opaque
type exported_private_constant = Constant.t * exported_opaque option

val repr_exported_opaque : exported_opaque -> Opaqueproof.opaque_handle * Opaqueproof.opaque_proofterm

val export_private_constants :
  private_constants ->
  exported_private_constant list safe_transformer

(** returns the main constant *)
val add_constant :
  ?typing_flags:Declarations.typing_flags ->
  Label.t -> global_declaration -> Constant.t safe_transformer

(** Similar to add_constant but also returns a certificate *)
val add_private_constant :
  Label.t -> Univ.ContextSet.t -> side_effect_declaration -> (Constant.t * private_constants) safe_transformer

(** {5 Delayed proofs} *)

(** Witness that a delayed Qed hole has a proof. This datatype is marshallable
    but care must be taken to marshal it at the same time as the environment
    it is referring to, since {!fill_opaque} relies on a shared pointer between
    the environment and the certificate. *)
type opaque_certificate

(** Check that the provided proof is correct for the corresponding handle. This
    does not modify the environment. Call {!fill_opaque} below for that. *)
val check_opaque : safe_environment -> Opaqueproof.opaque_handle ->
  private_constants Entries.proof_output -> opaque_certificate

(** Given an already checked proof for an opaque hole, actually fill it with the
    proof. This might fail if the current set of global universes is
    inconsistent with the one at the time of the call to {!check_opaque}.
    Precondition: the underlying handle must exist and must not have been
    filled. *)
val fill_opaque : opaque_certificate -> safe_transformer0

(** Check whether a handle was filled. It assumes that the handle was introduced
    in the opaque table and throws an anomaly otherwise. *)
val is_filled_opaque : Opaqueproof.opaque_handle -> safe_environment -> bool

(** Get the proof term that was checked by the kernel. *)
val repr_certificate : opaque_certificate ->
  Constr.t * Univ.ContextSet.t Opaqueproof.delayed_universes

(** {5 Inductive blocks} *)

(** Adding an inductive type *)

val add_mind :
  ?typing_flags:Declarations.typing_flags ->
  Label.t -> Entries.mutual_inductive_entry ->
    MutInd.t safe_transformer

(** Adding a module or a module type *)

val add_module :
  Label.t -> Entries.module_entry -> Declarations.inline ->
    (ModPath.t * Mod_subst.delta_resolver) safe_transformer
val add_modtype :
  Label.t -> Entries.module_type_entry -> Declarations.inline ->
    ModPath.t safe_transformer

(** Adding universe constraints *)

val push_context_set :
  strict:bool -> Univ.ContextSet.t -> safe_transformer0

val add_constraints :
  Univ.Constraints.t -> safe_transformer0

(* (\** Generator of universes *\) *)
(* val next_universe : int safe_transformer *)

(** Setting the type theory flavor *)
val set_impredicative_set : bool -> safe_transformer0
val set_indices_matter : bool -> safe_transformer0
val set_typing_flags : Declarations.typing_flags -> safe_transformer0
val set_share_reduction : bool -> safe_transformer0
val set_check_guarded : bool -> safe_transformer0
val set_check_positive : bool -> safe_transformer0
val set_check_universes : bool -> safe_transformer0
val set_VM : bool -> safe_transformer0
val set_native_compiler : bool -> safe_transformer0
val set_allow_sprop : bool -> safe_transformer0

(** {6 Interactive section functions } *)

val open_section : safe_transformer0

val close_section : safe_transformer0

val sections_are_opened : safe_environment -> bool

(** Insertion of local declarations (Local or Variables) *)

val push_named_assum : (Id.t * Constr.types) -> safe_transformer0

val push_named_def :
  Id.t * Entries.section_def_entry -> safe_transformer0

(** Add local universes to a polymorphic section *)
val push_section_context : Univ.UContext.t -> safe_transformer0

(** {6 Interactive module functions } *)

val start_module : Label.t -> ModPath.t safe_transformer

val start_modtype : Label.t -> ModPath.t safe_transformer

val add_module_parameter :
  MBId.t -> Entries.module_struct_entry -> Declarations.inline ->
    Mod_subst.delta_resolver safe_transformer

(** returns the number of module (type) parameters following the nested module
    structure. The inner module (type) comes first in the list. *)
val module_num_parameters : safe_environment -> int list

(** returns true if the module is a module type following the nested module
    structure. The inner module (type) comes first in the list. true means
    a module type, false a regular module *)
val module_is_modtype : safe_environment -> bool list

(** Traditional mode: check at end of module that no future was
    created. *)
val allow_delayed_constants : bool ref

(** The optional result type is given without its functorial part *)

val end_module :
  Label.t -> (Entries.module_struct_entry * Declarations.inline) option ->
    (ModPath.t * MBId.t list * Mod_subst.delta_resolver) safe_transformer

val end_modtype : Label.t -> (ModPath.t * MBId.t list) safe_transformer

val add_include :
  Entries.module_struct_entry -> bool -> Declarations.inline ->
   Mod_subst.delta_resolver safe_transformer

val current_modpath : safe_environment -> ModPath.t

val current_dirpath : safe_environment -> DirPath.t

(** {6 Libraries : loading and saving compilation units } *)

type compiled_library

val module_of_library : compiled_library -> Declarations.module_body
val univs_of_library : compiled_library -> Univ.ContextSet.t

val start_library : DirPath.t -> ModPath.t safe_transformer

val export :
  output_native_objects:bool ->
  safe_environment -> DirPath.t ->
    ModPath.t * compiled_library * Nativelib.native_library

(* Constraints are non empty iff the file is a vi2vo *)
val import : compiled_library -> Univ.ContextSet.t -> vodigest ->
  ModPath.t safe_transformer

(** {6 Safe typing judgments } *)

type judgment

val j_val : judgment -> Constr.constr
val j_type : judgment -> Constr.constr

(** The safe typing of a term returns a typing judgment. *)
val typing : safe_environment -> Constr.constr -> judgment

(** {6 Queries } *)

val exists_objlabel : Label.t -> safe_environment -> bool

val delta_of_senv :
  safe_environment -> Mod_subst.delta_resolver * Mod_subst.delta_resolver

val constant_of_delta_kn_senv : safe_environment -> KerName.t -> Constant.t
val mind_of_delta_kn_senv : safe_environment -> KerName.t -> MutInd.t

(** {6 Retroknowledge / Native compiler } *)

val register_inline : Constant.t -> safe_transformer0
val register_inductive : inductive -> 'a CPrimitives.prim_ind -> safe_transformer0

val set_strategy :
  Names.Constant.t Names.tableKey -> Conv_oracle.level -> safe_transformer0
