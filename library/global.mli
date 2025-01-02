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
open Declarations
open Mod_declarations

(** This module defines the global environment of Rocq. The functions
   below are exactly the same as the ones in [Safe_typing], operating on
   that global environment. [add_*] functions perform name verification,
   i.e. check that the name given as argument match those provided by
   [Safe_typing]. *)

val safe_env : unit -> Safe_typing.safe_environment
val env : unit -> Environ.env

val universes : unit -> UGraph.t
val named_context_val : unit -> Environ.named_context_val
val named_context : unit -> Constr.named_context

(** {6 Enriching the global environment } *)

(** Changing the (im)predicativity of the system *)
val set_impredicative_set : bool -> unit

val set_indices_matter : bool -> unit
val set_typing_flags : typing_flags -> unit
val set_check_guarded : bool -> unit
val set_check_positive : bool -> unit
val set_check_universes : bool -> unit
val typing_flags : unit -> typing_flags
val set_allow_sprop : bool -> unit
val sprop_allowed : unit -> bool
val set_rewrite_rules_allowed : bool -> unit
val rewrite_rules_allowed : unit -> bool

(** Variables, Local definitions, constants, inductive types *)

val push_named_assum : (Id.t * Constr.types) -> unit
val push_named_def   : (Id.t * Entries.section_def_entry) -> unit
val push_section_context : UVars.UContext.t -> unit

val export_private_constants :
  Safe_typing.private_constants ->
  Safe_typing.exported_private_constant list

val add_constant :
  ?typing_flags:typing_flags ->
  Id.t -> Entries.constant_entry -> Constant.t
val fill_opaque : Safe_typing.opaque_certificate -> unit
val add_private_constant :
  Id.t -> Univ.ContextSet.t -> Safe_typing.side_effect_declaration -> Constant.t * Safe_typing.private_constants
val add_rewrite_rules : Id.t -> rewrite_rules_body -> unit
val add_mind :
  ?typing_flags:typing_flags ->
  Id.t -> Entries.mutual_inductive_entry ->
  MutInd.t * IndTyping.NotPrimRecordReason.t option

(** Extra universe constraints *)
val add_constraints : Univ.Constraints.t -> unit

val push_context_set : Univ.ContextSet.t -> unit

(** Non-interactive modules and module types *)

val add_module :
  Id.t -> Entries.module_entry -> inline ->
    ModPath.t * Mod_subst.delta_resolver
val add_modtype :
  Id.t -> Entries.module_type_entry -> inline -> ModPath.t
val add_include :
  Entries.module_struct_entry -> bool -> inline ->
    Mod_subst.delta_resolver

(** Sections *)

val open_section : unit -> unit
(** [poly] is true when the section should be universe polymorphic *)

val close_section : Summary.Interp.frozen -> unit
(** Close the section and reset the global state to the one at the time when
    the section what opened. *)

val sections_are_opened : unit -> bool

(** Interactive modules and module types *)

val start_module : Id.t -> ModPath.t
val start_modtype : Id.t -> ModPath.t

val end_module : Summary.Interp.frozen -> Id.t ->
  (Entries.module_struct_entry * inline) option ->
    ModPath.t * MBId.t list * Mod_subst.delta_resolver

val end_modtype : Summary.Interp.frozen -> Id.t -> ModPath.t * MBId.t list

val add_module_parameter :
  MBId.t -> Entries.module_struct_entry -> inline ->
    Mod_subst.delta_resolver

(** {6 Queries in the global environment } *)

val lookup_named     : variable -> Constr.named_declaration
val lookup_constant  : Constant.t -> constant_body
val lookup_inductive : inductive ->
  mutual_inductive_body * one_inductive_body
val lookup_pinductive : Constr.pinductive ->
  mutual_inductive_body * one_inductive_body
val lookup_mind      : MutInd.t -> mutual_inductive_body
val lookup_module    : ModPath.t -> module_body
val lookup_modtype   : ModPath.t -> module_type_body
val exists_objlabel  : Label.t -> bool

val constant_of_delta_kn : KerName.t -> Constant.t
val mind_of_delta_kn : KerName.t -> MutInd.t

type indirect_accessor = {
  access_proof : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm option;
}

val force_proof : indirect_accessor -> Opaqueproof.opaque -> Opaqueproof.opaque_proofterm

val body_of_constant : indirect_accessor -> Constant.t ->
  (Constr.constr * unit Opaqueproof.delayed_universes * UVars.AbstractContext.t) option
(** Returns the body of the constant if it has any, and the polymorphic context
    it lives in. For monomorphic constant, the latter is empty, and for
    polymorphic constants, the term contains De Bruijn universe variables that
    need to be instantiated. *)

val body_of_constant_body : indirect_accessor ->
  constant_body ->
    (Constr.constr * unit Opaqueproof.delayed_universes * UVars.AbstractContext.t) option
(** Same as {!body_of_constant} but on {!constant_body}. *)

(** {6 Compiled libraries } *)

val start_library : DirPath.t -> ModPath.t
val export : output_native_objects:bool -> DirPath.t ->
  ModPath.t * Safe_typing.compiled_library * Vmlibrary.compiled_library * Nativelib.native_library
val import :
  Safe_typing.compiled_library -> Vmlibrary.on_disk -> Safe_typing.vodigest ->
  ModPath.t

(** {6 Misc } *)

(** Function to get an environment from the constants part of the global
 * environment and a given context. *)

val env_of_context : Environ.named_context_val -> Environ.env

val is_joined_environment : unit -> bool
val is_curmod_library : unit -> bool

val is_polymorphic : GlobRef.t -> bool
val is_template_polymorphic : GlobRef.t -> bool
val is_type_in_type : GlobRef.t -> bool

(** {6 Retroknowledge } *)

val register_inline : Constant.t -> unit
val register_inductive : inductive -> 'a CPrimitives.prim_ind -> unit

(** {6 Oracle } *)

val set_strategy : Conv_oracle.evaluable -> Conv_oracle.level -> unit

(** {6 Conversion settings } *)

val set_share_reduction : bool -> unit

val set_VM : bool -> unit
val set_native_compiler : bool -> unit

(* Modifies the global state, registering new universes *)

val current_modpath : unit -> ModPath.t

val current_dirpath : unit -> DirPath.t

val with_global : (Environ.env -> DirPath.t -> 'a Univ.in_universe_context_set) -> 'a

val global_env_summary_tag : Safe_typing.safe_environment Summary.Dyn.tag
