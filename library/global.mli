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

(** This module defines the global environment of Coq. The functions
   below are exactly the same as the ones in [Safe_typing], operating on
   that global environment. [add_*] functions perform name verification,
   i.e. check that the name given as argument match those provided by
   [Safe_typing]. *)

val safe_env : unit -> Safe_typing.safe_environment
val env : unit -> Environ.env

val env_is_initial : unit -> bool

val universes : unit -> UGraph.t
val universes_lbound : unit -> UGraph.Bound.t
val named_context_val : unit -> Environ.named_context_val
val named_context : unit -> Constr.named_context

(** {6 Enriching the global environment } *)

(** Changing the (im)predicativity of the system *)
val set_engagement : Declarations.engagement -> unit
val set_indices_matter : bool -> unit
val set_typing_flags : Declarations.typing_flags -> unit
val set_check_guarded : bool -> unit
val set_check_sized : bool -> unit
val set_check_positive : bool -> unit
val set_check_universes : bool -> unit
val typing_flags : unit -> Declarations.typing_flags
val set_cumulative_sprop : bool -> unit
val is_cumulative_sprop : unit -> bool
val set_allow_sprop : bool -> unit
val sprop_allowed : unit -> bool

(** Variables, Local definitions, constants, inductive types *)

val push_named_assum : (Id.t * Constr.types) -> unit
val push_named_def   : (Id.t * Entries.section_def_entry) -> unit
val push_section_context : (Name.t array * Univ.UContext.t) -> unit

val export_private_constants :
  Safe_typing.private_constants ->
  Safe_typing.exported_private_constant list

val add_constant :
  Id.t -> Safe_typing.global_declaration -> Constant.t
val add_private_constant :
  Id.t -> Safe_typing.side_effect_declaration -> Constant.t * Safe_typing.private_constants
val add_mind :
  Id.t -> Entries.mutual_inductive_entry -> MutInd.t

(** Extra universe constraints *)
val add_constraints : Univ.Constraint.t -> unit

val push_context_set : strict:bool -> Univ.ContextSet.t -> unit

(** Non-interactive modules and module types *)

val add_module :
  Id.t -> Entries.module_entry -> Declarations.inline ->
    ModPath.t * Mod_subst.delta_resolver
val add_modtype :
  Id.t -> Entries.module_type_entry -> Declarations.inline -> ModPath.t
val add_include :
  Entries.module_struct_entry -> bool -> Declarations.inline ->
    Mod_subst.delta_resolver

(** Sections *)

val open_section : unit -> unit
(** [poly] is true when the section should be universe polymorphic *)

val close_section : Summary.frozen -> unit
(** Close the section and reset the global state to the one at the time when
    the section what opened. *)

val sections_are_opened : unit -> bool

(** Interactive modules and module types *)

val start_module : Id.t -> ModPath.t
val start_modtype : Id.t -> ModPath.t

val end_module : Summary.frozen -> Id.t ->
  (Entries.module_struct_entry * Declarations.inline) option ->
    ModPath.t * MBId.t list * Mod_subst.delta_resolver

val end_modtype : Summary.frozen -> Id.t -> ModPath.t * MBId.t list

val add_module_parameter :
  MBId.t -> Entries.module_struct_entry -> Declarations.inline ->
    Mod_subst.delta_resolver

(** {6 Queries in the global environment } *)

val lookup_named     : variable -> Constr.named_declaration
val lookup_constant  : Constant.t -> Opaqueproof.opaque Declarations.constant_body
val lookup_inductive : inductive ->
  Declarations.mutual_inductive_body * Declarations.one_inductive_body
val lookup_pinductive : Constr.pinductive ->
  Declarations.mutual_inductive_body * Declarations.one_inductive_body
val lookup_mind      : MutInd.t -> Declarations.mutual_inductive_body
val lookup_module    : ModPath.t -> Declarations.module_body
val lookup_modtype   : ModPath.t -> Declarations.module_type_body
val exists_objlabel  : Label.t -> bool

val constant_of_delta_kn : KerName.t -> Constant.t
val mind_of_delta_kn : KerName.t -> MutInd.t

val opaque_tables : unit -> Opaqueproof.opaquetab

val body_of_constant : Opaqueproof.indirect_accessor -> Constant.t ->
  (Constr.constr * unit Opaqueproof.delayed_universes * Univ.AUContext.t) option
(** Returns the body of the constant if it has any, and the polymorphic context
    it lives in. For monomorphic constant, the latter is empty, and for
    polymorphic constants, the term contains De Bruijn universe variables that
    need to be instantiated. *)

val body_of_constant_body : Opaqueproof.indirect_accessor ->
  Opaqueproof.opaque Declarations.constant_body ->
    (Constr.constr * unit Opaqueproof.delayed_universes * Univ.AUContext.t) option
(** Same as {!body_of_constant} but on {!Declarations.constant_body}. *)

(** {6 Compiled libraries } *)

val start_library : DirPath.t -> ModPath.t
val export : ?except:Future.UUIDSet.t -> output_native_objects:bool -> DirPath.t ->
  ModPath.t * Safe_typing.compiled_library * Safe_typing.native_library
val import :
  Safe_typing.compiled_library -> Univ.ContextSet.t -> Safe_typing.vodigest ->
  ModPath.t

(** {6 Misc } *)

(** Function to get an environment from the constants part of the global
 * environment and a given context. *)

val env_of_context : Environ.named_context_val -> Environ.env

val join_safe_environment : ?except:Future.UUIDSet.t -> unit -> unit
val is_joined_environment : unit -> bool

val is_polymorphic : GlobRef.t -> bool
val is_template_polymorphic : GlobRef.t -> bool
val get_template_polymorphic_variables : GlobRef.t -> Univ.Level.t list
val is_type_in_type : GlobRef.t -> bool

(** {6 Retroknowledge } *)

val register_inline : Constant.t -> unit
val register_inductive : inductive -> 'a CPrimitives.prim_ind -> unit

(** {6 Oracle } *)

val set_strategy : Constant.t Names.tableKey -> Conv_oracle.level -> unit

(** {6 Conversion settings } *)

val set_share_reduction : bool -> unit

val set_VM : bool -> unit
val set_native_compiler : bool -> unit

(* Modifies the global state, registering new universes *)

val current_modpath : unit -> ModPath.t

val current_dirpath : unit -> DirPath.t

val with_global : (Environ.env -> DirPath.t -> 'a Univ.in_universe_context_set) -> 'a

val global_env_summary_tag : Safe_typing.safe_environment Summary.Dyn.tag
