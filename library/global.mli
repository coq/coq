(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
val named_context_val : unit -> Environ.named_context_val
val named_context : unit -> Context.Named.t

(** {6 Enriching the global environment } *)

(** Changing the (im)predicativity of the system *)
val set_engagement : Declarations.engagement -> unit
val set_typing_flags : Declarations.typing_flags -> unit

(** Variables, Local definitions, constants, inductive types *)

val push_named_assum : (Id.t * Constr.types * bool) Univ.in_universe_context_set -> unit
val push_named_def   : (Id.t * Safe_typing.private_constants Entries.definition_entry) -> Univ.universe_context_set

val export_private_constants : in_section:bool ->
  Safe_typing.private_constants Entries.constant_entry ->
  unit Entries.constant_entry * Safe_typing.exported_private_constant list

val add_constant :
  DirPath.t -> Id.t -> Safe_typing.global_declaration -> constant
val add_mind :
  DirPath.t -> Id.t -> Entries.mutual_inductive_entry -> mutual_inductive

(** Extra universe constraints *)
val add_constraints : Univ.constraints -> unit

val push_context : bool -> Univ.universe_context -> unit
val push_context_set : bool -> Univ.universe_context_set -> unit

(** Non-interactive modules and module types *)

val add_module :
  Id.t -> Entries.module_entry -> Declarations.inline ->
    module_path * Mod_subst.delta_resolver
val add_modtype :
  Id.t -> Entries.module_type_entry -> Declarations.inline -> module_path
val add_include :
  Entries.module_struct_entry -> bool -> Declarations.inline ->
    Mod_subst.delta_resolver

(** Interactive modules and module types *)

val start_module : Id.t -> module_path
val start_modtype : Id.t -> module_path

val end_module : Summary.frozen -> Id.t ->
  (Entries.module_struct_entry * Declarations.inline) option ->
    module_path * MBId.t list * Mod_subst.delta_resolver

val end_modtype : Summary.frozen -> Id.t -> module_path * MBId.t list

val add_module_parameter :
  MBId.t -> Entries.module_struct_entry -> Declarations.inline ->
    Mod_subst.delta_resolver

(** {6 Queries in the global environment } *)

val lookup_named     : variable -> Context.Named.Declaration.t
val lookup_constant  : constant -> Declarations.constant_body
val lookup_inductive : inductive ->
  Declarations.mutual_inductive_body * Declarations.one_inductive_body
val lookup_pinductive : Constr.pinductive -> 
  Declarations.mutual_inductive_body * Declarations.one_inductive_body
val lookup_mind      : mutual_inductive -> Declarations.mutual_inductive_body
val lookup_module    : module_path -> Declarations.module_body
val lookup_modtype   : module_path -> Declarations.module_type_body
val exists_objlabel  : Label.t -> bool

val constant_of_delta_kn : kernel_name -> constant
val mind_of_delta_kn : kernel_name -> mutual_inductive

val opaque_tables : unit -> Opaqueproof.opaquetab

val body_of_constant : constant -> (Term.constr * Univ.AUContext.t) option
(** Returns the body of the constant if it has any, and the polymorphic context
    it lives in. For monomorphic constant, the latter is empty, and for
    polymorphic constants, the term contains De Bruijn universe variables that
    need to be instantiated. *)

val body_of_constant_body : Declarations.constant_body -> (Term.constr * Univ.AUContext.t) option
(** Same as {!body_of_constant} but on {!Declarations.constant_body}. *)

(** Global universe name <-> level mapping *)
type universe_names = 
  (Decl_kinds.polymorphic * Univ.universe_level) Id.Map.t * Id.t Univ.LMap.t

val global_universe_names : unit -> universe_names
val set_global_universe_names : universe_names -> unit

(** {6 Compiled libraries } *)

val start_library : DirPath.t -> module_path
val export : ?except:Future.UUIDSet.t -> DirPath.t ->
  module_path * Safe_typing.compiled_library * Safe_typing.native_library
val import :
  Safe_typing.compiled_library -> Univ.universe_context_set -> Safe_typing.vodigest ->
  module_path

(** {6 Misc } *)

(** Function to get an environment from the constants part of the global
 * environment and a given context. *)

val env_of_context : Environ.named_context_val -> Environ.env

val join_safe_environment : ?except:Future.UUIDSet.t -> unit -> unit
val is_joined_environment : unit -> bool

val is_polymorphic : Globnames.global_reference -> bool
val is_template_polymorphic : Globnames.global_reference -> bool
val is_type_in_type : Globnames.global_reference -> bool

val constr_of_global_in_context : Environ.env ->
  Globnames.global_reference -> Constr.types * Univ.AUContext.t
(** Returns the type of the constant in its local universe
    context. The type should not be used without pushing it's universe
    context in the environmnent of usage. For non-universe-polymorphic
    constants, it does not matter. *)

val type_of_global_in_context : Environ.env -> 
  Globnames.global_reference -> Constr.types * Univ.AUContext.t
(** Returns the type of the constant in its local universe
    context. The type should not be used without pushing it's universe
    context in the environmnent of usage. For non-universe-polymorphic
    constants, it does not matter. *)

(** Returns the universe context of the global reference (whatever its polymorphic status is). *)
val universes_of_global : Globnames.global_reference -> Univ.abstract_universe_context

(** {6 Retroknowledge } *)

val register :
  Retroknowledge.field -> Term.constr -> Term.constr -> unit

val register_inline : constant -> unit

(** {6 Oracle } *)

val set_strategy : Names.constant Names.tableKey -> Conv_oracle.level -> unit

(* Modifies the global state, registering new universes *)

val current_dirpath : unit -> Names.dir_path

val with_global : (Environ.env -> Names.dir_path -> 'a Univ.in_universe_context_set) -> 'a

val global_env_summary_name : string
