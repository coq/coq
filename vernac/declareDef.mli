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
open Decl_kinds

(** Declaration hooks *)
type declaration_hook

(* Hooks allow users of the API to perform arbitrary actions at
 * proof/definition saving time. For example, to register a constant
 * as a Coercion, perform some cleanup, update the search database,
 * etc...
 *
 * Here, we use an extended hook type suitable for obligations /
 * equations.
 *)
(** [hook_type] passes to the client:
    - [ustate]: universe constraints obtained when the term was closed
    - [(n1,t1),...(nm,tm)]: association list between obligation
        name and the corresponding defined term (might be a constant,
        but also an arbitrary term in the Expand case of obligations)
    - [locality]: Locality of the original declaration
    - [ref]: identifier of the origianl declaration
 *)
type hook_type = UState.t -> (Id.t * Constr.t) list -> Decl_kinds.locality -> GlobRef.t -> unit

val mk_hook : hook_type -> declaration_hook
val call_hook
  :  ?hook:declaration_hook
  -> ?fix_exn:Future.fix_exn
  -> hook_type

(* Locality  *)
val get_locality : Id.t -> kind:string -> Decl_kinds.locality -> bool

val declare_definition
  :  ontop:bool
  -> Id.t
  -> definition_kind
  -> ?hook_data:(declaration_hook * UState.t * (Id.t * Constr.t) list)
  -> Safe_typing.private_constants Entries.definition_entry
  -> UnivNames.universe_binders
  -> Impargs.manual_implicits
  -> GlobRef.t

val declare_fix
  :  ontop:bool
  -> ?opaque:bool
  -> ?hook_data:(declaration_hook * UState.t * (Id.t * Constr.t) list)
  -> definition_kind
  -> UnivNames.universe_binders
  -> Entries.universes_entry
  -> Id.t
  -> Safe_typing.private_constants Entries.proof_output
  -> Constr.types
  -> Impargs.manual_implicits
  -> GlobRef.t

val prepare_definition : allow_evars:bool ->
  ?opaque:bool -> ?inline:bool -> poly:bool ->
  Evd.evar_map -> UState.universe_decl ->
  types:EConstr.t option -> body:EConstr.t ->
  Evd.evar_map * Safe_typing.private_constants Entries.definition_entry

val prepare_parameter : allow_evars:bool ->
  poly:bool -> Evd.evar_map -> UState.universe_decl -> EConstr.types ->
  Evd.evar_map * Entries.parameter_entry
