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

type locality = Discharge | Global of Declare.import_status

(** Declaration hooks *)
module Hook : sig
  type t

  (** Hooks allow users of the API to perform arbitrary actions at
     proof/definition saving time. For example, to register a constant
     as a Coercion, perform some cleanup, update the search database,
     etc...  *)
  module S : sig
    type t =
      { uctx : UState.t
      (** [ustate]: universe constraints obtained when the term was closed *)
      ; obls : (Id.t * Constr.t) list
      (** [(n1,t1),...(nm,tm)]: association list between obligation
          name and the corresponding defined term (might be a constant,
          but also an arbitrary term in the Expand case of obligations) *)
      ; scope : locality
      (** [scope]: Locality of the original declaration *)
      ; dref : GlobRef.t
      (** [dref]: identifier of the original declaration *)
      }
  end

  val make : (S.t -> unit) -> t
  val call : ?hook:t -> S.t -> unit
end

val declare_definition
  :  name:Id.t
  -> scope:locality
  -> kind:Decls.logical_kind
  -> ?hook_data:(Hook.t * UState.t * (Id.t * Constr.t) list)
  -> ubind:UnivNames.universe_binders
  -> impargs:Impargs.manual_implicits
  -> Evd.side_effects Declare.proof_entry
  -> GlobRef.t

val declare_assumption
  :  ?fix_exn:(Exninfo.iexn -> Exninfo.iexn)
  -> name:Id.t
  -> scope:locality
  -> hook:Hook.t option
  -> impargs:Impargs.manual_implicits
  -> uctx:UState.t
  -> Entries.parameter_entry
  -> GlobRef.t

module Recthm : sig
  type t =
    { name : Id.t
    (** Name of theorem *)
    ; typ : Constr.t
    (** Type of theorem  *)
    ; args : Name.t list
    (** Names to pre-introduce  *)
    ; impargs : Impargs.manual_implicits
    (** Explicitily declared implicit arguments  *)
    }
end

val declare_mutually_recursive
  : opaque:bool
  -> scope:locality
  -> kind:Decls.logical_kind
  -> poly:bool
  -> uctx:UState.t
  -> udecl:UState.universe_decl
  -> ntns:Vernacexpr.decl_notation list
  -> rec_declaration:Constr.rec_declaration
  -> possible_indexes:int list list option
  -> ?restrict_ucontext:bool
  (** XXX: restrict_ucontext should be always true, this seems like a
     bug in obligations, so this parameter should go away *)
  -> Recthm.t list
  -> Names.GlobRef.t list

val prepare_definition
  :  ?opaque:bool
  -> ?inline:bool
  -> poly:bool
  -> udecl:UState.universe_decl
  -> types:EConstr.t option
  -> body:EConstr.t
  -> Evd.evar_map
  -> Evd.evar_map * Evd.side_effects Declare.proof_entry

val prepare_obligation
  :  ?opaque:bool
  -> ?inline:bool
  -> name:Id.t
  -> poly:bool
  -> udecl:UState.universe_decl
  -> types:EConstr.t option
  -> body:EConstr.t
  -> Evd.evar_map
  -> Constr.constr * Constr.types * UState.t * RetrieveObl.obligation_info

val prepare_parameter
  : poly:bool
  -> udecl:UState.universe_decl
  -> types:EConstr.types
  -> Evd.evar_map
  -> Evd.evar_map * Entries.parameter_entry
