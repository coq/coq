(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ
open Constr
open Evd
open Names

val check_evars : env -> evar_map -> unit

val evar_dependencies : evar_map -> Evar.t -> Evar.Set.t
val sort_dependencies : (Evar.t * evar_info * Evar.Set.t) list -> (Evar.t * evar_info * Evar.Set.t) list

(* env, id, evars, number of function prototypes to try to clear from
   evars contexts, object and type *)
val eterm_obligations : env -> Id.t -> evar_map -> int ->
  ?status:Evar_kinds.obligation_definition_status -> EConstr.constr -> EConstr.types ->
  (Id.t * types * Evar_kinds.t Loc.located *
     (bool * Evar_kinds.obligation_definition_status) * Int.Set.t *
      unit Proofview.tactic option) array
    (* Existential key, obl. name, type as product, 
       location of the original evar, associated tactic,
       status and dependencies as indexes into the array *)
  * ((Evar.t * Id.t) list * ((Id.t -> EConstr.constr) -> EConstr.constr -> constr)) *
    constr * types
    (* Translations from existential identifiers to obligation identifiers 
       and for terms with existentials to closed terms, given a 
       translation from obligation identifiers to constrs, new term, new type *)

type obligation_info =
  (Id.t * types * Evar_kinds.t Loc.located *
      (bool * Evar_kinds.obligation_definition_status) * Int.Set.t * unit Proofview.tactic option) array
    (* ident, type, location, (opaque or transparent, expand or define),
       dependencies, tactic to solve it *)

val default_tactic : unit Proofview.tactic ref

val add_definition
  :  name:Names.Id.t
  -> ?term:constr -> types
  -> UState.t
  -> ?univdecl:UState.universe_decl (* Universe binders and constraints *)
  -> ?implicits:Impargs.manual_implicits
  -> poly:bool
  -> ?scope:DeclareDef.locality
  -> ?kind:Decl_kinds.definition_object_kind
  -> ?tactic:unit Proofview.tactic
  -> ?reduce:(constr -> constr)
  -> ?hook:DeclareDef.Hook.t
  -> ?opaque:bool
  -> obligation_info
  -> DeclareObl.progress

val add_mutual_definitions
  : (Names.Id.t * constr * types * Impargs.manual_implicits * obligation_info) list
  -> UState.t
  -> ?univdecl:UState.universe_decl
  (** Universe binders and constraints *)
  -> ?tactic:unit Proofview.tactic
  -> poly:bool
  -> ?scope:DeclareDef.locality
  -> ?kind:Decl_kinds.definition_object_kind
  -> ?reduce:(constr -> constr)
  -> ?hook:DeclareDef.Hook.t -> ?opaque:bool
  -> DeclareObl.notations
  -> DeclareObl.fixpoint_kind -> unit

val obligation
  :  int * Names.Id.t option * Constrexpr.constr_expr option
  -> Genarg.glob_generic_argument option
  -> Lemmas.t

val next_obligation
  :  Names.Id.t option
  -> Genarg.glob_generic_argument option
  -> Lemmas.t

val solve_obligations : Names.Id.t option -> unit Proofview.tactic option
  -> DeclareObl.progress
(* Number of remaining obligations to be solved for this program *)

val solve_all_obligations : unit Proofview.tactic option -> unit

val try_solve_obligation : int -> Names.Id.t option -> unit Proofview.tactic option -> unit

val try_solve_obligations : Names.Id.t option -> unit Proofview.tactic option -> unit

val show_obligations : ?msg:bool -> Names.Id.t option -> unit

val show_term : Names.Id.t option -> Pp.t

val admit_obligations : Names.Id.t option -> unit

exception NoObligations of Names.Id.t option

val explain_no_obligations : Names.Id.t option -> Pp.t

val check_program_libraries : unit -> unit
