(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr

val default_tactic : unit Proofview.tactic ref

val add_definition
  :  name:Names.Id.t
  -> ?term:constr -> types
  -> uctx:UState.t
  -> ?udecl:UState.universe_decl (* Universe binders and constraints *)
  -> ?impargs:Impargs.manual_implicits
  -> poly:bool
  -> ?scope:DeclareDef.locality
  -> ?kind:Decls.definition_object_kind
  -> ?tactic:unit Proofview.tactic
  -> ?reduce:(constr -> constr)
  -> ?hook:DeclareDef.Hook.t
  -> ?opaque:bool
  -> RetrieveObl.obligation_info
  -> DeclareObl.progress

val add_mutual_definitions
  (* XXX: unify with MutualEntry *)
  : (Names.Id.t * constr * types * Impargs.manual_implicits * RetrieveObl.obligation_info) list
  -> uctx:UState.t
  -> ?udecl:UState.universe_decl
  (** Universe binders and constraints *)
  -> ?tactic:unit Proofview.tactic
  -> poly:bool
  -> ?scope:DeclareDef.locality
  -> ?kind:Decls.definition_object_kind
  -> ?reduce:(constr -> constr)
  -> ?hook:DeclareDef.Hook.t -> ?opaque:bool
  -> Vernacexpr.decl_notation list
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
