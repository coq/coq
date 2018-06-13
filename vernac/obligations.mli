(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

(* This is a hack to make it possible for Obligations to craft a Qed
 * behind the scenes.  The fix_exn the Stm attaches to the Future proof
 * is not available here, so we provide a side channel to get it *)
val stm_get_fix_exn : (unit -> Exninfo.iexn -> Exninfo.iexn) Hook.t

val check_evars : env -> evar_map -> unit

val evar_dependencies : evar_map -> Evar.t -> Evar.Set.t
val sort_dependencies : (Evar.t * evar_info * Evar.Set.t) list -> (Evar.t * evar_info * Evar.Set.t) list

(* env, id, evars, number of function prototypes to try to clear from
   evars contexts, object and type *)
val eterm_obligations : env -> Id.t -> evar_map -> int ->
  ?status:Evar_kinds.obligation_definition_status -> constr -> types ->
  (Id.t * types * Evar_kinds.t Loc.located *
     (bool * Evar_kinds.obligation_definition_status) * Int.Set.t *
      unit Proofview.tactic option) array
    (* Existential key, obl. name, type as product, 
       location of the original evar, associated tactic,
       status and dependencies as indexes into the array *)
  * ((Evar.t * Id.t) list * ((Id.t -> constr) -> constr -> constr)) *
    constr * types
    (* Translations from existential identifiers to obligation identifiers 
       and for terms with existentials to closed terms, given a 
       translation from obligation identifiers to constrs, new term, new type *)

type obligation_info =
  (Id.t * types * Evar_kinds.t Loc.located *
      (bool * Evar_kinds.obligation_definition_status) * Int.Set.t * unit Proofview.tactic option) array
    (* ident, type, location, (opaque or transparent, expand or define),
       dependencies, tactic to solve it *)

type progress = (* Resolution status of a program *)
  | Remain of int  (* n obligations remaining *)
  | Dependent (* Dependent on other definitions *)
  | Defined of GlobRef.t (* Defined as id *)

val default_tactic : unit Proofview.tactic ref

val add_definition : Names.Id.t -> ?term:constr -> types -> 
  UState.t ->
  ?univdecl:UState.universe_decl -> (* Universe binders and constraints *)
  ?implicits:(Constrexpr.explicitation * (bool * bool * bool)) list ->
  ?kind:Decl_kinds.definition_kind ->
  ?tactic:unit Proofview.tactic ->
  ?reduce:(constr -> constr) ->
  ?hook:(UState.t -> unit) Lemmas.declaration_hook -> ?opaque:bool -> obligation_info -> progress

type notations =
    (lstring * Constrexpr.constr_expr * Notation_term.scope_name option) list

type fixpoint_kind =
  | IsFixpoint of (lident option * Constrexpr.recursion_order_expr) list
  | IsCoFixpoint

val add_mutual_definitions :
  (Names.Id.t * constr * types *
      (Constrexpr.explicitation * (bool * bool * bool)) list * obligation_info) list ->
  UState.t ->
  ?univdecl:UState.universe_decl -> (* Universe binders and constraints *)
  ?tactic:unit Proofview.tactic ->
  ?kind:Decl_kinds.definition_kind ->
  ?reduce:(constr -> constr) ->
  ?hook:(UState.t -> unit) Lemmas.declaration_hook -> ?opaque:bool ->
  notations ->
  fixpoint_kind -> unit

val obligation : int * Names.Id.t option * Constrexpr.constr_expr option ->
  Genarg.glob_generic_argument option -> unit

val next_obligation : Names.Id.t option -> Genarg.glob_generic_argument option -> unit

val solve_obligations : Names.Id.t option -> unit Proofview.tactic option -> progress
(* Number of remaining obligations to be solved for this program *)

val solve_all_obligations : unit Proofview.tactic option -> unit

val try_solve_obligation : int -> Names.Id.t option -> unit Proofview.tactic option -> unit

val try_solve_obligations : Names.Id.t option -> unit Proofview.tactic option -> unit

val show_obligations : ?msg:bool -> Names.Id.t option -> unit

val show_term : Names.Id.t option -> Pp.t

val admit_obligations : Names.Id.t option -> unit

exception NoObligations of Names.Id.t option

val explain_no_obligations : Names.Id.t option -> Pp.t

val set_program_mode : bool -> unit

type program_info
val program_tcc_summary_tag : program_info Id.Map.t Summary.Dyn.tag
