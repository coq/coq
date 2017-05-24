(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Environ
open Term
open Evd
open Names
open Pp
open Globnames
open Decl_kinds

(** Forward declaration. *)
val declare_fix_ref : (?opaque:bool -> definition_kind -> Univ.universe_context -> Id.t ->
  Safe_typing.private_constants Entries.proof_output -> types -> Impargs.manual_implicits -> global_reference) ref

val declare_definition_ref :
  (Id.t -> definition_kind ->
     Safe_typing.private_constants Entries.definition_entry -> Impargs.manual_implicits
       -> global_reference Lemmas.declaration_hook -> global_reference) ref

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
  * ((existential_key * Id.t) list * ((Id.t -> constr) -> constr -> constr)) *
    constr * types
    (* Translations from existential identifiers to obligation identifiers 
       and for terms with existentials to closed terms, given a 
       translation from obligation identifiers to constrs, new term, new type *)

type obligation_info =
  (Id.t * Term.types * Evar_kinds.t Loc.located *
      (bool * Evar_kinds.obligation_definition_status) * Int.Set.t * unit Proofview.tactic option) array
    (* ident, type, location, (opaque or transparent, expand or define),
       dependencies, tactic to solve it *)

type progress = (* Resolution status of a program *)
  | Remain of int  (* n obligations remaining *)
  | Dependent (* Dependent on other definitions *)
  | Defined of global_reference (* Defined as id *)

val default_tactic : unit Proofview.tactic ref

val add_definition : Names.Id.t -> ?term:Term.constr -> Term.types -> 
  Evd.evar_universe_context ->
  ?pl:(Id.t Loc.located list) -> (* Universe binders *)
  ?implicits:(Constrexpr.explicitation * (bool * bool * bool)) list ->
  ?kind:Decl_kinds.definition_kind ->
  ?tactic:unit Proofview.tactic ->
  ?reduce:(Term.constr -> Term.constr) ->
  ?hook:(Evd.evar_universe_context -> unit) Lemmas.declaration_hook -> ?opaque:bool -> obligation_info -> progress

type notations =
    (Vernacexpr.lstring * Constrexpr.constr_expr * Notation_term.scope_name option) list

type fixpoint_kind =
  | IsFixpoint of (Id.t Loc.located option * Constrexpr.recursion_order_expr) list
  | IsCoFixpoint

val add_mutual_definitions :
  (Names.Id.t * Term.constr * Term.types *
      (Constrexpr.explicitation * (bool * bool * bool)) list * obligation_info) list ->
  Evd.evar_universe_context ->
  ?pl:(Id.t Loc.located list) -> (* Universe binders *)
  ?tactic:unit Proofview.tactic ->
  ?kind:Decl_kinds.definition_kind ->
  ?reduce:(Term.constr -> Term.constr) ->
  ?hook:(Evd.evar_universe_context -> unit) Lemmas.declaration_hook -> ?opaque:bool ->
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

val show_term : Names.Id.t option -> std_ppcmds

val admit_obligations : Names.Id.t option -> unit

exception NoObligations of Names.Id.t option

val explain_no_obligations : Names.Id.t option -> Pp.std_ppcmds

val set_program_mode : bool -> unit
