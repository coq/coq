(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Environ
open Tacmach
open Term
open Evd
open Names
open Pp
open Util
open Tacinterp
open Libnames
open Proof_type
open Vernacexpr
open Decl_kinds
open Tacexpr

(** Forward declaration. *)
val declare_fix_ref : (definition_object_kind -> identifier ->
  constr -> types -> Impargs.manual_implicits -> global_reference) ref

val declare_definition_ref :
  (identifier -> locality * definition_object_kind ->
     Entries.definition_entry -> Impargs.manual_implicits
       -> global_reference declaration_hook -> global_reference) ref

val check_evars : env -> evar_map -> unit

val mkMetas : int -> constr list

val evar_dependencies : evar_map -> int -> Intset.t
val sort_dependencies : (int * evar_info * Intset.t) list -> (int * evar_info * Intset.t) list

(* env, id, evars, number of function prototypes to try to clear from
   evars contexts, object and type *)
val eterm_obligations : env -> identifier -> evar_map -> int ->
  ?status:obligation_definition_status -> constr -> types -> 
  (identifier * types * hole_kind located * obligation_definition_status * Intset.t * 
      tactic option) array
    (* Existential key, obl. name, type as product, 
       location of the original evar, associated tactic,
       status and dependencies as indexes into the array *)
  * ((existential_key * identifier) list * ((identifier -> constr) -> constr -> constr)) *
    constr * types
    (* Translations from existential identifiers to obligation identifiers 
       and for terms with existentials to closed terms, given a 
       translation from obligation identifiers to constrs, new term, new type *)

type obligation_info =
  (identifier * Term.types * hole_kind located *
      obligation_definition_status * Intset.t * tactic option) array
    (* ident, type, location, (opaque or transparent, expand or define),
       dependencies, tactic to solve it *)

type progress = (* Resolution status of a program *)
  | Remain of int  (* n obligations remaining *)
  | Dependent (* Dependent on other definitions *)
  | Defined of global_reference (* Defined as id *)
      
val set_default_tactic : bool -> Tacexpr.glob_tactic_expr -> unit
val get_default_tactic : unit -> locality_flag * Proof_type.tactic
val print_default_tactic : unit -> Pp.std_ppcmds

val set_proofs_transparency : bool -> unit (* true = All transparent, false = Opaque if possible *)
val get_proofs_transparency : unit -> bool

val add_definition : Names.identifier -> ?term:Term.constr -> Term.types -> 
  ?implicits:(Topconstr.explicitation * (bool * bool * bool)) list ->
  ?kind:Decl_kinds.definition_kind ->
  ?tactic:Proof_type.tactic ->
  ?reduce:(Term.constr -> Term.constr) ->
  ?hook:(unit Tacexpr.declaration_hook) -> obligation_info -> progress

type notations = (Vernacexpr.lstring * Topconstr.constr_expr * Topconstr.scope_name option) list

type fixpoint_kind =
  | IsFixpoint of (identifier located option * Topconstr.recursion_order_expr) list
  | IsCoFixpoint

val add_mutual_definitions :
  (Names.identifier * Term.constr * Term.types *
      (Topconstr.explicitation * (bool * bool * bool)) list * obligation_info) list ->
  ?tactic:Proof_type.tactic ->
  ?kind:Decl_kinds.definition_kind ->
  ?reduce:(Term.constr -> Term.constr) ->
  ?hook:unit Tacexpr.declaration_hook ->
  notations ->
  fixpoint_kind -> unit

val obligation : int * Names.identifier option * Topconstr.constr_expr option ->
  Tacexpr.raw_tactic_expr option -> unit

val next_obligation : Names.identifier option -> Tacexpr.raw_tactic_expr option -> unit

val solve_obligations : Names.identifier option -> Proof_type.tactic option -> progress
(* Number of remaining obligations to be solved for this program *)

val solve_all_obligations : Proof_type.tactic option -> unit

val try_solve_obligation : int -> Names.identifier option -> Proof_type.tactic option -> unit

val try_solve_obligations : Names.identifier option -> Proof_type.tactic option -> unit

val show_obligations : ?msg:bool -> Names.identifier option -> unit

val show_term : Names.identifier option -> unit

val admit_obligations : Names.identifier option -> unit

exception NoObligations of Names.identifier option

val explain_no_obligations : Names.identifier option -> Pp.std_ppcmds

val set_program_mode : bool -> unit
