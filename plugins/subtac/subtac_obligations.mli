open Names
open Util
open Libnames
open Evd
open Proof_type
open Vernacexpr

type obligation_info =
  (identifier * Term.types * hole_kind located *
      obligation_definition_status * Intset.t * tactic option) array
    (* ident, type, source, (opaque or transparent, expand or define),
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
  ?hook:(Tacexpr.declaration_hook) -> obligation_info -> progress

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
  ?hook:Tacexpr.declaration_hook ->
  notations ->
  fixpoint_kind -> unit

val subtac_obligation : int * Names.identifier option * Topconstr.constr_expr option ->
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

