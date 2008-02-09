(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Term
open Proof_type
open Tacexpr
open Auto
open Topconstr
open Evd
open Environ
open Explore
(*i*)

val rawwit_hintbases : hint_db_name list option raw_abstract_argument_type

val rawwit_auto_using : constr_expr list raw_abstract_argument_type

val e_assumption : tactic

val registered_e_assumption : tactic

val e_give_exact_constr : constr -> tactic

type search_state = { 
  depth : int; (*r depth of search before failing *)
  tacres : goal list sigma * validation;
  last_tactic : Pp.std_ppcmds;
  dblist : Auto.Hint_db.t list;
  localdb :  Auto.Hint_db.t list }

module SearchProblem : sig
  type state = search_state
      
  val filter_tactics :     Proof_type.goal list Tacmach.sigma * (Proof_type.proof_tree list -> 'a) ->
    (Tacmach.tactic * Pp.std_ppcmds) list ->
    ((Proof_type.goal list Tacmach.sigma * (Proof_type.proof_tree list -> 'a)) *
     Pp.std_ppcmds)
    list

  val compare :  search_state -> search_state -> int

  val branching : state -> state list
  val success : state -> bool
  val pp : state -> unit
end

module Search : sig
  val depth_first : search_state -> search_state
  val debug_depth_first : search_state -> search_state

  val breadth_first : search_state -> search_state
  val debug_breadth_first : search_state -> search_state
end

val full_eauto_gls : bool -> bool * int -> constr list -> goal list sigma * validation -> 
  goal list sigma * validation

val resolve_all_evars_once : bool -> bool * int -> env -> (evar -> evar_info -> bool) -> evar_defs ->
  evar_defs

val resolve_all_evars : bool -> bool * int -> env -> (evar -> evar_info -> bool) -> evar_defs ->
  evar_defs

val valid :     Evd.evar_map ->
    (Evd.evar -> Evd.evar_info -> bool) ->
    Evd.evar_map ref -> Proof_type.proof_tree list -> 'a


val gen_eauto : bool -> bool * int -> constr list -> 
  hint_db_name list option -> tactic
