
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
open Environ
open Declare
open Proof_trees
open Tacmach
(*i*)

val proof_prompt : unit -> string
val refining : unit -> bool
val abort_goal : string -> unit
val abort_cur_goal : unit -> unit
val abort_goals : unit -> unit
val abort_refine : ('a -> 'b) -> 'a -> 'b
val msg_proofs : bool -> std_ppcmds

val undo_limit : int ref
val set_undo : int -> unit
val unset_undo : unit -> unit
val undo : int -> unit
val resume_last : unit -> unit

type proof_topstate = {
  top_hyps : env * env;
  top_goal : goal;
  top_strength : strength }

val get_state : unit -> pftreestate * proof_topstate
val get_topstate : unit -> proof_topstate
val get_pftreestate : unit -> pftreestate
val get_evmap_sign : int option -> evar_declarations * env
val set_proof : string option -> unit
val get_proof : unit -> string
val list_proofs : unit -> string list
val add_proof : string * pftreestate * proof_topstate -> unit
val del_proof : string -> unit
val init_proofs : unit -> unit

val mutate : (pftreestate -> pftreestate) -> unit
val rev_mutate : (pftreestate -> pftreestate) -> unit
val start : string * proof_topstate -> unit
val restart : unit -> unit
val proof_prompt : unit -> string
val proof_term : unit -> constr

val start_proof : string -> strength -> Coqast.t -> unit
val start_proof_constr : string -> strength -> constr -> unit
val reset_name : identifier -> unit

val save_named : bool -> unit
val save_anonymous : bool -> string -> 'a -> unit
val save_anonymous_thm : bool -> string -> unit
val save_anonymous_remark : bool -> string -> unit

val solve_nth : int -> tactic -> unit
val by : tactic -> unit
val traverse : int -> unit
val traverse_nth_goal : int -> unit
val traverse_to : int list -> unit

val make_focus : int -> unit
val focus : unit -> int
val focused_goal : unit -> int

val subtree_solved : unit -> bool
