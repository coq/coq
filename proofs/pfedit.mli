
(* $Id$ *)

(*i*)
open Pp
open Sign
open Declare
open Proof_trees
open Tacmach
(*i*)

val proof_prompt : unit -> string
val refining : unit -> bool
val msg_proofs : bool -> std_ppcmds

val undo_limit : int ref
val set_undo : int -> unit
val unset_undo : unit -> unit

type proof_topstate = {
  top_hyps : context * context;
  top_goal : goal;
  top_strength : strength }

val get_state : unit -> pftreestate * proof_topstate
val get_topstate : unit -> proof_topstate
val get_pftreestate : unit -> pftreestate
val get_evmap_sign : int option -> evar_declarations * context
val set_proof : string option -> unit
val get_proof : unit -> string
val list_proofs : unit -> string list
val add_proof : string * pftreestate * proof_topstate -> unit
val del_proof : string -> unit
val init_proofs : unit -> unit

val make_focus : int -> unit
val focus : unit -> int
val focused_goal : unit -> int

