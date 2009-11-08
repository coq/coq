(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Pp
open Names
open Term
open Sign
open Environ
open Decl_kinds
open Tacmach
open Tacexpr
(*i*)

(*s Several proofs can be opened simultaneously but at most one is
   focused at some time. The following functions work by side-effect
   on current set of open proofs. In this module, ``proofs'' means an
   open proof (something started by vernacular command [Goal], [Lemma]
   or [Theorem]), and ``goal'' means a subgoal of the current focused
   proof *)

(*s [refining ()] tells if there is some proof in progress, even if a not
   focused one *)

val refining : unit -> bool

(* [check_no_pending_proofs ()] fails if there is still some proof in
   progress *)

val check_no_pending_proofs : unit -> unit

(*s [delete_proof name] deletes proof of name [name] or fails if no proof
    has this name *)

val delete_proof : identifier located -> unit

(* [delete_current_proof ()] deletes current focused proof or fails if
    no proof is focused *)

val delete_current_proof : unit -> unit

(* [delete_all_proofs ()] deletes all open proofs if any *)

val delete_all_proofs : unit -> unit

(*s [undo n] undoes the effect of the last [n] tactics applied to the
    current proof; it fails if no proof is focused or if the ``undo''
    stack is exhausted *)

val undo : int -> unit

(* Same as undo, but undoes the current proof stack to reach depth
   [n]. This is used in [vernac_backtrack]. *)
val undo_todepth : int -> unit

(* Returns the depth of the current focused proof stack, this is used
   to put informations in coq prompt (in emacs mode). *)
val current_proof_depth: unit -> int

(* [set_undo (Some n)] sets the size of the ``undo'' stack; [set_undo None]
   sets the size to the default value (12) *)

val set_undo : int option -> unit
val get_undo : unit -> int option

(*s [start_proof s str env t hook tac] starts a proof of name [s] and
    conclusion [t]; [hook] is optionally a function to be applied at
    proof end (e.g. to declare the built constructions as a coercion
    or a setoid morphism); init_tac is possibly a tactic to
    systematically apply at initialization time (e.g. to start the
    proof of mutually dependent theorems) *)

val start_proof :
  identifier -> goal_kind -> named_context_val -> constr ->
    ?init_tac:tactic -> ?compute_guard:bool -> declaration_hook -> unit

(* [restart_proof ()] restarts the current focused proof from the beginning
   or fails if no proof is focused *)

val restart_proof : unit -> unit

(*s [resume_last_proof ()] focus on the last unfocused proof or fails
   if there is no suspended proofs *)

val resume_last_proof : unit -> unit

(* [resume_proof name] focuses on the proof of name [name] or
   raises [UserError] if no proof has name [name] *)

val resume_proof : identifier located -> unit

(* [suspend_proof ()] unfocuses the current focused proof or
   failed with [UserError] if no proof is currently focused *)

val suspend_proof : unit -> unit

(*s [cook_proof opacity] turns the current proof (assumed completed) into
    a constant with its name, kind and possible hook (see [start_proof]);
    it fails if there is no current proof of if it is not completed;
    it also tells if the guardness condition has to be inferred. *)

val cook_proof : (Refiner.pftreestate -> unit) ->
  identifier * (Entries.definition_entry * bool * goal_kind * declaration_hook)

(* To export completed proofs to xml *)
val set_xml_cook_proof : (goal_kind * pftreestate -> unit) -> unit

(*s [get_pftreestate ()] returns the current focused pending proof or
   raises [UserError "no focused proof"] *)

val get_pftreestate : unit -> pftreestate

(* [get_end_tac ()] returns the current tactic to apply to all new subgoal *)

val get_end_tac : unit -> tactic option

(* [get_goal_context n] returns the context of the [n]th subgoal of
   the current focused proof or raises a [UserError] if there is no
   focused proof or if there is no more subgoals *)

val get_goal_context : int -> Evd.evar_map * env

(* [get_current_goal_context ()] works as [get_goal_context 1] *)

val get_current_goal_context : unit -> Evd.evar_map * env

(* [current_proof_statement] *)

val current_proof_statement :
  unit -> identifier * goal_kind * types * declaration_hook

(*s [get_current_proof_name ()] return the name of the current focused
    proof or failed if no proof is focused *)

val get_current_proof_name : unit -> identifier

(* [get_all_proof_names ()] returns the list of all pending proof names *)

val get_all_proof_names : unit -> identifier list

(*s [set_end_tac tac] applies tactic [tac] to all subgoal generate
    by [solve_nth] *)

val set_end_tac : tactic -> unit

(*s [solve_nth n tac] applies tactic [tac] to the [n]th subgoal of the
   current focused proof or raises a UserError if no proof is focused or
   if there is no [n]th subgoal *)

val solve_nth : int -> tactic -> unit

(* [by tac] applies tactic [tac] to the 1st subgoal of the current
   focused proof or raises a UserError if there is no focused proof or
   if there is no more subgoals *)

val by : tactic -> unit

(* [instantiate_nth_evar_com n c] instantiate the [n]th undefined
   existential variable of the current focused proof by [c] or raises a
   UserError if no proof is focused or if there is no such [n]th
   existential variable *)

val instantiate_nth_evar_com : int -> Topconstr.constr_expr -> unit

(*s To deal with subgoal focus *)

val make_focus : int -> unit
val focus : unit -> int
val focused_goal : unit -> int
val subtree_solved : unit -> bool
val tree_solved : unit -> bool
val top_tree_solved : unit -> bool

val reset_top_of_tree : unit -> unit
val reset_top_of_script : unit -> unit

val traverse : int -> unit
val traverse_nth_goal : int -> unit
val traverse_next_unproven : unit -> unit
val traverse_prev_unproven : unit -> unit


(* These two functions make it possible to implement more elaborate
   proof and goal management, as it is done, for instance in pcoq *)

val traverse_to : int list -> unit
val mutate : (pftreestate -> pftreestate) -> unit


(* [build_by_tactic typ tac] returns a term of type [typ] by calling [tac] *)

val build_by_tactic : types -> tactic -> constr
