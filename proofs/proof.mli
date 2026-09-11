(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Module defining the last essential tiles of interactive proofs.
   A proof deals with the focusing commands (including the braces and bullets),
   the shelf (see the [shelve] tactic) and given up goal (see the [give_up]
   tactic). A proof is made of the following:
   - Proofview: a proof is primarily the data of the current view.
     That which is shown to the user (as a remainder, a proofview
     is mainly the logical state of the proof, together with the
     currently focused goals).
   - Focus: a proof has a focus stack: the top of the stack contains
     the context in which to unfocus the current view to a view focused
     with the rest of the stack.
     In addition, this contains, for each of the focus context,  a
     "focus kind" and a "focus condition" (in practice, and for modularity,
     the focus kind is actually stored inside the condition). To unfocus, one
     needs to know the focus kind, and the condition (for instance "no condition" or
     the proof under focused must be complete) must be met.
   - Shelf: A list of goals which have been put aside during the proof. They can be
     retrieved with the [Unshelve] command, or solved by side effects
   - Given up goals: as long as there is a given up goal, the proof is not completed.
     Given up goals cannot be retrieved, the user must go back where the tactic
     [give_up] was run and solve the goal there.
*)

(* Type of a proof. *)
type t

type data = private
  { sigma : Evd.evar_map
  (** A representation of the evar_map [EJGA wouldn't it better to just return the proofview?] *)
  ; goals : Evar.t list
  (** Focused goals *)
  ; entry : Proofview.entry
  (** Entry for the proofview *)
  ; stack : (Evar.t list * Evar.t list) list
  (** A representation of the focus stack *)
  ; name : Names.Id.t
  (** The name of the theorem whose proof is being constructed *)
  ; poly : PolyFlags.t
  (** Universe polymorphism *)
  }

val data : t -> data

(*** General proof functions ***)
val start
  :  name:Names.Id.t
  -> poly:PolyFlags.t
  -> ?typing_flags:Declarations.typing_flags
  -> Evd.evar_map -> (Environ.env * EConstr.types) list -> t

val dependent_start
  :  name:Names.Id.t
  -> poly:PolyFlags.t
  -> ?typing_flags:Declarations.typing_flags
  -> Proofview.telescope -> t

(* Returns [true] if the considered proof is completed, that is if no goal remain
    to be considered (this does not require that all evars have been solved). *)
val is_done : t -> bool

(* Returns the list of partial proofs to initial goals. *)
val partial_proof : t -> EConstr.constr list

val compact : t -> t

(** [update_sigma_univs] lifts [UState.update_sigma_univs] to the proof *)
val update_sigma_univs : UGraph.t -> t -> t

(*** Focusing actions ***)

(* ['a focus_kind] is the type used by focusing and unfocusing
    commands to synchronise. Focusing and unfocusing commands use
    a particular ['a focus_kind], and if they don't match, the unfocusing command
    will fail.
    When focusing with an ['a focus_kind], an information of type ['a] is
    stored at the focusing point. An example use is the "induction" tactic
    of the declarative mode where sub-tactics must be aware of the current
    induction argument. *)
type 'a focus_kind
val new_focus_kind : string -> 'a focus_kind

(* To be authorized to unfocus one must meet the condition prescribed by
    the action which focused.
    Conditions always carry a focus kind, and inherit their type parameter
    from it.*)
type 'a focus_condition
(* [no_cond] only checks that the unfocusing command uses the right
    [focus_kind].
   If [loose_end] (default [false]) is [true], then if the [focus_kind]
   doesn't match, then unfocusing can occur, provided it unfocuses
   an earlier focus.
   For instance bullets can be unfocused in the following situation
   [{- solve_goal. }] because they use a loose-end condition. *)
val no_cond : ?loose_end:bool -> 'a focus_kind -> 'a focus_condition
(* [done_cond] checks that the unfocusing command uses the right [focus_kind]
    and that the focused proofview is complete.
   If [loose_end] (default [false]) is [true], then if the [focus_kind]
   doesn't match, then unfocusing can occur, provided it unfocuses
   an earlier focus.
   For instance bullets can be unfocused in the following situation
   [{ - solve_goal. }] because they use a loose-end condition.  *)
val done_cond : ?loose_end:bool -> 'a focus_kind -> 'a focus_condition

(* focus command (focuses on the [i]th subgoal) *)
(* spiwack: there could also, easily be a focus-on-a-range tactic, is there
   a need for it? *)
val focus : 'a focus_condition -> 'a -> int -> t -> t

(* focus on goal named id *)
val focus_id : 'a focus_condition -> 'a -> Libnames.qualid -> t -> t

exception FullyUnfocused
exception CannotUnfocusThisWay

(* This is raised when trying to focus on non-existing subgoals. It is
   handled by an error message but one may need to catch it and
   settle a better error message in some case (suggesting a better
   bullet for example), see proof_global.ml function Bullet.pop and
   Bullet.push. *)
exception NoSuchGoals of int * int

exception NoSuchGoal of Libnames.qualid option

(* Unfocusing command.
   Raises [FullyUnfocused] if the proof is not focused.
   Raises [CannotUnfocusThisWay] if the proof the unfocusing condition
     is not met. *)
val unfocus : 'a focus_kind -> t -> unit -> t

(* [unfocused p] returns [true] when [p] is fully unfocused. *)
val unfocused : t -> bool

(** Unfocus everything (fail if no allowed). *)
val unfocus_all : t -> t

(** Brackets "{" and "}" *)

type subproof_select =
  | SubproofNth of int
  | SubproofId of Libnames.qualid
  | SubproofAbstract

val start_subproof : subproof_select -> t -> t

val end_subproof : t -> t

(* [get_at_focus k] gets the information stored at the closest focus point
    of kind [k].
    Raises [NoSuchFocus] if there is no focus point of kind [k]. *)
exception NoSuchFocus
val get_at_focus : 'a focus_kind -> t -> 'a

(* [is_last_focus k] check if the most recent focus is of kind [k] *)
val is_last_focus : 'a focus_kind -> t -> bool

(* returns [true] if there is no goal under focus. *)
val no_focused_goal : t -> bool

(*** Tactics ***)

(* the returned boolean signal whether an unsafe tactic has been
   used. In which case it is [false]. *)
val run_tactic
  :  Environ.env
  -> 'a Proofview.tactic -> t -> t * (Environ.env*bool*Proofview_monad.Info.tree) * 'a

val maximal_unfocus : 'a focus_kind -> t -> t

(*** Commands ***)

(* Remove all the goals from the shelf and adds them at the end of the
   focused goals. *)
val unshelve : t -> t

(* Gives a unique identifier to each goal. The identifier is
   guaranteed to contain no space. *)
val goal_uid : Evar.t -> string

val pr_proof : t -> Pp.t

(* All the subgoals of the proof, including those which are not focused. *)
val background_subgoals : t -> Evar.t list

(* returns the set of all goals in the proof *)
val all_goals : t -> Evar.Set.t

(** [solve (select_nth n) tac] applies tactic [tac] to the [n]th
    subgoal of the current focused proof. [solve SelectAll
    tac] applies [tac] to all subgoals. *)

val solve :
     ?with_end_tac:unit Proofview.tactic
  -> Environ.env
  -> Goal_select.t
  -> int option
  -> unit Proofview.tactic
  -> t
  -> t * bool

(** Option telling if unification heuristics should be used. *)
val use_unification_heuristics : unit -> bool

exception SuggestNoSuchGoals of int * t

(** {6 Helpers to obtain proof state when in an interactive proof } *)
val get_goal_context_gen : t -> int -> Evd.evar_map * Environ.env

(** [get_proof_context ()] gets the goal context for the first subgoal
    of the proof *)
val get_proof_context : t -> Evd.evar_map * Environ.env

val purge_side_effects : t -> t * Evd.side_effects

(** [set_used_variables env kept p] clears variables not in [kept]
    from the proof terms, with an error if this is impossible
    (eg "#[refine]" with the refine term using a forbidden
    variable). *)
val set_used_variables : Environ.env -> kept:Names.Id.Set.t -> t -> t

(** Exposed for printing *)
exception ProofUsingClearDependency of
    Environ.env * Evd.evar_map * Names.Id.t * Evarutil.clear_dependency_error * Names.GlobRef.t option

val abstract_hook : (unit Proofview.tactic -> unit Proofview.tactic) Hook.t
