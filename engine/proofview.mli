(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This files defines the basic mechanism of proofs: the [proofview]
    type is the state which tactics manipulate (a global state for
    existential variables, together with the list of goals), and the type
    ['a tactic] is the (abstract) type of tactics modifying the proof
    state and returning a value of type ['a]. *)

open Util
open EConstr

(** Main state of tactics *)
type proofview

(** Returns a stylised view of a proofview for use by, for instance,
    ide-s. *)
(* spiwack: the type of [proofview] will change as we push more
   refined functions to ide-s. This would be better than spawning a
   new nearly identical function everytime. Hence the generic name. *)
(* In this version: returns the list of focused goals together with
   the [evar_map] context. *)
val proofview : proofview -> Evar.t list * Evd.evar_map


(** {6 Starting and querying a proof view} *)

(** Abstract representation of the initial goals of a proof. *)
type entry

(** Optimize memory consumption *)
val compact : entry -> proofview -> entry * proofview

(** Initialises a proofview, the main argument is a list of
    environments (including a [named_context] which are used as
    hypotheses) pair with conclusion types, creating accordingly many
    initial goals. Because a proof does not necessarily starts in an
    empty [evar_map] (indeed a proof can be triggered by an incomplete
    pretyping), [init] takes an additional argument to represent the
    initial [evar_map]. *)
val init : Evd.evar_map -> (Environ.env * types) list -> entry * proofview

(** A [telescope] is a list of environment and conclusion like in
    {!init}, except that each element may depend on the previous
    goals. The telescope passes the goals in the form of a
    [Term.constr] which represents the goal as an [evar]. The
    [evar_map] is threaded in state passing style. *)
type telescope =
  | TNil of Evd.evar_map
  | TCons of Environ.env * Evd.evar_map * types * (Evd.evar_map -> constr -> telescope)

(** Like {!init}, but goals are allowed to be dependent on one
    another. Dependencies between goals is represented with the type
    [telescope] instead of [list]. Note that the first [evar_map] of
    the telescope plays the role of the [evar_map] argument in
    [init]. *)
val dependent_init  : telescope -> entry * proofview

(** [finished pv] is [true] if and only if [pv] is complete. That is,
    if it has an empty list of focused goals. There could still be
    unsolved subgoals, but they would then be out of focus. *)
val finished : proofview -> bool

(** Returns the current [evar] state. *)
val return : proofview -> Evd.evar_map

val partial_proof : entry -> proofview -> constr list
val initial_goals : entry -> (constr * types) list

(** goal <-> goal_with_state *)

val with_empty_state :
  Proofview_monad.goal ->  Proofview_monad.goal_with_state
val drop_state :
  Proofview_monad.goal_with_state -> Proofview_monad.goal
val goal_with_state :
  Proofview_monad.goal -> Proofview_monad.StateStore.t ->
    Proofview_monad.goal_with_state

(** {6 Focusing commands} *)

(** A [focus_context] represents the part of the proof view which has
    been removed by a focusing action, it can be used to unfocus later
    on. *)
type focus_context

(** Returns a stylised view of a focus_context for use by, for
    instance, ide-s. *)
(* spiwack: the type of [focus_context] will change as we push more
   refined functions to ide-s. This would be better than spawning a
   new nearly identical function everytime. Hence the generic name. *)
(* In this version: the goals in the context, as a "zipper" (the first
   list is in reversed order). *)
val focus_context : focus_context -> Evar.t list * Evar.t list

(** [focus i j] focuses a proofview on the goals from index [i] to
    index [j] (inclusive, goals are indexed from [1]). I.e. goals
    number [i] to [j] become the only focused goals of the returned
    proofview.  It returns the focused proofview, and a context for
    the focus stack. *)
val focus : int -> int -> proofview -> proofview * focus_context

(** Unfocuses a proofview with respect to a context. *)
val unfocus : focus_context -> proofview -> proofview


(** {6 The tactic monad} *)

(** - Tactics are objects which apply a transformation to all the
    subgoals of the current view at the same time. By opposition to
    the old vision of applying it to a single goal. It allows tactics
    such as [shelve_unifiable], tactics to reorder the focused goals,
    or global automation tactic for dependent subgoals (instantiating
    an evar has influences on the other goals of the proof in
    progress, not being able to take that into account causes the
    current eauto tactic to fail on some instances where it could
    succeed).  Another benefit is that it is possible to write tactics
    that can be executed even if there are no focused goals.
    - Tactics form a monad ['a tactic], in a sense a tactic can be
    seen as a function (without argument) which returns a value of
    type 'a and modifies the environment (in our case: the view).
    Tactics of course have arguments, but these are given at the
    meta-level as OCaml functions.  Most tactics in the sense we are
    used to return [()], that is no really interesting values. But
    some might pass information around.  The tactics seen in Coq's
    Ltac are (for now at least) only [unit tactic], the return values
    are kept for the OCaml toolkit.  The operation or the monad are
    [Proofview.tclUNIT] (which is the "return" of the tactic monad)
    [Proofview.tclBIND] (which is the "bind") and [Proofview.tclTHEN]
    (which is a specialized bind on unit-returning tactics).
    - Tactics have support for full-backtracking. Tactics can be seen
    having multiple success: if after returning the first success a
    failure is encountered, the tactic can backtrack and use a second
    success if available. The state is backtracked to its previous
    value, except the non-logical state defined in the {!NonLogical}
    module below.
*)


(** The abstract type of tactics *)
type +'a tactic 

(** Applies a tactic to the current proofview. Returns a tuple
    [a,pv,(b,sh,gu)] where [a] is the return value of the tactic, [pv]
    is the updated proofview, [b] a boolean which is [true] if the
    tactic has not done any action considered unsafe (such as
    admitting a lemma), [sh] is the list of goals which have been
    shelved by the tactic, and [gu] the list of goals on which the
    tactic has given up. In case of multiple success the first one is
    selected. If there is no success, fails with
    {!Logic_monad.TacticFailure}*)
val apply : Environ.env -> 'a tactic -> proofview -> 'a
                                                   * proofview
                                                   * (bool*Evar.t list*Evar.t list)
                                                   * Proofview_monad.Info.tree

(** {7 Monadic primitives} *)

(** Unit of the tactic monad. *)
val tclUNIT : 'a -> 'a tactic
 
(** Bind operation of the tactic monad. *)
val tclBIND : 'a tactic -> ('a -> 'b tactic) -> 'b tactic

(** Interprets the ";" (semicolon) of Ltac. As a monadic operation,
    it's a specialized "bind". *)
val tclTHEN : unit tactic -> 'a tactic -> 'a tactic

(** [tclIGNORE t] has the same operational content as [t], but drops
    the returned value. *)
val tclIGNORE : 'a tactic -> unit tactic

(** Generic monadic combinators for tactics. *)
module Monad : Monad.S with type +'a t = 'a tactic

(** {7 Failure and backtracking} *)

(** [tclZERO e] fails with exception [e]. It has no success. *)
val tclZERO : ?info:Exninfo.info -> exn -> 'a tactic

(** [tclOR t1 t2] behaves like [t1] as long as [t1] succeeds. Whenever
    the successes of [t1] have been depleted and it failed with [e],
    then it behaves as [t2 e]. In other words, [tclOR] inserts a
    backtracking point. *)
val tclOR : 'a tactic -> (iexn -> 'a tactic) -> 'a tactic

(** [tclORELSE t1 t2] is equal to [t1] if [t1] has at least one
    success or [t2 e] if [t1] fails with [e]. It is analogous to
    [try/with] handler of exception in that it is not a backtracking
    point. *)
val tclORELSE : 'a tactic -> (iexn -> 'a tactic) -> 'a tactic

(** [tclIFCATCH a s f] is a generalisation of {!tclORELSE}: if [a]
    succeeds at least once then it behaves as [tclBIND a s] otherwise,
    if [a] fails with [e], then it behaves as [f e]. *)
val tclIFCATCH : 'a tactic -> ('a -> 'b tactic) -> (iexn -> 'b tactic) -> 'b tactic

(** [tclONCE t] behave like [t] except it has at most one success:
    [tclONCE t] stops after the first success of [t]. If [t] fails
    with [e], [tclONCE t] also fails with [e]. *)
val tclONCE : 'a tactic -> 'a tactic

(** [tclEXACTLY_ONCE e t] succeeds as [t] if [t] has exactly one
    success. Otherwise it fails. The tactic [t] is run until its first
    success, then a failure with exception [e] is simulated. It [t]
    yields another success, then [tclEXACTLY_ONCE e t] fails with
    [MoreThanOneSuccess] (it is a user error). Otherwise,
    [tclEXACTLY_ONCE e t] succeeds with the first success of
    [t]. Notice that the choice of [e] is relevant, as the presence of
    further successes may depend on [e] (see {!tclOR}). *)
exception MoreThanOneSuccess
val tclEXACTLY_ONCE : exn -> 'a tactic -> 'a tactic

(** [tclCASE t] splits [t] into its first success and a
    continuation. It is the most general primitive to control
    backtracking. *)
type 'a case =
  | Fail of iexn
  | Next of 'a * (iexn -> 'a tactic)
val tclCASE : 'a tactic -> 'a case tactic

(** [tclBREAK p t] is a generalization of [tclONCE t]. Instead of
    stopping after the first success, it succeeds like [t] until a
    failure with an exception [e] such that [p e = Some e'] is raised. At
    which point it drops the remaining successes, failing with [e'].
    [tclONCE t] is equivalent to [tclBREAK (fun e -> Some e) t]. *)
val tclBREAK : (iexn -> iexn option) -> 'a tactic -> 'a tactic


(** {7 Focusing tactics} *)

(** [tclFOCUS i j t] applies [t] after focusing on the goals number
    [i] to [j] (see {!focus}). The rest of the goals is restored after
    the tactic action. If the specified range doesn't correspond to
    existing goals, fails with [NoSuchGoals] (a user error). this
    exception is caught at toplevel with a default message + a hook
    message that can be customized by [set_nosuchgoals_hook] below.
    This hook is used to add a suggestion about bullets when
    applicable. *)
exception NoSuchGoals of int
val set_nosuchgoals_hook: (int -> Pp.t) -> unit

val tclFOCUS : int -> int -> 'a tactic -> 'a tactic

(** [tclFOCUSLIST li t] applies [t] on the list of focused goals
    described by [li]. Each element of [li] is a pair [(i, j)] denoting
    the goals numbered from [i] to [j] (inclusive, starting from 1).
    It will try to apply [t] to all the valid goals in any of these
    intervals. If the set of such goals is not a single range, then it
    will move goals such that it is a single range. (So, for
    instance, [[1, 3-5]; idtac.] is not the identity.)
    If the set of such goals is empty, it will fail. *)
val tclFOCUSLIST : (int * int) list -> 'a tactic -> 'a tactic

(** [tclFOCUSID x t] applies [t] on a (single) focused goal like
    {!tclFOCUS}. The goal is found by its name rather than its
    number.*)
val tclFOCUSID : Names.Id.t -> 'a tactic -> 'a tactic

(** [tclTRYFOCUS i j t] behaves like {!tclFOCUS}, except that if the
    specified range doesn't correspond to existing goals, behaves like
    [tclUNIT ()] instead of failing. *)
val tclTRYFOCUS : int -> int -> unit tactic -> unit tactic


(** {7 Dispatching on goals} *)

(** Dispatch tacticals are used to apply a different tactic to each
    goal under focus. They come in two flavours: [tclDISPATCH] takes a
    list of [unit tactic]-s and build a [unit tactic]. [tclDISPATCHL]
    takes a list of ['a tactic] and returns an ['a list tactic].

    They both work by applying each of the tactic in a focus
    restricted to the corresponding goal (starting with the first
    goal). In the case of [tclDISPATCHL], the tactic returns a list of
    the same size as the argument list (of tactics), each element
    being the result of the tactic executed in the corresponding goal.

    When the length of the tactic list is not the number of goal,
    raises [SizeMismatch (g,t)] where [g] is the number of available
    goals, and [t] the number of tactics passed. *)
exception SizeMismatch of int*int
val tclDISPATCH : unit tactic list -> unit tactic
val tclDISPATCHL : 'a tactic list -> 'a list tactic

(** [tclEXTEND b r e] is a variant of {!tclDISPATCH}, where the [r]
    tactic is "repeated" enough time such that every goal has a tactic
    assigned to it ([b] is the list of tactics applied to the first
    goals, [e] to the last goals, and [r] is applied to every goal in
    between). *)
val tclEXTEND : unit tactic list -> unit tactic -> unit tactic list -> unit tactic

(** [tclINDEPENDENT tac] runs [tac] on each goal successively, from
    the first one to the last one. Backtracking in one goal is
    independent of backtracking in another. It is equivalent to
    [tclEXTEND [] tac []]. *)
val tclINDEPENDENT : unit tactic -> unit tactic
val tclINDEPENDENTL: 'a tactic -> 'a list tactic


(** {7 Goal manipulation} *)

(** Shelves all the goals under focus. The goals are placed on the
    shelf for later use (or being solved by side-effects). *)
val shelve : unit tactic

(** Shelves the given list of goals, which might include some that are
    under focus and some that aren't. All the goals are placed on the
    shelf for later use (or being solved by side-effects). *)
val shelve_goals : Evar.t list -> unit tactic

(** [unifiable sigma g l] checks whether [g] appears in another
    subgoal of [l]. The list [l] may contain [g], but it does not
    affect the result. Used by [shelve_unifiable]. *)
val unifiable : Evd.evar_map -> Evar.t -> Evar.t list -> bool

(** Shelves the unifiable goals under focus, i.e. the goals which
    appear in other goals under focus (the unfocused goals are not
    considered). *)
val shelve_unifiable : unit tactic

(** Idem but also returns the list of shelved variables *)
val shelve_unifiable_informative : Evar.t list tactic

(** [guard_no_unifiable] returns the list of unifiable goals if some
    goals are unifiable (see {!shelve_unifiable}) in the current focus. *)
val guard_no_unifiable : Names.Name.t list option tactic

(** [unshelve l p] adds all the goals in [l] at the end of the focused
    goals of p *)
val unshelve : Evar.t list -> proofview -> proofview

(** [depends_on g1 g2 sigma] checks if g1 occurs in the type/ctx of g2 *)
val depends_on : Evd.evar_map -> Evar.t -> Evar.t -> bool

(** [with_shelf tac] executes [tac] and returns its result together with
    the set of goals shelved by [tac]. The current shelf is unchanged
    and the returned list contains only unsolved goals. *)
val with_shelf : 'a tactic -> (Evar.t list * 'a) tactic

(** If [n] is positive, [cycle n] puts the [n] first goal last. If [n]
    is negative, then it puts the [n] last goals first.*)
val cycle : int -> unit tactic

(** [swap i j] swaps the position of goals number [i] and [j]
    (negative numbers can be used to address goals from the end. Goals
    are indexed from [1]. For simplicity index [0] corresponds to goal
    [1] as well, rather than raising an error. *)
val swap : int -> int -> unit tactic

(** [revgoals] reverses the list of focused goals. *)
val revgoals : unit tactic

(** [numgoals] returns the number of goals under focus. *)
val numgoals : int tactic


(** {7 Access primitives} *)

(** [tclEVARMAP] doesn't affect the proof, it returns the current
    [evar_map]. *)
val tclEVARMAP : Evd.evar_map tactic

(** [tclENV] doesn't affect the proof, it returns the current
    environment. It is not the environment of a particular goal,
    rather the "global" environment of the proof. The goal-wise
    environment is obtained via {!Proofview.Goal.env}. *)
val tclENV : Environ.env tactic


(** {7 Put-like primitives} *)

(** [tclEFFECTS eff] add the effects [eff] to the current state. *)
val tclEFFECTS : Safe_typing.private_constants -> unit tactic

(** [mark_as_unsafe] declares the current tactic is unsafe. *)
val mark_as_unsafe : unit tactic

(** Gives up on the goal under focus. Reports an unsafe status. Proofs
    with given up goals cannot be closed. *)
val give_up : unit tactic

(** {7 Control primitives} *)

(** [tclPROGRESS t] checks the state of the proof after [t]. It it is
    identical to the state before, then [tclePROGRESS t] fails, otherwise
    it succeeds like [t]. *)
val tclPROGRESS : 'a tactic -> 'a tactic

(** Checks for interrupts *)
val tclCHECKINTERRUPT : unit tactic

exception Timeout
(** [tclTIMEOUT n t] can have only one success.
    In case of timeout if fails with [tclZERO Timeout]. *)
val tclTIMEOUT : int -> 'a tactic -> 'a tactic

(** [tclTIME s t] displays time for each atomic call to t, using s as an
    identifying annotation if present *)
val tclTIME : string option -> 'a tactic -> 'a tactic

(** {7 Unsafe primitives} *)

(** The primitives in the [Unsafe] module should be avoided as much as
    possible, since they can make the proof state inconsistent. They are
    nevertheless helpful, in particular when interfacing the pretyping and
    the proof engine. *)
module Unsafe : sig

  (** [tclEVARS sigma] replaces the current [evar_map] by [sigma]. If
      [sigma] has new unresolved [evar]-s they will not appear as
      goal. If goals have been solved in [sigma] they will still
      appear as unsolved goals. *)
  val tclEVARS : Evd.evar_map -> unit tactic
    
  (** Like {!tclEVARS} but also checks whether goals have been solved. *)
  val tclEVARSADVANCE : Evd.evar_map -> unit tactic

  (** Set the global environment of the tactic *)
  val tclSETENV : Environ.env -> unit tactic

  (** [tclNEWGOALS gls] adds the goals [gls] to the ones currently
      being proved, appending them to the list of focused goals. If a
      goal is already solved, it is not added. *)
  val tclNEWGOALS : Proofview_monad.goal_with_state list -> unit tactic

  (** [tclSETGOALS gls] sets goals [gls] as the goals being under focus. If a
      goal is already solved, it is not set. *)
  val tclSETGOALS : Proofview_monad.goal_with_state list -> unit tactic

  (** [tclGETGOALS] returns the list of goals under focus. *)
  val tclGETGOALS : Proofview_monad.goal_with_state list tactic

  (** [tclSETSHELF gls] sets goals [gls] as the current shelf. *)
  val tclSETSHELF : Evar.t list -> unit tactic

  (** [tclGETSHELF] returns the list of goals on the shelf. *)
  val tclGETSHELF : Evar.t list tactic

  (** [tclPUTSHELF] appends goals to the shelf. *)
  val tclPUTSHELF : Evar.t list -> unit tactic

  (** [tclPUTGIVENUP] add an given up goal. *)
  val tclPUTGIVENUP : Evar.t list -> unit tactic

  (** Sets the evar universe context. *)
  val tclEVARUNIVCONTEXT : UState.t -> unit tactic

  (** Clears the future goals store in the proof view. *)
  val reset_future_goals : proofview -> proofview

  (** Give an evar the status of a goal (changes its source location
      and makes it unresolvable for type classes. *)
  val mark_as_goal : Evd.evar_map -> Evar.t -> Evd.evar_map

  (** Make an evar unresolvable for type classes. *)
  val mark_as_unresolvable : proofview -> Evar.t -> proofview

  (** [advance sigma g] returns [Some g'] if [g'] is undefined and is
      the current avatar of [g] (for instance [g] was changed by [clear]
      into [g']). It returns [None] if [g] has been (partially)
      solved. *)
  val advance : Evd.evar_map -> Evar.t -> Evar.t option

  (** [undefined sigma l] applies [advance] to the goals of [l], then
      returns the subset of resulting goals which have not yet been
      defined *)
  val undefined : Evd.evar_map -> Proofview_monad.goal_with_state list ->
    Proofview_monad.goal_with_state list

  val typeclass_resolvable : unit Evd.Store.field

end

(** This module gives access to the innards of the monad. Its use is
    restricted to very specific cases. *)
module UnsafeRepr :
sig
  type state = Proofview_monad.Logical.Unsafe.state
  val repr : 'a tactic -> ('a, state, state, iexn) Logic_monad.BackState.t
  val make : ('a, state, state, iexn) Logic_monad.BackState.t -> 'a tactic
end

(** {6 Goal-dependent tactics} *)

module Goal : sig

  (** Type of goals. *)
  type t

  (** Normalises the argument goal. *)
  val normalize : t -> t tactic

  (** [concl], [hyps], [env] and [sigma] given a goal [gl] return
      respectively the conclusion of [gl], the hypotheses of [gl], the
      environment of [gl] (i.e. the global environment and the
      hypotheses) and the current evar map. *)
  val concl : t -> constr
  val hyps : t -> named_context
  val env : t -> Environ.env
  val sigma : t -> Evd.evar_map
  val extra : t -> Evd.Store.t
  val state : t -> Proofview_monad.StateStore.t

  (** [nf_enter t] applies the goal-dependent tactic [t] in each goal
      independently, in the manner of {!tclINDEPENDENT} except that
      the current goal is also given as an argument to [t]. The goal
      is normalised with respect to evars. *)
  val nf_enter : (t -> unit tactic) -> unit tactic

  (** Like {!nf_enter}, but does not normalize the goal beforehand. *)
  val enter : (t -> unit tactic) -> unit tactic

  (** Like {!enter}, but assumes exactly one goal under focus, raising *)
  (** a fatal error otherwise. *)
  val enter_one : ?__LOC__:string -> (t -> 'a tactic) -> 'a tactic

  (** Recover the list of current goals under focus, without evar-normalization.
      FIXME: encapsulate the level in an existential type. *)
  val goals : t tactic list tactic

  (** [unsolved g] is [true] if [g] is still unsolved in the current
      proof state. *)
  val unsolved : t -> bool tactic

  (** Compatibility: avoid if possible *)
  val goal : t -> Evar.t
  val print : t -> Goal.goal Evd.sigma

end


(** {6 Trace} *)

module Trace : sig

  (** [record_info_trace t] behaves like [t] except the [info] trace
      is stored. *)
  val record_info_trace : 'a tactic -> 'a tactic

  val log : Proofview_monad.lazy_msg -> unit tactic
  val name_tactic : Proofview_monad.lazy_msg -> 'a tactic -> 'a tactic

  val pr_info : ?lvl:int -> Proofview_monad.Info.tree -> Pp.t

end


(** {6 Non-logical state} *)

(** The [NonLogical] module allows the execution of effects (including
    I/O) in tactics (non-logical side-effects are not discarded at
    failures). *)
module NonLogical : module type of Logic_monad.NonLogical

(** [tclLIFT c] is a tactic which behaves exactly as [c]. *)
val tclLIFT : 'a NonLogical.t -> 'a tactic


(**/**)

(*** Compatibility layer with <= 8.2 tactics ***)
module V82 : sig
  type tac = Evar.t Evd.sigma -> Evar.t list Evd.sigma

  (* [nf_evars=true] applies the evar (assignment) map to the goals
   * (conclusion and context) before calling the tactic *)
  val tactic : ?nf_evars:bool -> tac -> unit tactic

  (* normalises the evars in the goals, and stores the result in
     solution. *)
  val nf_evar_goals : unit tactic

  val has_unresolved_evar : proofview -> bool

  (* Main function in the implementation of Grab Existential Variables.
     Resets the proofview's goals so that it contains all unresolved evars
     (in chronological order of insertion). *)
  val grab : proofview -> proofview

  val top_goals : entry -> proofview -> Evar.t list Evd.sigma

  (* returns the existential variable used to start the proof *)
  val top_evars : entry -> Evar.t list

  (* Caution: this function loses quite a bit of information. It
     should be avoided as much as possible.  It should work as
     expected for a tactic obtained from {!V82.tactic} though. *)
  val of_tactic : 'a tactic -> tac

  (* marks as unsafe if the argument is [false] *)
  val put_status : bool -> unit tactic

  (* exception for which it is deemed to be safe to transmute into
     tactic failure. *)
  val catchable_exception : exn -> bool

  (* transforms every Ocaml (catchable) exception into a failure in
     the monad. *)
  val wrap_exceptions : (unit -> 'a tactic) -> 'a tactic
end

(** {7 Notations} *)

module Notations : sig

  (** {!tclBIND} *)
  val (>>=) : 'a tactic -> ('a -> 'b tactic) -> 'b tactic
  (** {!tclTHEN} *)
  val (<*>) : unit tactic -> 'a tactic -> 'a tactic
  (** {!tclOR}: [t1+t2] = [tclOR t1 (fun _ -> t2)]. *)
  val (<+>) : 'a tactic -> 'a tactic -> 'a tactic

end
