(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Message.

(** Panic *)

Ltac2 @ external throw : exn -> 'a := "rocq-runtime.plugins.ltac2" "throw".
(** Fatal exception throwing. This does not induce backtracking. *)

(** Generic backtracking control *)

Ltac2 @ external zero : exn -> 'a := "rocq-runtime.plugins.ltac2" "zero".
(** [zero e] raises the exception e, passing control to the current backtracking continuation. *)

Ltac2 @ external plus : (unit -> 'a) -> (exn -> 'a) -> 'a := "rocq-runtime.plugins.ltac2" "plus".
(** Backtracking point, cf Backtracking section of the ltac2 refman. *)

Ltac2 @ external once : (unit -> 'a) -> 'a := "rocq-runtime.plugins.ltac2" "once".
(** [once t] behaves like [t], except it has at most one success: [once t]
    stops after the first success of [t]. If [t] fails with [e],
    [once t] also fails with [e]. If [once t; t'] fails on [t'], then [once t] will not backtrack and evaluate [t] for another value, and will instead fail. *)

Ltac2 @ external case : (unit -> 'a) -> ('a * (exn -> 'a)) result := "rocq-runtime.plugins.ltac2" "case".
(** [case] is the most general primitive to control backtracking:
- If [t ()] would fail with [e], [case t] returns [Err e].
- If [t ()] would succeed and evaluate to [v] then [case t] returns [Val (v, h)],
  where [h] is the continuation to execute in case of subsequent failure.
  [case] reifies a backtracking computation into an inspectable value, it allows the programmer to make explicit the effects which are normally implicit (i.e., they do not appear in the type system).
*)

Ltac2 once_plus (run : unit -> 'a) (handle : exn -> 'a) : 'a :=
  once (fun () => plus run handle).
(** [once_plus run handle] is [once] applied to [plus run handle]. *)

(** Proof state manipulation *)

Ltac2 @ external numgoals : unit -> int := "rocq-runtime.plugins.ltac2" "numgoals".
(** Return the number of goals currently focused. *)

Ltac2 @ external dispatch : (unit -> unit) list -> unit := "rocq-runtime.plugins.ltac2" "dispatch".
(** The dispatch tactical is used to apply a different tactic to each
    goal under focus. It works by applying each of the tactics in a focus
    restricted to the corresponding goal (starting with the first
    goal). When the length of the tactic list is not equal to the
    number of focused goals, raises Internal err. *)

Ltac2 @ external extend : (unit -> unit) list -> (unit -> unit) -> (unit -> unit) list -> unit := "rocq-runtime.plugins.ltac2" "extend".
(** extend is a more flexible variant of dispatch, where the second argument
    tactic is "repeated" enough times such that every goal has a tactic
    assigned to it. [extend b r e] applies the tactics in [b] to the first
    [length b] goals, the tactics in [r] to the last [length r] goals, and
    [e] to all tactics in between. Raises Internal err if [length b + length r]
    is greater than the number of goals under focus.*)

Ltac2 @ external enter : (unit -> unit) -> unit := "rocq-runtime.plugins.ltac2" "enter".
(** [enter] takes a single tactic [t] and applies [t] in each goal under focus independently. *)

Ltac2 @ external focus : int -> int -> (unit -> 'a) -> 'a := "rocq-runtime.plugins.ltac2" "focus".
(** [focus i j tac] focuses a proofview on the goals from index [i] to
    index [j] (inclusive, goals are indexed from [1]) and runs
    t with those goals under focus, i.e. goals
    number [i] to [j] become the only focused goals during the execution
    of tac. When [focus] returns, the present focus is restored. If the range [i - j] is invalid, fails with a backtrackable "no such goal" error. *)

Ltac2 @ external cycle : int -> unit := "rocq-runtime.plugins.ltac2" "cycle".
(** If [n] is positive, [cycle n] puts the [n] first goal last. If [n]
    is negative, then it puts the [n] last goals first.*)

Ltac2 @ external shelve : unit -> unit := "rocq-runtime.plugins.ltac2" "shelve".
(** Shelve all goals under focus. The goals are placed on the shelf for later use, or to be solved by side-effects.*)

Ltac2 @ external shelve_unifiable : unit -> unit := "rocq-runtime.plugins.ltac2" "shelve_unifiable".
(** Shelves the unifiable goals under focus, i.e. the goals which
    appear in other goals under focus (the unfocused goals are not
    considered). *)

Ltac2 @ external new_goal : evar -> unit := "rocq-runtime.plugins.ltac2" "new_goal".
(** Adds the given evar to the list of goals as the last one. If it is
    already defined in the current state, don't do anything. Panics if the
    evar is not in the current state. *)

Ltac2 @ external unshelve : (unit -> 'a) -> 'a := "rocq-runtime.plugins.ltac2" "unshelve".
(** Runs the closure, then unshelves existential variables added to the
    shelf by its execution, prepending them to the current goal.
    Returns the value produced by the closure. *)

Ltac2 @ external progress : (unit -> 'a) -> 'a := "rocq-runtime.plugins.ltac2" "progress".
(** [progress t] checks the state of the proof after [t]. It it is
    identical to the state before, then [progress t] fails, otherwise
    it succeeds like [t]. *)

(** Goal inspection *)

Ltac2 @ external goal : unit -> constr := "rocq-runtime.plugins.ltac2" "goal".
(** Panics if there is not exactly one goal under focus. Otherwise returns
    the conclusion of this goal. *)

Ltac2 @ external hyp : ident -> constr := "rocq-runtime.plugins.ltac2" "hyp".
(** Panics if there is more than one goal under focus. If there is no
    goal under focus, looks for the section variable with the given name.
    If there is one, looks for the hypothesis with the given name. *)

Ltac2 @ external hyp_value : ident -> constr option := "rocq-runtime.plugins.ltac2" "hyp_value".
(** Panics if there is more than one goal under focus. If there is no
    goal under focus, looks for the section variable with the given
    name and return its value ("v" in "H := v") if there is one. If
    there is one, looks for the hypothesis with the given name and
    return its value if there is one. *)

Ltac2 @ external hyps : unit -> (ident * constr option * constr) list := "rocq-runtime.plugins.ltac2" "hyps".
(** Panics if there is more than one goal under focus. If there is no
    goal under focus, returns the list of section variables.
    If there is one, returns the list of hypotheses. In both cases, the
    list is ordered with rightmost values being last introduced. *)

(** Refinement *)

Ltac2 @ external refine : (unit -> constr) -> unit := "rocq-runtime.plugins.ltac2" "refine".
(** [refine t] computes the type of the term [t ()] and unifies the
 type with the current goal. All unification variables produced while computing [t ()] not
 solved by this unification process are added as new goals. *)

(** Evars *)

Ltac2 @ external with_holes : (unit -> 'a) -> ('a -> 'b) -> 'b := "rocq-runtime.plugins.ltac2" "with_holes".
(** [with_holes x f] evaluates [x], then apply [f] to the result, and fails if
    all evars generated by the call to [x] have not been solved when [f]
    returns. *)

(** Misc *)

Ltac2 @ external time : string option -> (unit -> 'a) -> 'a := "rocq-runtime.plugins.ltac2" "time".
(** Displays the time taken by a tactic to evaluate. *)

Ltac2 @ external abstract : ident option -> (unit -> unit) -> unit := "rocq-runtime.plugins.ltac2" "abstract".
(** Abstract a subgoal. *)

Ltac2 @ external check_interrupt : unit -> unit := "rocq-runtime.plugins.ltac2" "check_interrupt".
(** For internal use. *)

(** Assertions throwing exceptions and short form throws *)

Ltac2 throw_invalid_argument (msg : string) :=
  Control.throw (Invalid_argument (Some (Message.of_string msg))).

Ltac2 throw_out_of_bounds (msg : string) :=
  Control.throw (Out_of_bounds (Some (Message.of_string msg))).

Ltac2 assert_valid_argument (msg : string) (test : bool) :=
  match test with
  | true => ()
  | false => throw_invalid_argument msg
  end.

Ltac2 assert_bounds (msg : string) (test : bool) :=
  match test with
  | true => ()
  | false => throw_out_of_bounds msg
  end.

Ltac2 assert_true b :=
  if b then () else throw Assertion_failure.

Ltac2 assert_false b :=
  if b then throw Assertion_failure else ().

(** Short form backtracks *)

Ltac2 backtrack_tactic_failure (msg : string) :=
  Control.zero (Tactic_failure (Some (Message.of_string msg))).

(** Backtraces. *)

(** [throw_bt info e] is similar to [throw e], but raises [e] with the
    backtrace represented by [info]. *)
Ltac2 @ external throw_bt : exn -> exninfo -> 'a :=
  "rocq-runtime.plugins.ltac2" "throw_bt".

(** [zero_bt info e] is similar to [zero e], but raises [e] with the
    backtrace represented by [info]. *)
Ltac2 @ external zero_bt : exn -> exninfo -> 'a :=
  "rocq-runtime.plugins.ltac2" "zero_bt".

(** [plus_bt run handle] is similar to [plus run handle] (up to the type
    missmatch for [handle]), but it calls [handle] with an extra argument
    representing the backtrace at the point of the exception. The [handle]
    function can thus decide to re-attach that backtrace when using the
    [throw_bt] or [zero_bt] functions. *)
Ltac2 @ external plus_bt : (unit -> 'a) -> (exn -> exninfo -> 'a) -> 'a :=
  "rocq-runtime.plugins.ltac2" "plus_bt".

(** [once_plus_bt run handle] is a non-backtracking variant of [once_plus]
    that has backtrace support similar to that of [plus_bt]. *)
Ltac2 once_plus_bt (run : unit -> 'a) (handle : exn -> exninfo -> 'a) : 'a :=
  once (fun _ => plus_bt run handle).

Ltac2 @ external clear_err_info : err -> err :=
  "rocq-runtime.plugins.ltac2" "clear_err_info".

Ltac2 clear_exn_info (e : exn) : exn :=
  match e with
  | Init.Internal err => Init.Internal (clear_err_info err)
  | e => e
  end.

(** Timeout. *)

(** [timeout t thunk] calls [thunk ()] with a timeout of [t] seconds. *)
Ltac2 @ external timeout : int -> (unit -> 'a) -> 'a :=
  "rocq-runtime.plugins.ltac2" "timeout".

(** [timeoutf t thunk] calls [thunk ()] with a timeout of [t] seconds. *)
Ltac2 @ external timeoutf : float -> (unit -> 'a) -> 'a :=
  "rocq-runtime.plugins.ltac2" "timeoutf".
