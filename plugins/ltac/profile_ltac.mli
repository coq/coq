(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** Ltac profiling primitives *)

(* Note(JasonGross): Ltac semantics are a bit insane.  There isn't
   really a good notion of how many times a tactic has been "called",
   because tactics can be partially evaluated, and it's unclear
   whether the number of "calls" should be the number of times the
   body is fetched and unfolded, or the number of times the code is
   executed to a value, etc.  The logic in [Tacinterp.eval_tactic]
   gives a decent approximation, which I believe roughly corresponds
   to the number of times that the engine runs the tactic value which
   results from evaluating the tactic expression bound to the name
   we're considering.  However, this is a poor approximation of the
   time spent in the tactic; we want to consider time spent evaluating
   a tactic expression to a tactic value to be time spent in the
   expression, not just time spent in the caller of the expression.
   So we need to wrap some nodes in additional profiling calls which
   don't count towards to total call count.  Whether or not a call
   "counts" is indicated by the [count_call] boolean argument.

   Unfortunately, at present, we can get very strange call graphs when
   a named tactic expression never runs as a tactic value: if we have
   [Ltac t0 := t.] and [Ltac t1 := t0.], then [t1] is considered to
   run 0(!) times.  It evaluates to [t] during tactic expression
   evaluation, and although the call trace records the fact that it
   was called by [t0] which was called by [t1], the tactic running
   phase never sees this.  Thus we get one call tree (from expression
   evaluation) that has [t1] calls [t0] calls [t], and another call
   tree which says that the caller of [t1] calls [t] directly; the
   expression evaluation time goes in the first tree, and the call
   count and tactic running time goes in the second tree.  Alas, I
   suspect that fixing this requires a redesign of how the profiler
   hooks into the tactic engine. *)
val do_profile :
  string -> ('a * Tacexpr.ltac_call_kind) list ->
    ?count_call:bool -> 'b Proofview.tactic -> 'b Proofview.tactic

val set_profiling : bool -> unit

(* Cut off results < than specified cutoff *)
val print_results : cutoff:float -> unit

val print_results_tactic : string -> unit

val reset_profile : unit -> unit

val restart_timer : string option -> unit

val finish_timing : prefix:string -> string option -> unit

val do_print_results_at_close : unit -> unit

(* The collected statistics for a tactic. The timing data is collected over all
 * instances of a given tactic from its parent. E.g. if tactic 'aaa' calls
 * 'foo' twice, then 'aaa' will contain just one entry for 'foo' with the
 * statistics of the two invocations combined, and also combined over all
 * invocations of 'aaa'.
 * total:     time spent running this tactic and its subtactics (seconds)
 * local:      time spent running this tactic, minus its subtactics (seconds)
 * ncalls: the number of invocations of this tactic that have been made
 * max_total: the greatest running time of a single invocation (seconds)
 *)
type treenode = {
  name : CString.Map.key;
  total : float;
  local : float;
  ncalls : int;
  max_total : float;
  children : treenode CString.Map.t
}

(* Returns the profiling results known by the current process *)
val get_local_profiling_results : unit -> treenode
val feedback_results : treenode -> unit
