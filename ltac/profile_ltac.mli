(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Ltac profiling primitives *)

val do_profile : string -> ('a * Tacexpr.ltac_call_kind) list -> 'b Proofview.tactic -> 'b Proofview.tactic

val set_profiling : bool -> unit

val get_profiling : unit -> bool

val entered_call : unit -> unit

val print_results : unit -> unit

val print_results_tactic : string -> unit

val reset_profile : unit -> unit

val do_print_results_at_close : unit -> unit

(* The collected statistics for a tactic. The timing data is collected over all
 * instances of a given tactic from its parent. E.g. if tactic 'aaa' calls
 * 'foo' twice, then 'aaa' will contain just one entry for 'foo' with the
 * statistics of the two invocations combined, and also combined over all
 * invocations of 'aaa'.
 * total:     time spent running this tactic and its subtactics (seconds)
 * self:      time spent running this tactic, minus its subtactics (seconds)
 * num_calls: the number of invocations of this tactic that have been made
 * max_total: the greatest running time of a single invocation (seconds)
 *)
type ltacprof_entry = {total : float; self : float; num_calls : int; max_total : float}
(* A profiling entry for a tactic and the tactics that it called
 * name:       name of the tactic
 * statistics: profiling data collected
 * tactics:    profiling results for each tactic that this tactic invoked;
 *             multiple invocations of the same sub-tactic are combined together.
 *)
type ltacprof_tactic = {name: string; statistics : ltacprof_entry; tactics : ltacprof_tactic list}
(* The full results of profiling
 * total_time: time spent running tactics (seconds)
 * tactics:    the tactics that have been invoked since profiling was started or reset
 *)
type ltacprof_results = {total_time : float; tactics : ltacprof_tactic list}

(* Returns the profiling results for the currently-focused state. *)
val get_profiling_results : unit -> ltacprof_results

