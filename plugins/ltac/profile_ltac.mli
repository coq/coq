(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


(** Ltac profiling primitives *)

val do_profile :
  string -> ('a * Tacexpr.ltac_call_kind) list ->
    'b Proofview.tactic -> 'b Proofview.tactic

val set_profiling : bool -> unit

(* Cut off results < than specified cutoff *)
val print_results : cutoff:float -> unit

val print_results_tactic : string -> unit

val reset_profile : unit -> unit

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

