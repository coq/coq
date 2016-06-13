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
