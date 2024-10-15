(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2expr

(** {5 Backtrace} *)

val backtrace : backtrace Exninfo.t

val get_backtrace : backtrace Proofview.tactic

val with_frame : frame -> 'a Proofview.tactic -> 'a Proofview.tactic

val print_ltac2_backtrace : bool ref

val pr_frame_hook : (frame -> Pp.t) Hook.t
