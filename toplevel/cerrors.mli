(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Util
(*i*)

(* Error report. *)

val print_loc : loc -> std_ppcmds

val explain_exn : exn -> std_ppcmds

(** Same, but will re-raise all anomalies instead of explaining them *)

val explain_exn_no_anomaly : exn -> std_ppcmds

(** For debugging purpose (?), the explain function can be twicked *)

val explain_exn_function : (exn -> std_ppcmds) ref
val explain_exn_default : exn -> std_ppcmds

val raise_if_debug : exn -> unit
