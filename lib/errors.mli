(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** This modules implements basic manipulations of errors for use
    throughout Coq's code. *)

(** [register_handler h] registers [h] as a handler.
    When an expression is printed with [print e], it
    goes through all registered handles (the most
    recent first) until a handle deals with it.

    Handles signal that they don't deal with some exception
    by raising [Unhandled].

    Handles can raise exceptions themselves, in which
    case, the exception is passed to the handles which
    were registered before.

    The exception that are considered anomalies should not be
    handled by registered handlers.
*)

exception Unhandled

val register_handler : (exn -> Pp.std_ppcmds) -> unit

(** The standard exception printer *)
val print : exn -> Pp.std_ppcmds

(** Same as [print], except that the "Please report" part of an anomaly
    isn't printed (used in Ltac debugging). *)
val print_no_report : exn -> Pp.std_ppcmds

(** Same as [print], except that anomalies are not printed but re-raised
    (used for the Fail command) *)
val print_no_anomaly : exn -> Pp.std_ppcmds
