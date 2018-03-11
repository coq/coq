(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This modules implements basic manipulations of errors for use
    throughout Coq's code. *)

(** {6 Error handling} *)

val push : exn -> Exninfo.iexn
(** Alias for [Backtrace.add_backtrace]. *)

(** {6 Generic errors.}

 [Anomaly] is used for system errors and [UserError] for the
   user's ones. *)

val make_anomaly : ?label:string -> Pp.t -> exn
(** Create an anomaly. *)

val anomaly : ?loc:Loc.t -> ?label:string -> Pp.t -> 'a
(** Raise an anomaly, with an optional location and an optional
    label identifying the anomaly. *)

val is_anomaly : exn -> bool
(** Check whether a given exception is an anomaly.
    This is mostly provided for compatibility. Please avoid doing specific
    tricks with anomalies thanks to it. See rather [noncritical] below. *)

exception UserError of string option * Pp.t
(** Main error signaling exception. It carries a header plus a pretty printing
    doc *)

val user_err : ?loc:Loc.t -> ?hdr:string -> Pp.t -> 'a
(** Main error raising primitive. [user_err ?loc ?hdr pp] signals an
    error [pp] with optional header and location [hdr] [loc] *)

exception AlreadyDeclared of Pp.t
val alreadydeclared : Pp.t -> 'a

val invalid_arg : ?loc:Loc.t -> string -> 'a

(** [todo] is for running of an incomplete code its implementation is
   "do nothing" (or print a message), but this function should not be
   used in a released code *)

val todo : string -> unit

exception Timeout

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

val register_handler : (exn -> Pp.t) -> unit

(** The standard exception printer *)
val print : ?info:Exninfo.info -> exn -> Pp.t
val iprint : Exninfo.iexn -> Pp.t

(** Same as [print], except that the "Please report" part of an anomaly
    isn't printed (used in Ltac debugging). *)
val print_no_report : exn -> Pp.t
val iprint_no_report : Exninfo.iexn -> Pp.t

(** Critical exceptions should not be caught and ignored by mistake
    by inner functions during a [vernacinterp]. They should be handled
    only in [Toplevel.do_vernac] (or Ideslave), to be displayed to the user.
    Typical example: [Sys.Break], [Assert_failure], [Anomaly] ...
*)
val noncritical : exn -> bool

(** Check whether an exception is handled by some toplevel printer. The
    [Anomaly] exception is never handled. *)
val handled : exn -> bool
