(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This modules implements basic manipulations of errors for use
    throughout Rocq's code. *)

(** {6 Error handling} *)

val push : exn -> Exninfo.iexn
[@@ocaml.deprecated "(8.12) please use [Exninfo.capture]"]

(** {6 Generic errors.}

 [Anomaly] is used for system errors and [UserError] for the
   user's ones. *)

val anomaly : ?loc:Loc.t -> ?info:Exninfo.info -> ?label:string -> Pp.t -> 'a
(** Raise an anomaly, with an optional location and an optional
    label identifying the anomaly. *)

val is_anomaly : exn -> bool
(** Check whether a given exception is an anomaly.
    This is mostly provided for compatibility. Please avoid doing specific
    tricks with anomalies thanks to it. See rather [noncritical] below. *)

exception UserError of Pp.t
(** Main error signaling exception. It carries a header plus a pretty printing
    doc *)

val user_err : ?loc:Loc.t -> ?info:Exninfo.info -> Pp.t -> 'a
(** Main error raising primitive. [user_err ?loc pp] signals an
    error [pp] with optional header and location [loc] *)

exception Timeout

(** [register_handler h] registers [h] as a handler.
    When an expression is printed with [print e], it
    goes through all registered handles (the most
    recent first) until a handle deals with it.

    Handles signal that they don't deal with some exception
    by returning None. Raising any other exception is
    forbidden and will result in an anomaly.

    Exceptions that are considered anomalies should not be
    handled by registered handlers.
*)

val register_handler : (exn -> Pp.t option) -> unit

(** The standard exception printer *)
val print : exn -> Pp.t
val iprint : Exninfo.iexn -> Pp.t

(** Same as [print], except that the "Please report" part of an anomaly
    isn't printed (used in Ltac debugging). *)
val print_no_report : exn -> Pp.t
val iprint_no_report : Exninfo.iexn -> Pp.t

(** "Critical" exceptions, such as anomalies or interruptions should
    not be caught and ignored by mistake by inner Rocq functions by
    means of doing a "catch-all". They should be handled instead by
    the compiler layer which is in charge of coordinating the
    intepretation of Rocq vernaculars.

    Please, avoid exceptions catch-all! If you must do so, then use the form:
    {[
    try my_comp ()
    with exn when noncritical exn ->
      my_handler
    ]}

    If you need to re-raise the excepction, you must work to preserve
    the backtrace and other important information:
    {[
    try my_comp ()
    with exn when noncritical exn ->
      let iexn = Exninfo.capture exn in
      ...
      Exninfo.iraise iexn
    ]}
 *)
val noncritical : exn -> bool

(** Register a printer for errors carrying additional information on
   exceptions. This method is fragile and should be considered
   deprecated *)
val register_additional_error_info
  :  (Exninfo.info -> Pp.t option)
  -> unit

(** [to_result ~f x] reifies (non-critical) exceptions into a [('a,
    iexn) Result.t] type *)
val to_result : f:('a -> 'b) -> 'a -> ('b, Exninfo.iexn) Result.t
