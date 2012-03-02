(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Pp

(** This modules implements basic manipulations of errors for use
    throughout Coq's code. *)

(** {6 Generic errors.}

 [Anomaly] is used for system errors and [UserError] for the
   user's ones. *)

exception Anomaly of string * std_ppcmds
val anomaly : string -> 'a
val anomalylabstrm : string -> std_ppcmds -> 'a
val anomaly_loc : loc * string * std_ppcmds -> 'a

exception UserError of string * std_ppcmds
val error : string -> 'a
val errorlabstrm : string -> std_ppcmds -> 'a
val user_err_loc : loc * string * std_ppcmds -> 'a

exception AlreadyDeclared of std_ppcmds
val alreadydeclared : std_ppcmds -> 'a

val invalid_arg_loc : loc * string -> 'a

(** [todo] is for running of an incomplete code its implementation is
   "do nothing" (or print a message), but this function should not be
   used in a released code *)

val todo : string -> unit

exception Timeout

(** Like [Exc_located], but specifies the outermost file read, the
   input buffer associated to the location of the error (or the module name
   if boolean is true), and the error itself. *)

exception Error_in_file of string * (bool * string * loc) * exn

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
