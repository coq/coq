(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Checking opaque proofs in forked worker processes.

    The check of an opaque body is handed to [defer]. By default it is
    run immediately. With [-j N] for [N > 1], it is queued instead, and
    queued checks are run in batches by worker processes created with
    [Unix.fork]: up to [N-1] while the main process carries on with the
    rest of the libraries, then up to [N] while it waits for them in
    [finish], where it checks nothing itself. A worker inherits a
    copy-on-write copy of the whole heap, so it runs the queued closures
    as they are: nothing is marshalled and nothing is shared afterwards.

    A batch is checked only if its worker exits with code 0.

    A worker lives for at most a time budget (see [set_budget]): the
    longer a worker lives, the more of the heap it shares with the main
    process it has copied. Once the budget has passed, and the worker
    has completed at least one check, it stops after the check it is in
    and reports how many checks of its batch, the first ones in order, it
    completed. The main process queues the others again, at the front.
    So every check is run exactly once, by a process that ends
    successfully, whichever way the work is cut into batches. *)

val set_jobs : profiling:bool -> int -> unit
(** [set_jobs ~profiling n] allows [n] processes to check at the same
    time: the main one and [n-1] workers while the libraries are
    checked, then [n] workers. With [n <= 1], and, with a warning, when
    profiling or when [Unix.fork] is not available, every check runs at
    once in the main process. *)

val default_budget : float
(** Seconds. *)

val set_budget : float -> unit
(** [set_budget t] makes workers stop after [t] seconds of wall time,
    counted from their creation, at the next end of a check, but never
    before one check is completed. [t = 0.] makes a worker complete a
    single check. @raise Invalid_argument if [t] is negative or NaN. *)

exception CheckError of Names.Constant.t * exn
(** The deferred check of the body of a constant raised an exception.
    Only raised when checks are deferred, i.e. not with [-j 1]. *)

val set_error_printer : (exn -> unit) -> unit
(** How a worker reports the [CheckError] it caught, before it exits. *)

val defer : Names.Constant.t -> (unit -> unit) -> unit
(** [defer kn check] runs or queues the check of the opaque body of
    [kn]. [check] must not depend on anything that happens after it
    is queued, nor have effects that anything else depends on. *)

val finish : unit -> unit
(** Deal everything that is still queued to workers and wait for all of
    them. Raises [WorkerFailed] if a worker did not exit with code 0, or
    did not report between 1 and [size] completed checks. *)

val abort : unit -> unit
(** Kill all workers, wait for them, and drop the queued checks. *)

type batch = {
  size : int;
  first : Names.Constant.t;
  last : Names.Constant.t;
}

exception WorkerFailed of int * Unix.process_status * batch
(** A worker (pid, status) failed while checking the given batch. The
    other workers have been killed. *)

val pr_batch : batch -> Pp.t

val signal_name : int -> string

(** {2 For tests only} *)

val default_report_writer : Unix.file_descr -> int -> unit
(** What a worker does to report the number of checks it completed. *)

val set_report_writer : (Unix.file_descr -> int -> unit) -> unit
(** [set_report_writer f] replaces what a worker does to report the number
    of checks it completed, given the descriptor to write to. *)
