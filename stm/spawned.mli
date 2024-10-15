(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* To link this file, threads are needed *)

type chandescr = AnonPipe | Socket of string * int * int

(* Argument parsing should set these *)
val main_channel : chandescr option ref
val control_channel : chandescr option ref

(* Immediately after argument parsing one *must* call this *)
val init_channels : unit -> unit

(* Once initialized, these are the channels to talk with our master *)
val get_channels : unit -> CThread.thread_ic * out_channel

(** {6 Name of current process.} *)
val process_id : unit -> string
