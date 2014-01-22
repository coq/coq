(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* To link this file, threads are needed *)

type chandescr = AnonPipe | Socket of string * int

(* Argument parsing should set these *)
val main_channel : chandescr option ref
val control_channel : chandescr option ref

(* Immediately after argument parsing one *must* call this *)
val init_channels : unit -> unit

(* Once initialized, these are the channels to talk with our master *)
val get_channels : unit -> in_channel * out_channel

(* In multi threaded environments on windows blocking calls do
   prevent context switch.  This seems a huge BUG, here a work around *)
val prepare_in_channel_for_thread_friendly_blocking_input : in_channel -> unit
val thread_friendly_blocking_input : in_channel -> string -> int -> int
