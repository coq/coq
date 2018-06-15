(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module implements spawning/killing managed processes with a
 * synchronous or asynchronous comunication channel that works with
 * threads or with a glib like main loop model.
 *
 * This module requires no threads and no main loop model.  It takes care
 * of using the fastest communication channel given the underlying OS and
 * the requested kind of communication.
 *
 * The spawned process must use the Spawned module to init its communication
 * channels.
 *)

(* This is the control panel for managed processes *)
module type Control = sig
  type handle

  val kill : handle -> unit
  val wait : handle -> Unix.process_status
  val unixpid : handle -> int
  
  (* What is used in debug messages *)
  val uid : handle -> string

  val is_alive : handle -> bool
end

(* Abstraction to work with both threads and main loop models *)
module type MainLoopModel = sig
  type async_chan
  type condition
  type watch_id

  val add_watch : callback:(condition list -> bool) -> async_chan -> watch_id
  val remove_watch : watch_id -> unit
  val read_all : async_chan -> string
  val async_chan_of_file : Unix.file_descr -> async_chan
  val async_chan_of_socket : Unix.file_descr -> async_chan
end

(* spawn a process and read its output asynchronously *)
module Async(ML : MainLoopModel) : sig
  type process

  (* If the returned value is false the callback is never called again and
   * the process is killed *)
  type callback = ML.condition list -> read_all:(unit -> string) -> bool
  
  val spawn :
    ?prefer_sock:bool -> ?env:string array -> string -> string array ->
      callback -> process * out_channel

  include Control with type handle = process
end

(* spawn a process and read its output synchronously *)
module Sync () : sig
  type process
  
  val spawn :
    ?prefer_sock:bool -> ?env:string array -> string -> string array ->
      process * in_channel * out_channel

  include Control with type handle = process
end

(* This is exported to separate the Spawned module, that for simplicity assumes
 * Threads so it is in a separate file *)
type req = ReqDie | Hello of int * int
val proto_version : int
