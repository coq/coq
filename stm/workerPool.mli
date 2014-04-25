(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Make(Worker : sig
  type process
  val spawn :
      ?prefer_sock:bool -> ?env:string array -> string -> string array ->
      process * in_channel * out_channel
end) : sig

type worker_id = int
type spawn =
  args:string array -> env:string array -> unit ->
    in_channel * out_channel * Worker.process

val init :
  size:int -> manager:(cancel:bool ref -> worker_id -> spawn -> unit) -> unit
val is_empty : unit -> bool
val n_workers : unit -> int
val cancel : worker_id -> unit

(* The worker should call this function *)
val worker_handshake : in_channel -> out_channel -> unit

end
