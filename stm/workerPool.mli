(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type worker_id = string

type 'a cpanel = {
  exit : unit -> unit; (* called by manager to exit instead of Thread.exit *)
  cancelled : unit -> bool; (* manager checks for a request of termination *)
  extra : 'a;                        (* extra stuff to pass to the manager *)
}

module type PoolModel = sig
  (* this shall come from a Spawn.* model *)
  type process
  val spawn : int -> worker_id * process * CThread.thread_ic * out_channel

  (* this defines the main loop of the manager *)
  type extra
  val manager :
    extra cpanel -> worker_id * process * CThread.thread_ic * out_channel -> unit
end

module Make(Model : PoolModel) : sig

  type pool
  
  val create : Model.extra -> size:int -> pool

  val is_empty : pool -> bool
  val n_workers : pool -> int

  (* cancel signal *)
  val cancel : worker_id -> pool -> unit
  val cancel_all : pool -> unit
  (* camcel signal + true removal, the pool is empty afterward *)
  val destroy : pool -> unit

  (* The worker should call this function *)
  val worker_handshake : CThread.thread_ic -> out_channel -> unit

end
