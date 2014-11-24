(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type worker_id = string
type 'a spawn =
  args:string array -> env:string array -> unit -> in_channel * out_channel * 'a
type active
type parking

(* this shall come from a Spawn.* model *)
module type WorkerModel = sig
  type process
  val spawn :
    ?prefer_sock:bool -> ?env:string array -> string -> string array ->
      process * in_channel * out_channel
end

(* this defines the main loop of the manager *)
module type ManagerModel = sig
  type process
  type extra (* extra stuff to pass to the manager *)
  val manager :
    extra -> cancel:bool ref -> die:bool ref -> worker_id -> process spawn ->
      unit
  val naming : int -> worker_id
end

module Make(Worker : WorkerModel)
           (Manager : ManagerModel with type process = Worker.process) : sig

  type 'a pool
  
  val create_active : Manager.extra -> int -> active pool
  val create_parking :  unit -> parking pool

  val is_empty : 'a pool -> bool
  val n_workers : 'a pool -> int

  (* cancel signal *)
  val cancel : 'a pool -> worker_id -> unit
  val cancel_all : 'a pool -> unit
  (* die signal + true removal, the pool is empty afterward *)
  val destroy : 'a pool -> unit

  val move : active pool -> parking pool -> worker_id -> unit
  
  (* The worker should call this function *)
  val worker_handshake : in_channel -> out_channel -> unit

end
