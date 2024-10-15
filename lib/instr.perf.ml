(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let read_counter : unit -> (Int64.t, string) Result.t =
  let drop () = try Perf.drop () with Failure(_) -> () in
  try
    Perf.init (); at_exit drop;
    fun () -> try Ok(Perf.peek ()) with Failure(msg) -> Error(msg)
  with Failure(msg) ->
    fun () -> Error(msg)
