(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module WProof = AsyncTaskQueue.MakeWorker(Stm.ProofTask) ()
module WQuery = AsyncTaskQueue.MakeWorker(Stm.QueryTask) ()
module WTactic = AsyncTaskQueue.MakeWorker(Partac.TacTask) ()

let error s () =
  Format.eprintf "Usage: coqworker.opt --kind=[proof|query|tactic] $args@\ngot %s\n%!" s;
  exit 1

let () =
  if Array.length Sys.argv < 2
  then error "no argument" ()
  else
    let argv = List.tl (Array.to_list Sys.argv) in
    let kind = List.hd argv in
    let argv = List.tl argv in
    let init, loop =
      match kind with
      | "--kind=proof" -> WProof.init_stdout, WProof.main_loop
      | "--kind=query" -> WQuery.init_stdout, WQuery.main_loop
      | "--kind=tactic" -> WTactic.init_stdout, WTactic.main_loop
      | s -> error s ()
    in
    WorkerLoop.start ~init ~loop argv
