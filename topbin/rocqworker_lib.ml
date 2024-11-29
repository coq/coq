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
  Format.eprintf "Usage: coqworker.opt --kind=[compile|proof|query|tactic] $args@\ngot %s\n%!" s;
  exit 1

type kind =
  | Worker of { init : unit -> unit; loop : unit -> unit }
  | Compile

let start kind args = match kind with
  | Worker { init; loop } -> WorkerLoop.start ~init ~loop args
  | Compile -> Coqc.main args

let run = function
  | [] -> error "no argument" ()
  | kind :: argv ->
    let kind =
      match kind with
      | "--kind=compile" -> Compile
      | "--kind=proof" -> Worker { init = WProof.init_stdout; loop = WProof.main_loop }
      | "--kind=query" -> Worker { init = WQuery.init_stdout; loop = WQuery.main_loop }
      | "--kind=tactic" -> Worker { init = WTactic.init_stdout; loop = WTactic.main_loop }
      | s -> error s ()
    in
    start kind argv

let () = Rocqshim.run := run
