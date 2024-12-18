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
  Format.eprintf "Usage: rocqworker --kind=[compile|repl|proof|query|tactic] $args@\ngot %s\n%!" s;
  exit 1

type kind =
  | Worker of { init : unit -> unit; loop : unit -> unit }
  | Compile
  | Repl

let start kind args = match kind with
  | Worker { init; loop } -> WorkerLoop.start ~init ~loop args
  | Compile -> Coqc.main args
  | Repl -> Coqtop.(start_coq coqtop_toplevel args)

let () =
  if Array.length Sys.argv < 2
  then error "no argument" ()
  else
    let argv = List.tl (Array.to_list Sys.argv) in
    let kind = List.hd argv in
    let argv = List.tl argv in
    let kind =
      match kind with
      | "--kind=compile" -> Compile
      | "--kind=repl" -> Repl
      | "--kind=proof" -> Worker { init = WProof.init_stdout; loop = WProof.main_loop }
      | "--kind=query" -> Worker { init = WQuery.init_stdout; loop = WQuery.main_loop }
      | "--kind=tactic" -> Worker { init = WTactic.init_stdout; loop = WTactic.main_loop }
      | s -> error s ()
    in
    start kind argv
