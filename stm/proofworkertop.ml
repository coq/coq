(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module W = AsyncTaskQueue.MakeWorker(Stm.ProofTask) ()

let () = Coqtop.toploop_init := WorkerLoop.loop W.init_stdout

let () = Coqtop.toploop_run := (fun _ ~state:_ -> W.main_loop ())

