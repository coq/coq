(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module W = AsyncTaskQueue.MakeWorker(Stm.ProofTask)

let () = Coqtop.toploop_init := (fun args ->
        Flags.make_silent true;
        W.init_stdout ();
        CoqworkmgrApi.init !Flags.async_proofs_worker_priority;
        args)

let () = Coqtop.toploop_run := W.main_loop

