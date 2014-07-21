(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let () = Coqtop.toploop_init := (fun args ->
        Flags.make_silent true;
        Stm.tacslave_init_stdout ();
        args)

let () = Coqtop.toploop_run := Stm.tacslave_main_loop

