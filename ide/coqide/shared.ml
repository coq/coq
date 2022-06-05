(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* overridden on Windows; see file coqide_WIN32.c.in *)
let cvt_pid = ref (fun pid -> pid)

let get_interrupt_fname pid =
  let x =
  Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "coqide_interrupt_%d" (!cvt_pid pid)) in
  Printf.eprintf "file is %s\n%!" x;
  x
