(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* overridden on Windows; see file shared_WIN32.c.in *)
let cvt_pid = ref (fun pid -> pid)

let get_interrupt_fname pid =
  Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "rocqide_interrupt_%d" (!cvt_pid pid))
