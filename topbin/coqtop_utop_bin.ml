(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let utop_main () =
  Array.set Sys.argv 1 "-w";
  Array.set Sys.argv 2 "-3";
  UTop_main.main ()

let utop_drop_setup () =
  (* TODO: Enable rectypes in utop + add libraries using topfind *)
  let ppf = Format.std_formatter in
  Mltop.(set_top
           { load_obj = (fun f -> if not (Topdirs.load_file ppf f)
                          then CErrors.user_err Pp.(str ("Could not load plugin "^f))
                        );
             add_dir  = Topdirs.dir_directory;
             ml_loop  = utop_main;
           })

(* We could maybe pre-use the Coq stuff here, however not sure the
   initialization can take calling UTop_main later. *)
(* ignore (Toploop.use_silently Format.err_formatter fn : bool) *)

(* Main coqtop initialization *)
let _ =
  utop_drop_setup ();
  Coqtop.(start_coq coqtop_toplevel)
