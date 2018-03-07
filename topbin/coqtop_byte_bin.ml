(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let drop_setup () =
  begin try
    (* Enable rectypes in the toplevel if it has the directive #rectypes *)
    begin match Hashtbl.find Toploop.directive_table "rectypes" with
      | Toploop.Directive_none f -> f ()
      | _ -> ()
    end
    with
    | Not_found -> ()
  end;
  let ppf = Format.std_formatter in
  Mltop.(set_top
           { load_obj = (fun f -> if not (Topdirs.load_file ppf f)
                          then CErrors.user_err Pp.(str ("Could not load plugin "^f))
                        );
             use_file = Topdirs.dir_use ppf;
             add_dir  = Topdirs.dir_directory;
             ml_loop  = (fun () -> Toploop.loop ppf);
           })

(* Main coqtop initialization *)
let _ =
  drop_setup ();
  Coqtop.(start_coq coqtop_toplevel)
