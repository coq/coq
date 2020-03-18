(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* We register this handler for lower-level toplevel loading code *)
let _ = CErrors.register_handler (function
    | Symtable.Error e ->
      Some (Pp.str (Format.asprintf "%a" Symtable.report_error e))
    | _ ->
      None
  )

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
             add_dir  = Topdirs.dir_directory;
             ml_loop  = (fun () -> Toploop.loop ppf);
           })

(* Main coqtop initialization *)
let _ =
  drop_setup ();
  Coqtop.(start_coq coqtop_toplevel)
