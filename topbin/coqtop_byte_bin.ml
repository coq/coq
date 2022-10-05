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

(* XXX: Remove this for Toploop.get_directive once we bump the OCaml
   version, unfortunately 4.09 still doesn't have it, and 4.13
   deprecated directive_table *)
let _get_directive name =
  let dt = Toploop.directive_table [@ocaml.warning "-3"] in
  Hashtbl.find_opt dt name

let load_module fmt name =
  if not ((Topdirs.load_file [@ocaml.warning "-3"]) fmt name) then
    CErrors.user_err Pp.(str ("Could not load plugin " ^ name))

let load_plugin fmt ps =
  match Mltop.PluginSpec.repr ps with
  | (Some file, _)  ->
    let file = file ^ ".cma" in
    load_module fmt file
  | (None, lib ) ->
    Topfind.load_deeply [lib]

let drop_setup () =
  let ppf = Format.std_formatter in
  Mltop.(set_top
           { load_plugin = load_plugin ppf
           ; load_module = load_module ppf
           ; add_dir  = Topdirs.dir_directory
           ; ml_loop  = (fun () -> Toploop.loop ppf)
           })

(* Main coqtop initialization *)
let _ =
  drop_setup ();
  Coqtop.(start_coq coqtop_toplevel)
