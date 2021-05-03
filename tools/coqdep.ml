(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The basic parts of coqdep are in [Coqdep_common]. *)
module CD = Coqdep_common

let (//) = Filename.concat

(* Exception to be raised by Envars *)
exception CoqlibError of string

let _ = CErrors.register_handler (function
    | CoqlibError msg -> Some (Pp.str msg)
    | _ -> None)

let coqdep () =
  Coqdep_common.init ();
  (* XXX: All the code below is just setting loadpaths, refactor to
     common coq.boot library *)
  (* Add current dir with empty logical path if not set by options above. *)
  (try ignore (CD.find_dir_logpath (Sys.getcwd()))
   with Not_found -> CD.add_norec_dir_import CD.add_known "." []);
  (* We don't setup any loadpath if the -boot is passed *)
  if not !CD.option_boot then begin
    Envars.set_coqlib ~fail:(fun msg -> raise (CoqlibError msg));
    let coqlib = Envars.coqlib () in
    let coq_plugins_dir = Filename.concat (Envars.coqcorelib ()) "plugins" in
    if not (Sys.file_exists coq_plugins_dir) then
      CErrors.user_err Pp.(str "coqdep: cannot find plugins directory for coqlib: " ++ str coqlib ++ fnl ());
    CD.add_rec_dir_import CD.add_coqlib_known (coqlib//"theories") ["Coq"];
    CD.add_rec_dir_import CD.add_coqlib_known (coq_plugins_dir) ["Coq"];
    let user = coqlib//"user-contrib" in
    if Sys.file_exists user then CD.add_rec_dir_no_import CD.add_coqlib_known user [];
    List.iter (fun s -> CD.add_rec_dir_no_import CD.add_coqlib_known s [])
      (Envars.xdg_dirs ~warn:(fun x -> CD.coqdep_warning "%s" x));
    List.iter (fun s -> CD.add_rec_dir_no_import CD.add_coqlib_known s []) Envars.coqpath;
  end;
  if !CD.option_sort then
    CD.sort ()
  else
    CD.coq_dependencies ()

let _ =
  try
    coqdep ()
  with exn ->
    Format.eprintf "*** Error: @[%a@]@\n%!" Pp.pp_with (CErrors.print exn);
    exit 1
