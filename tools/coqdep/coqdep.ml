(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The basic parts of coqdep are in [Common]. *)

let coqdep () =
  let open Coqdeplib.Common in

  (* Initialize coqdep, add files to dependency computation *)
  if Array.length Sys.argv < 2 then usage ();
  let v_files = init (List.tl (Array.to_list Sys.argv)) in
  List.iter treat_file_command_line v_files;

  (* XXX: All the code below is just setting loadpaths, refactor to
     Common coq.boot library *)
  (* Add current dir with empty logical path if not set by options above. *)
  (try ignore (find_dir_logpath (Sys.getcwd()))
   with Not_found -> add_norec_dir_import add_known "." []);
  (* We don't setup any loadpath if the -boot is passed *)
  if not !option_boot then begin
    let env = Boot.Env.init () in
    let stdlib = Boot.Env.(stdlib env |> Path.to_string) in
    let plugins = Boot.Env.(plugins env |> Path.to_string) in
    let user_contrib = Boot.Env.(user_contrib env |> Path.to_string) in
    add_rec_dir_import add_coqlib_known stdlib ["Coq"];
    add_rec_dir_import add_coqlib_known plugins ["Coq"];
    if Sys.file_exists user_contrib
    then add_rec_dir_no_import add_coqlib_known user_contrib [];
    List.iter (fun s -> add_rec_dir_no_import add_coqlib_known s [])
      (Envars.xdg_dirs ~warn:(fun x -> coqdep_warning "%s" x));
    List.iter (fun s -> add_rec_dir_no_import add_coqlib_known s []) Envars.coqpath;
  end;
  if !option_sort then
    sort ()
  else
    coq_dependencies ()

let _ =
  try
    coqdep ()
  with exn ->
    Format.eprintf "*** Error: @[%a@]@\n%!" Pp.pp_with (CErrors.print exn);
    exit 1
