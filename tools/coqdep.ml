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

let coqdep () =
  Coqdep_common.init ();
  (* XXX: All the code below is just setting loadpaths, refactor to
     common coq.boot library *)
  (* Add current dir with empty logical path if not set by options above. *)
  (try ignore (CD.find_dir_logpath (Sys.getcwd()))
   with Not_found -> CD.add_norec_dir_import CD.add_known "." []);
  (* We don't setup any loadpath if the -boot is passed *)
  if not !CD.option_boot then begin
    let env = Boot.Env.init () in
    let stdlib = Boot.Env.(stdlib env |> Path.to_string) in
    let plugins = Boot.Env.(plugins env |> Path.to_string) in
    let user_contrib = Boot.Env.(user_contrib env |> Path.to_string) in
    CD.add_rec_dir_import CD.add_coqlib_known stdlib ["Coq"];
    CD.add_rec_dir_import CD.add_coqlib_known plugins ["Coq"];
    if Sys.file_exists user_contrib
    then CD.add_rec_dir_no_import CD.add_coqlib_known user_contrib [];
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
