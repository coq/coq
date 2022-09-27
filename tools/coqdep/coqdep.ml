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
open Coqdeplib

let coqdep () =
  let open Common in

  (* Initialize coqdep, add files to dependency computation *)
  if Array.length Sys.argv < 2 then Args.usage ();
  let args =
    Sys.argv
    |> Array.to_list
    |> List.tl
    |> Args.parse (Args.make ())
  in
  let v_files = args.Args.files in
  (* We are in makefile hack mode *)
  let make_separator_hack = true in
  let st = init ~make_separator_hack args in
  let lst = Common.State.loadpath st in
  List.iter treat_file_command_line v_files;

  (* XXX: All the code below is just setting loadpaths, refactor to
     Common coq.boot library *)
  (* Add current dir with empty logical path if not set by options above. *)
  (try ignore (Loadpath.find_dir_logpath (Sys.getcwd()))
   with Not_found -> Loadpath.add_current_dir lst ".");
  (* We don't setup any loadpath if the -boot is passed *)
  if not args.Args.boot then begin
    let env = Boot.Env.init () in
    let stdlib = Boot.Env.(stdlib env |> Path.to_string) in
    let plugins = Boot.Env.(plugins env |> Path.to_string) in
    let user_contrib = Boot.Env.(user_contrib env |> Path.to_string) in
    Loadpath.add_loadpath ~implicit:true lst stdlib ["Coq"];
    Loadpath.add_loadpath ~implicit:true lst plugins ["Coq"];
    if Sys.file_exists user_contrib
    then Loadpath.add_loadpath ~implicit:false lst user_contrib [];
    List.iter (fun s -> Loadpath.add_loadpath ~implicit:false lst s [])
      (Envars.xdg_dirs ~warn:(fun x -> Warning.give "%s" x));
    List.iter (fun s -> Loadpath.add_loadpath ~implicit:false lst s []) Envars.coqpath;
  end;
  if args.Args.sort then
    sort st
  else
    compute_deps st |> List.iter (Makefile.print_dep Format.std_formatter)

let () =
  try
    coqdep ()
  with exn ->
    Format.eprintf "*** Error: @[%a@]@\n%!" Pp.pp_with (CErrors.print exn);
    exit 1
