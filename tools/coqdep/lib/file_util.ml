(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let re_delim = Str.regexp (if Sys.win32 then "[/\\]+" else "/+" )

let to_relative_path : string -> string = fun full_path ->
  if Filename.is_relative full_path then full_path else
  let cwd = Str.split_delim re_delim (Sys.getcwd ()) in
  let path = Str.split_delim re_delim full_path in
  let rec remove_common_prefix l1 l2 =
    match (l1, l2) with
    | (x1 :: l1, x2 :: l2) when x1 = x2 -> remove_common_prefix l1 l2
    | (_       , _       )              -> (l1, String.concat "/" l2)
  in
  let (cwd, path) = remove_common_prefix cwd path in
  let add_parent path _ = Filename.concat Filename.parent_dir_name path in
  List.fold_left add_parent path cwd

let normalize_path : string -> string = fun path ->
  let path = Str.split_delim re_delim path in
  let rec normalize acc path =
    match (path, acc) with
    | ([]          , _          ) -> List.rev acc
    | ("."  :: path, _          ) -> normalize acc path
    | (".." :: path, []         ) -> normalize (".." :: []) path
    | (".." :: path, ".." :: _  ) -> normalize (".." :: acc) path
    | (".." :: path, _    :: acc) -> normalize acc path
    | (dir  :: path, _          ) -> normalize (dir :: acc) path
  in
  match normalize [] path with
  | []   -> "."
  | path -> String.concat "/" path
