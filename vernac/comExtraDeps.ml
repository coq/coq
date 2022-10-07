(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open CErrors

let warn_file_found_multiple_times =
  CWarnings.create ~name:"ambiguous-extra-dep" ~category:"filesystem"
    (fun (file,from,other,extra) ->
      Pp.(str "File " ++ str file ++ str " found twice in " ++
      DirPath.print from ++ str":" ++ spc () ++ str other ++ str " (selected)," ++
      spc() ++ str extra ++ str ".") )

let rec first_path_containing ?loc from file acc = function
  | [] ->
      begin match acc with
      | Some x -> x
      | None ->
          user_err Pp.(str "File " ++ str file ++ str " not found in " ++
            DirPath.print from ++ str".")
     end
  | x :: xs ->
      let abspath = x ^ "/" ^ file in
      if Sys.file_exists abspath then begin
        match acc with
        | None -> first_path_containing ?loc from file (Some abspath) xs
        | Some other ->
            warn_file_found_multiple_times ?loc (file,from,other,abspath);
            first_path_containing ?loc from file acc xs
      end else
        first_path_containing ?loc from file acc xs

let extra_deps = Summary.ref ~name:"extra_deps" Id.Map.empty

let bind_extra_dep ?loc path id =
  match Id.Map.find_opt id !extra_deps with
  | Some (other,loc) ->
      user_err Pp.(str "Extra dependency " ++ Id.print id ++
        str " already bound to " ++ str other ++
        pr_opt (fun x -> str " at " ++ Loc.pr x) loc ++ str ".")
  | None -> extra_deps := Id.Map.add id (path,loc) !extra_deps

let declare_extra_dep ?loc ~from ~file id =
  match Loadpath.find_with_logical_path from with
  | _ :: _ as paths ->
    let paths = List.map Loadpath.physical paths in
    let file_path = first_path_containing ?loc from file None paths in
    Option.iter (bind_extra_dep ?loc file_path) id
  | [] -> user_err Pp.(str "No LoadPath found for " ++ DirPath.print from ++ str".")

let query_extra_dep id = fst @@ Id.Map.find id !extra_deps
