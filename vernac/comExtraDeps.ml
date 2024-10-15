(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open CErrors

let extra_deps = Summary.ref ~name:"extra_deps" ~stage:Summary.Stage.Synterp Id.Map.empty

let bind_extra_dep ?loc path id =
  match Id.Map.find_opt id !extra_deps with
  | Some (other,loc) ->
      user_err Pp.(str "Extra dependency " ++ Id.print id ++
        str " already bound to " ++ str other ++
        pr_opt (fun x -> str " at " ++ Loc.pr x) loc ++ str ".")
  | None -> extra_deps := Id.Map.add id (path,loc) !extra_deps

let declare_extra_dep ?loc ~from ~file id =
  let file_path = Loadpath.find_extra_dep_with_logical_path ?loc ~from ~file () in
  Option.iter (bind_extra_dep ?loc file_path) id

let query_extra_dep id = fst @@ Id.Map.find id !extra_deps
