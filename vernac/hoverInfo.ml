(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module LM = Map.Make(Int)
module SM = Map.Make(Stateid)

type hover = {
    docstring : Pp.t;
    types : Pp.t option;
    def_loc : Loc.t; (* shifted *)
    id : Stateid.t;
}

type t = {
  hover_info_by_id: hover SM.t;
  hover_info_by_loc: hover LM.t;
}

let empty () = {hover_info_by_id=SM.empty; hover_info_by_loc=LM.empty}

let query info (loc : Loc.t) =
  LM.find_opt loc.ep info.hover_info_by_loc

let add_docstring info ?types id def_loc ~docstring =
  let {hover_info_by_id; hover_info_by_loc} = info in
  let hover = {docstring; types; def_loc; id} in
  let hover_info_by_id = SM.add id hover hover_info_by_id in
  let hover_info_by_loc = LM.add def_loc.ep hover hover_info_by_loc in
  {hover_info_by_id; hover_info_by_loc}

let prune_one info id =
  let {hover_info_by_id; hover_info_by_loc} = info in
  match SM.find_opt id hover_info_by_id with
  | None -> info
  | Some hover ->
    let hover_info_by_id = SM.remove id hover_info_by_id in
    let hover_info_by_loc = LM.remove hover.def_loc.ep hover_info_by_loc in
    {hover_info_by_loc; hover_info_by_id}

let prune info id_list = List.fold_left prune_one info id_list

let shift info ~from ~amount =
  let {hover_info_by_id; hover_info_by_loc} = info in
  let hover_infos = LM.filter (fun loc _ -> loc >= from) hover_info_by_loc in
  let stateids = List.map (fun (_, x) -> x.id) @@ LM.bindings hover_infos in
  let info = prune info stateids in
  let shift_and_add _ hover info =
    let def_loc = Loc.shift_loc amount amount hover.def_loc in
    let hover = {hover with def_loc} in
    let hover_info_by_loc = LM.add def_loc.ep hover info.hover_info_by_loc in
    let hover_info_by_id = SM.add hover.id hover info.hover_info_by_id in
    {hover_info_by_id; hover_info_by_loc}
  in
  LM.fold shift_and_add hover_infos info


let update_current_info = ref (fun ~uri ~sentence_id _ -> ())

let set_update_current_info f = update_current_info := f

let update_current_info ~uri ~sentence_id f = !update_current_info ~uri ~sentence_id f
