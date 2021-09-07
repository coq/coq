(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Monomorphic universes need to survive sections. *)

let name_instance inst =
  let map lvl = match Univ.Level.name lvl with
    | None -> (* Having Prop/Set/Var as section universes makes no sense *)
      assert false
    | Some na ->
      try
        let qid = Nametab.shortest_qualid_of_universe Names.Id.Map.empty na in
        Names.Name (Libnames.qualid_basename qid)
      with Not_found ->
        (* Best-effort naming from the string representation of the level.
           See univNames.ml for a similar hack. *)
        Names.Name (Names.Id.of_string_soft (Univ.Level.to_string lvl))
  in
  Array.map map (Univ.Instance.to_array inst)

let declare_universe_context ~poly ctx =
  if poly then
    let uctx = Univ.ContextSet.to_context name_instance ctx in
    Global.push_section_context uctx
  else
    Global.push_context_set ~strict:true ctx
