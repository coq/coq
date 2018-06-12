(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ
open Globnames
open Nametab


let qualid_of_level l =
  match Level.name l with
  | Some (d, n as na)  ->
    begin
    try Nametab.shortest_qualid_of_universe na
    with Not_found ->
      let name = Id.of_string_soft (string_of_int n) in
      Libnames.make_qualid d name
    end
  | None ->
    Libnames.qualid_of_ident @@ Id.of_string_soft (Level.to_string l)

let pr_with_global_universes l = Libnames.pr_qualid (qualid_of_level l)

(** Global universe information outside the kernel, to handle
    polymorphic universe names in sections that have to be discharged. *)

let universe_map = (Summary.ref UnivIdMap.empty ~name:"global universe info" : bool Nametab.UnivIdMap.t ref)

let add_global_universe u p =
  match Level.name u with
  | Some n -> universe_map := Nametab.UnivIdMap.add n p !universe_map
  | None -> ()

let is_polymorphic l =
  match Level.name l with
  | Some n ->
     (try Nametab.UnivIdMap.find n !universe_map
      with Not_found -> false)
  | None -> false

(** Local universe names of polymorphic references *)

type universe_binders = Univ.Level.t Names.Id.Map.t

let empty_binders = Id.Map.empty

let universe_binders_table = Summary.ref Refmap.empty ~name:"universe binders"

let universe_binders_of_global ref : universe_binders =
  try
    let l = Refmap.find ref !universe_binders_table in l
  with Not_found -> Names.Id.Map.empty

let cache_ubinder (_,(ref,l)) =
  universe_binders_table := Refmap.add ref l !universe_binders_table

let subst_ubinder (subst,(ref,l as orig)) =
  let ref' = fst (Globnames.subst_global subst ref) in
  if ref == ref' then orig else ref', l

let discharge_ubinder (_,(ref,l)) =
  Some (Lib.discharge_global ref, l)

let ubinder_obj : GlobRef.t * universe_binders -> Libobject.obj =
  let open Libobject in
  declare_object { (default_object "universe binder") with
    cache_function = cache_ubinder;
    load_function = (fun _ x -> cache_ubinder x);
    classify_function = (fun x -> Substitute x);
    subst_function = subst_ubinder;
    discharge_function = discharge_ubinder;
    rebuild_function = (fun x -> x); }

let register_universe_binders ref ubinders =
  (* Add the polymorphic (section) universes *)
  let ubinders = UnivIdMap.fold (fun lvl poly ubinders ->
    let qid = Nametab.shortest_qualid_of_universe lvl in
    let level = Level.make (fst lvl) (snd lvl) in
    if poly then Id.Map.add (snd (Libnames.repr_qualid qid)) level ubinders
    else ubinders)
    !universe_map ubinders
  in
  if not (Id.Map.is_empty ubinders)
  then Lib.add_anonymous_leaf (ubinder_obj (ref,ubinders))

type univ_name_list = Names.lname list

let universe_binders_with_opt_names ref levels = function
  | None -> universe_binders_of_global ref
  | Some udecl ->
    if Int.equal(List.length levels) (List.length udecl)
    then
      List.fold_left2 (fun acc { CAst.v = na} lvl -> match na with
          | Anonymous -> acc
          | Name na -> Names.Id.Map.add na lvl acc)
        empty_binders udecl levels
    else
      CErrors.user_err ~hdr:"universe_binders_with_opt_names"
        Pp.(str "Universe instance should have length " ++ int (List.length levels))
