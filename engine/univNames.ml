(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Univ


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

(** Local universe names of polymorphic references *)

type universe_binders = Univ.Level.t Names.Id.Map.t

let empty_binders = Id.Map.empty

let universe_binders_table = Summary.ref GlobRef.Map.empty ~name:"universe binders"

let universe_binders_of_global ref : Id.t list =
  try
    let l = GlobRef.Map.find ref !universe_binders_table in l
  with Not_found -> []

let cache_ubinder (_,(ref,l)) =
  universe_binders_table := GlobRef.Map.add ref l !universe_binders_table

let subst_ubinder (subst,(ref,l as orig)) =
  let ref' = fst (Globnames.subst_global subst ref) in
  if ref == ref' then orig else ref', l

let name_universe lvl =
  (** Best-effort naming from the string representation of the level. This is
      completely hackish and should be solved in upper layers instead. *)
  Id.of_string_soft (Level.to_string lvl)

let discharge_ubinder (_,(ref,l)) =
  (** Expand polymorphic binders with the section context *)
  let info = Lib.section_segment_of_reference ref in
  let sec_inst = Array.to_list (Instance.to_array (info.Lib.abstr_subst)) in
  let map lvl = match Level.name lvl with
    | None -> (* Having Prop/Set/Var as section universes makes no sense *)
      assert false
    | Some na ->
      try
        let qid = Nametab.shortest_qualid_of_universe na in
        snd (Libnames.repr_qualid qid)
      with Not_found -> name_universe lvl
  in
  let l = List.map map sec_inst @ l in
  Some (ref, l)

let ubinder_obj : GlobRef.t * Id.t list -> Libobject.obj =
  let open Libobject in
  declare_object { (default_object "universe binder") with
    cache_function = cache_ubinder;
    load_function = (fun _ x -> cache_ubinder x);
    classify_function = (fun x -> Substitute x);
    subst_function = subst_ubinder;
    discharge_function = discharge_ubinder;
    rebuild_function = (fun x -> x); }

let register_universe_binders ref ubinders =
  (** TODO: change the API to register a [Name.t list] instead. This is the last
      part of the code that depends on the internal representation of names in
      abstract contexts, but removing it requires quite a rework of the
      callers. *)
  let univs = AUContext.instance (Environ.universes_of_global (Global.env()) ref) in
  let revmap = Id.Map.fold (fun id lvl accu -> LMap.add lvl id accu) ubinders LMap.empty in
  let map lvl =
    try LMap.find lvl revmap
    with Not_found -> name_universe lvl
  in
  let ubinders = Array.map_to_list map (Instance.to_array univs) in
  if not (List.is_empty ubinders) then Lib.add_anonymous_leaf (ubinder_obj (ref, ubinders))

type univ_name_list = Names.lname list

let universe_binders_with_opt_names ref names =
  let orig = universe_binders_of_global ref in
  let udecl = match names with
  | None -> orig
  | Some udecl ->
    try
      List.map2 (fun orig {CAst.v = na} ->
          match na with
          | Anonymous -> orig
          | Name id -> id) orig udecl
    with Invalid_argument _ ->
      let len = List.length orig in
      CErrors.user_err ~hdr:"universe_binders_with_opt_names"
        Pp.(str "Universe instance should have length " ++ int len)
  in
  let fold i acc na = Names.Id.Map.add na (Level.var i) acc in
  List.fold_left_i fold 0 empty_binders udecl
