(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Pp
open Names
open Libnames
open Globnames

type object_prefix = {
  obj_dir : DirPath.t;
  obj_mp  : ModPath.t;
}

let eq_op op1 op2 =
  DirPath.equal op1.obj_dir op2.obj_dir &&
  ModPath.equal op1.obj_mp  op2.obj_mp

(* to this type are mapped DirPath.t's in the nametab *)
module GlobDirRef = struct
  type t =
    | DirOpenModule of object_prefix
    | DirOpenModtype of object_prefix
    | DirOpenSection of object_prefix
    | DirModule of object_prefix

  let equal r1 r2 = match r1, r2 with
    | DirOpenModule op1, DirOpenModule op2 -> eq_op op1 op2
    | DirOpenModtype op1, DirOpenModtype op2 -> eq_op op1 op2
    | DirOpenSection op1, DirOpenSection op2 -> eq_op op1 op2
    | DirModule op1, DirModule op2 -> eq_op op1 op2
    | _ -> false

end

exception GlobalizationError of qualid

let error_global_not_found ~info qid =
  let info = Option.cata (Loc.add_loc info) info qid.CAst.loc in
  Exninfo.iraise (GlobalizationError qid, info)

(* The visibility can be registered either
   - for all suffixes not shorter then a given int - when the object
     is loaded inside a module
   or
   - for a precise suffix, when the module containing (the module
     containing ...) the object is open (imported)
*)
type visibility = Until of int | Exactly of int

let map_visibility f = function
  | Until i -> Until (f i)
  | Exactly i -> Exactly (f i)

(* Data structure for nametabs *******************************************)


(* This module type will be instantiated by [full_path] of [DirPath.t] *)
(* The [repr] function is assumed to return the reversed list of idents. *)
module type UserName = sig
  type t
  val equal : t -> t -> bool
  val to_string : t -> string
  val repr : t -> Id.t * module_ident list
end

module type EqualityType =
sig
  type t
  val equal : t -> t -> bool
end

(* A ['a t] is a map from [user_name] to ['a], with possible lookup by
   partially qualified names of type [qualid]. The mapping of
   partially qualified names to ['a] is determined by the [visibility]
   parameter of [push].

   The [shortest_qualid] function given a user_name Coq.A.B.x, tries
   to find the shortest among x, B.x, A.B.x and Coq.A.B.x that denotes
   the same object.
*)
module type NAMETREE = sig
  type elt
  type t
  type user_name

  val empty : t
  val push : visibility -> user_name -> elt -> t -> t
  val locate : qualid -> t -> elt
  val find : user_name -> t -> elt
  val exists : user_name -> t -> bool
  val user_name : qualid -> t -> user_name
  val shortest_qualid_gen : ?loc:Loc.t -> (Id.t -> bool) -> user_name -> t -> qualid
  val shortest_qualid : ?loc:Loc.t -> Id.Set.t -> user_name -> t -> qualid
  val find_prefixes : qualid -> t -> elt list

  (** Matches a prefix of [qualid], useful for completion *)
  val match_prefixes : qualid -> t -> elt list
end

module Make (U : UserName) (E : EqualityType) : NAMETREE
  with type user_name = U.t and type elt = E.t =
struct
  type elt = E.t

  (* A name became inaccessible, even with absolute qualification.
     Example:
     Module F (X : S). Module X.
     The argument X of the functor F is masked by the inner module X.
   *)
  let warn_masking_absolute =
    CWarnings.create ~name:"masking-absolute-name" ~category:"deprecated"
      (fun n -> str ("Trying to mask the absolute name \"" ^ U.to_string n ^ "\"!"))

  type user_name = U.t

  type path_status =
      Nothing
    | Relative of user_name * elt
    | Absolute of user_name * elt

  (* Dictionaries of short names *)
  type nametree =
      { path : path_status;
        map : nametree ModIdmap.t }

  let mktree p m = { path=p; map=m }
  let empty_tree = mktree Nothing ModIdmap.empty

  type t = nametree Id.Map.t

  let empty = Id.Map.empty

  (* [push_until] is used to register [Until vis] visibility and
     [push_exactly] to [Exactly vis] and [push_tree] chooses the right one*)

  let rec push_until uname o level tree = function
    | modid :: path ->
        let modify _ mc = push_until uname o (level-1) mc path in
        let map =
          try ModIdmap.modify modid modify tree.map
          with Not_found ->
            let ptab = modify () empty_tree in
            ModIdmap.add modid ptab tree.map
        in
        let this =
          if level <= 0 then
            match tree.path with
              | Absolute (n,_) ->
                  (* This is an absolute name, we must keep it
                     otherwise it may become unaccessible forever *)
                warn_masking_absolute n; tree.path
              | Nothing
              | Relative _ -> Relative (uname,o)
          else tree.path
        in
        mktree this map
    | [] ->
        match tree.path with
          | Absolute (uname',o') ->
              if E.equal o' o then begin
                assert (U.equal uname uname');
                tree
                  (* we are putting the same thing for the second time :) *)
              end
              else
                (* This is an absolute name, we must keep it otherwise it may
                   become unaccessible forever *)
                (* But ours is also absolute! This is an error! *)
                user_err Pp.(str @@ "Cannot mask the absolute name \""
                                   ^ U.to_string uname' ^ "\"!")
          | Nothing
          | Relative _ -> mktree (Absolute (uname,o)) tree.map

let rec push_exactly uname o level tree = function
| [] ->
  anomaly (Pp.str "Prefix longer than path! Impossible!")
| modid :: path ->
  if Int.equal level 0 then
    let this =
      match tree.path with
        | Absolute (n,_) ->
            (* This is an absolute name, we must keep it
                otherwise it may become unaccessible forever *)
            warn_masking_absolute n; tree.path
        | Nothing
        | Relative _ -> Relative (uname,o)
    in
    mktree this tree.map
  else (* not right level *)
    let modify _ mc = push_exactly uname o (level-1) mc path in
    let map =
      try ModIdmap.modify modid modify tree.map
      with Not_found ->
        let ptab = modify () empty_tree in
        ModIdmap.add modid ptab tree.map
    in
    mktree tree.path map


let push visibility uname o tab =
  let id,dir = U.repr uname in
  let modify _ ptab = match visibility with
    | Until i -> push_until uname o (i-1) ptab dir
    | Exactly i -> push_exactly uname o (i-1) ptab dir
  in
  try Id.Map.modify id modify tab
  with Not_found ->
    let ptab = modify () empty_tree in
    Id.Map.add id ptab tab


let rec search tree = function
  | modid :: path -> search (ModIdmap.find modid tree.map) path
  | [] -> tree.path

let find_node qid tab =
  let (dir,id) = repr_qualid qid in
    search (Id.Map.find id tab) (DirPath.repr dir)

let locate qid tab =
  let o = match find_node qid tab with
    | Absolute (uname,o) | Relative (uname,o) -> o
    | Nothing -> raise Not_found
  in
    o

let user_name qid tab =
  let uname = match find_node qid tab with
    | Absolute (uname,o) | Relative (uname,o) -> uname
    | Nothing -> raise Not_found
  in
    uname

let find uname tab =
  let id,l = U.repr uname in
    match search (Id.Map.find id tab) l with
        Absolute (_,o) -> o
      | _ -> raise Not_found

let exists uname tab =
  try
    let _ = find uname tab in
      true
  with
      Not_found -> false

let shortest_qualid_gen ?loc hidden uname tab =
  let id,dir = U.repr uname in
  let hidden = hidden id in
  let rec find_uname pos dir tree =
    let is_empty = match pos with [] -> true | _ -> false in
    match tree.path with
    | Absolute (u,_) | Relative (u,_)
          when U.equal u uname && not (is_empty && hidden) -> List.rev pos
    | _ ->
        match dir with
            [] -> raise Not_found
          | id::dir -> find_uname (id::pos) dir (ModIdmap.find id tree.map)
  in
  let ptab = Id.Map.find id tab in
  let found_dir = find_uname [] dir ptab in
    make_qualid ?loc (DirPath.make found_dir) id

let shortest_qualid ?loc ctx uname tab =
  shortest_qualid_gen ?loc (fun id -> Id.Set.mem id ctx) uname tab

let push_node node l =
  match node with
  | Absolute (_,o) | Relative (_,o) when not (List.mem_f E.equal o l) -> o::l
  | _ -> l

let rec flatten_idmap tab l =
  let f _ tree l = flatten_idmap tree.map (push_node tree.path l) in
  ModIdmap.fold f tab l

let rec search_prefixes tree = function
  | modid :: path -> search_prefixes (ModIdmap.find modid tree.map) path
  | [] -> List.rev (flatten_idmap tree.map (push_node tree.path []))

let find_prefixes qid tab =
  try
    let (dir,id) = repr_qualid qid in
    search_prefixes (Id.Map.find id tab) (DirPath.repr dir)
  with Not_found -> []

let match_prefixes =
  let cprefix x y = CString.(compare x (sub y 0 (min (length x) (length y)))) in
  fun qid tab ->
    try
      let (dir,id) = repr_qualid qid in
      let id_prefix = cprefix Id.(to_string id) in
      let matches = Id.Map.filter_range (fun x -> id_prefix Id.(to_string x)) tab in
      let matches = Id.Map.mapi (fun _key tab -> search_prefixes tab (DirPath.repr dir)) matches in
      (* Coq's flatten is "magical", so this is not so bad perf-wise *)
      CList.flatten @@ Id.Map.(fold (fun _ r l -> r :: l) matches [])
    with Not_found -> []

end

(* Global name tables *************************************************)

module FullPath =
struct
  type t = full_path
  let equal = eq_full_path
  let to_string = string_of_path
  let repr sp =
    let dir,id = repr_path sp in
      id, (DirPath.repr dir)
end

module ExtRefEqual = ExtRefOrdered
module MPEqual = Names.ModPath

module ExtRefTab = Make(FullPath)(ExtRefEqual)
module MPTab = Make(FullPath)(MPEqual)

type ccitab = ExtRefTab.t
let the_ccitab = Summary.ref ~name:"ccitab" (ExtRefTab.empty : ccitab)

type mptab = MPTab.t
let the_modtypetab = Summary.ref ~name:"modtypetab" (MPTab.empty : mptab)

module DirPath' =
struct
  include DirPath
  let repr dir = match DirPath.repr dir with
    | [] -> anomaly (Pp.str "Empty dirpath.")
    | id :: l -> (id, l)
end

module DirTab = Make(DirPath')(GlobDirRef)

(* If we have a (closed) module M having a submodule N, than N does not
   have the entry in [the_dirtab]. *)
type dirtab = DirTab.t
let the_dirtab = Summary.ref ~name:"dirtab" (DirTab.empty : dirtab)

module UnivIdEqual =
struct
  type t = Univ.Level.UGlobal.t
  let equal = Univ.Level.UGlobal.equal
end
module UnivTab = Make(FullPath)(UnivIdEqual)
type univtab = UnivTab.t
let the_univtab = Summary.ref ~name:"univtab" (UnivTab.empty : univtab)

(* Reversed name tables ***************************************************)

(* This table translates extended_global_references back to section paths *)
type globrevtab = full_path ExtRefMap.t
let the_globrevtab = Summary.ref ~name:"globrevtab" (ExtRefMap.empty : globrevtab)


type mprevtab = DirPath.t MPmap.t
let the_modrevtab = Summary.ref ~name:"modrevtab" (MPmap.empty : mprevtab)

type mptrevtab = full_path MPmap.t
let the_modtyperevtab = Summary.ref ~name:"modtyperevtab" (MPmap.empty : mptrevtab)

module UnivIdOrdered =
struct
  type t = Univ.Level.UGlobal.t
  let hash = Univ.Level.UGlobal.hash
  let compare = Univ.Level.UGlobal.compare
end

module UnivIdMap = HMap.Make(UnivIdOrdered)

type univrevtab = full_path UnivIdMap.t
let the_univrevtab = Summary.ref ~name:"univrevtab" (UnivIdMap.empty : univrevtab)

(* Push functions *********************************************************)

(* This is for permanent constructions (never discharged -- but with
   possibly limited visibility, i.e. Theorem, Lemma, Definition, Axiom,
   Parameter but also Remark and Fact) *)

let push_xref visibility sp xref =
  match visibility with
    | Until _ ->
        the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab;
        the_globrevtab := ExtRefMap.add xref sp !the_globrevtab
    | _ ->
        begin
          if ExtRefTab.exists sp !the_ccitab then
            let open GlobRef in
            match ExtRefTab.find sp !the_ccitab with
              | TrueGlobal( ConstRef _) | TrueGlobal( IndRef _) |
                    TrueGlobal( ConstructRef _) as xref ->
                  the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab;
              | _ ->
                  the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab;
            else
              the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab;
        end

let push_cci visibility sp ref =
  push_xref visibility sp (TrueGlobal ref)

(* This is for Syntactic Definitions *)
let push_syndef visibility sp kn =
  push_xref visibility sp (SynDef kn)

let push = push_cci

let push_modtype vis sp kn =
  the_modtypetab := MPTab.push vis sp kn !the_modtypetab;
  the_modtyperevtab := MPmap.add kn sp !the_modtyperevtab

(* This is to remember absolute Section/Module names and to avoid redundancy *)
let push_dir vis dir dir_ref =
  the_dirtab := DirTab.push vis dir dir_ref !the_dirtab;
  match dir_ref with
  | GlobDirRef.DirModule { obj_mp; _ } -> the_modrevtab := MPmap.add obj_mp dir !the_modrevtab
  | _ -> ()

(* This is for global universe names *)

let push_universe vis sp univ =
  the_univtab := UnivTab.push vis sp univ !the_univtab;
  the_univrevtab := UnivIdMap.add univ sp !the_univrevtab

(* Locate functions *******************************************************)


(* This should be used when syntactic definitions are allowed *)
let locate_extended qid = ExtRefTab.locate qid !the_ccitab

(* This should be used when no syntactic definitions is expected *)
let locate qid = match locate_extended qid with
  | TrueGlobal ref -> ref
  | SynDef _ -> raise Not_found
let full_name_cci qid = ExtRefTab.user_name qid !the_ccitab

let locate_syndef qid = match locate_extended qid with
  | TrueGlobal _ -> raise Not_found
  | SynDef kn -> kn

let locate_modtype qid = MPTab.locate qid !the_modtypetab
let full_name_modtype qid = MPTab.user_name qid !the_modtypetab

let locate_universe qid = UnivTab.locate qid !the_univtab

let locate_dir qid = DirTab.locate qid !the_dirtab

let locate_module qid =
  match locate_dir qid with
    | GlobDirRef.DirModule { obj_mp ; _} -> obj_mp
    | _ -> raise Not_found

let full_name_module qid =
  match locate_dir qid with
    | GlobDirRef.DirModule { obj_dir ; _} -> obj_dir
    | _ -> raise Not_found

let locate_section qid =
  match locate_dir qid with
    | GlobDirRef.DirOpenSection { obj_dir; _ } -> obj_dir
    | _ -> raise Not_found

let locate_all qid =
  List.fold_right (fun a l -> match a with TrueGlobal a -> a::l | _ -> l)
    (ExtRefTab.find_prefixes qid !the_ccitab) []

let locate_extended_all qid = ExtRefTab.find_prefixes qid !the_ccitab

let locate_extended_all_dir qid = DirTab.find_prefixes qid !the_dirtab

let locate_extended_all_modtype qid = MPTab.find_prefixes qid !the_modtypetab

(* Completion *)
let completion_canditates qualid =
  ExtRefTab.match_prefixes qualid !the_ccitab

(* Derived functions *)

let locate_constant qid =
  let open GlobRef in
  match locate_extended qid with
    | TrueGlobal (ConstRef kn) -> kn
    | _ -> raise Not_found

let global_of_path sp =
  match ExtRefTab.find sp !the_ccitab with
    | TrueGlobal ref -> ref
    | _ -> raise Not_found

let extended_global_of_path sp = ExtRefTab.find sp !the_ccitab

let global qid =
  try match locate_extended qid with
    | TrueGlobal ref -> ref
    | SynDef _ ->
        user_err ?loc:qid.CAst.loc ~hdr:"global"
          (str "Unexpected reference to a notation: " ++
           pr_qualid qid)
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    error_global_not_found ~info qid

(* Exists functions ********************************************************)

let exists_cci sp = ExtRefTab.exists sp !the_ccitab

let exists_dir dir = DirTab.exists dir !the_dirtab

let exists_modtype sp = MPTab.exists sp !the_modtypetab

let exists_universe kn = UnivTab.exists kn !the_univtab

(* Reverse locate functions ***********************************************)

let path_of_global ref =
  let open GlobRef in
  match ref with
    | VarRef id -> make_path DirPath.empty id
    | _ -> ExtRefMap.find (TrueGlobal ref) !the_globrevtab

let dirpath_of_global ref =
  fst (repr_path (path_of_global ref))

let basename_of_global ref =
  snd (repr_path (path_of_global ref))

let path_of_syndef kn =
  ExtRefMap.find (SynDef kn) !the_globrevtab

let dirpath_of_module mp =
  MPmap.find mp !the_modrevtab

let path_of_modtype mp =
  MPmap.find mp !the_modtyperevtab

let path_of_universe mp =
  UnivIdMap.find mp !the_univrevtab

(* Shortest qualid functions **********************************************)

let shortest_qualid_of_global ?loc ctx ref =
  let open GlobRef in
  match ref with
    | VarRef id -> make_qualid ?loc DirPath.empty id
    | _ ->
        let sp = ExtRefMap.find (TrueGlobal ref) !the_globrevtab in
        ExtRefTab.shortest_qualid ?loc ctx sp !the_ccitab

let shortest_qualid_of_syndef ?loc ctx kn =
  let sp = path_of_syndef kn in
    ExtRefTab.shortest_qualid ?loc ctx sp !the_ccitab

let shortest_qualid_of_module ?loc mp =
  let dir = MPmap.find mp !the_modrevtab in
    DirTab.shortest_qualid ?loc Id.Set.empty dir !the_dirtab

let shortest_qualid_of_modtype ?loc kn =
  let sp = MPmap.find kn !the_modtyperevtab in
    MPTab.shortest_qualid ?loc Id.Set.empty sp !the_modtypetab

let shortest_qualid_of_universe ?loc ctx kn =
  let sp = UnivIdMap.find kn !the_univrevtab in
    UnivTab.shortest_qualid_gen ?loc (fun id -> Id.Map.mem id ctx) sp !the_univtab

let pr_global_env env ref =
  try pr_qualid (shortest_qualid_of_global env ref)
  with Not_found as exn ->
    let exn, info = Exninfo.capture exn in
    if CDebug.(get_flag misc) then Feedback.msg_debug (Pp.str "pr_global_env not found");
    Exninfo.iraise (exn, info)

let global_inductive qid =
  let open GlobRef in
  match global qid with
  | IndRef ind -> ind
  | ref ->
      user_err ?loc:qid.CAst.loc ~hdr:"global_inductive"
        (pr_qualid qid ++ spc () ++ str "is not an inductive type")
