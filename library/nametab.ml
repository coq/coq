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
open Libnames

(* Shadowing help *)
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
    | DirOpenModule of ModPath.t
    | DirOpenModtype of ModPath.t
    | DirOpenSection of DirPath.t

  let equal r1 r2 = match r1, r2 with
    | DirOpenModule op1, DirOpenModule op2 -> ModPath.equal op1 op2
    | DirOpenModtype op1, DirOpenModtype op2 -> ModPath.equal op1 op2
    | DirOpenSection op1, DirOpenSection op2 -> DirPath.equal op1 op2
    | (DirOpenModule _ | DirOpenModtype _ | DirOpenSection _), _ -> false

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
  type t
  type elt
  type user_name

  val empty : t
  val push : visibility -> user_name -> elt -> t -> t
  val locate : qualid -> t -> elt
  val find : user_name -> t -> elt
  val remove : user_name -> t -> t
  val exists : user_name -> t -> bool
  val user_name : qualid -> t -> user_name
  val shortest_qualid_gen : ?loc:Loc.t -> (Id.t -> bool) -> user_name -> t -> qualid
  val shortest_qualid : ?loc:Loc.t -> Id.Set.t -> user_name -> t -> qualid
  val find_prefixes : qualid -> t -> elt list

  (** Matches a prefix of [qualid], useful for completion *)
  val match_prefixes : qualid -> t -> elt list
end

let masking_absolute = CWarnings.create_warning
    ~from:[Deprecation.Version.v8_8] ~name:"masking-absolute-name" ()

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
    CWarnings.create_in masking_absolute
      (fun n -> Pp.str ("Trying to mask the absolute name \"" ^ U.to_string n ^ "\"!"))

  type user_name = U.t

  type path_status =
    | Relative of user_name * elt
    | Absolute of user_name * elt

  (* Dictionaries of short names *)
  type nametree =
      { path : path_status list;
        map : nametree ModIdmap.t }

  let mktree p m = { path=p; map=m }
  let empty_tree = mktree [] ModIdmap.empty
  let is_empty_tree tree = tree.path = [] && ModIdmap.is_empty tree.map

  type t = nametree Id.Map.t

  let empty = Id.Map.empty

  (* [push_until] is used to register [Until vis] visibility.

     Example: [push_until Top.X.Y.t o (Until 1) tree [Y;X;Top]] adds the
     value [Relative (Top.X.Y.t,o)] to occurrences [Y] and [Y.X] of
     the tree, and [Absolute (Top.X.Y.t,o)] to occurrence [Y.X.Top] of
     the tree. In particular, the tree now includes the following shape:
     { map := Y |-> {map := X |-> {map := Top |-> {map := ...;
                                                   path := Absolute (Top.X.Y.t,o)::...}
                                          ...;
                                   path := Relative (Top.X.Y.t,o)::...}
                             ...;
                     path := Relative (Top.X.Y.t,o)::...}
               ...;
       path := ...}
     where ... denotes what was there before.

     [push_exactly] is to register [Exactly vis] and [push] chooses
     the right one *)

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
              | Absolute (n,_)::_ ->
                  (* This is an absolute name, we must keep it
                     otherwise it may become unaccessible forever *)
                warn_masking_absolute n; tree.path
              | current -> Relative (uname,o) :: current
          else tree.path
        in
        mktree this map
    | [] ->
        match tree.path with
          | Absolute (uname',o') :: _ ->
              if E.equal o' o then begin
                assert (U.equal uname uname');
                tree
                  (* we are putting the same thing for the second time :) *)
              end
              else
                (* This is an absolute name, we must keep it otherwise it may
                   become unaccessible forever *)
                (* But ours is also absolute! This is an error! *)
                CErrors.user_err Pp.(str @@ "Cannot mask the absolute name \""
                                   ^ U.to_string uname' ^ "\"!")
          | current -> mktree (Absolute (uname,o) :: current) tree.map

let rec push_exactly uname o level tree = function
| [] ->
  CErrors.anomaly (Pp.str "Prefix longer than path! Impossible!")
| modid :: path ->
  if Int.equal level 0 then
    let this =
      match tree.path with
        | Absolute (n,_) :: _ ->
            (* This is an absolute name, we must keep it
                otherwise it may become unaccessible forever *)
            warn_masking_absolute n; tree.path
        | current -> Relative (uname,o) :: current
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

(** [remove_path uname tree dir] removes all bindings pointing to
    [uname] along the path [dir] in [tree] (i.e. all such bindings are
    assumed to be on this path) *)

let rec remove_path uname tree = function
  | modid :: path ->
      let update = function
        | None -> (* The name was actually not here *) None
        | Some mc ->
          let mc = remove_path uname mc path in
          if is_empty_tree mc then None else Some mc
      in
      let map = ModIdmap.update modid update tree.map in
      let this =
        let test = function Relative (uname',_) -> not (U.equal uname uname') | _ -> true in
        List.filter test tree.path
      in
      mktree this map
  | [] ->
      let this =
        let test = function Absolute (uname',_) -> not (U.equal uname uname') | _ -> true in
        List.filter test tree.path
      in
      mktree this tree.map

(** Remove all bindings pointing to [uname] in [tab] *)

let remove uname tab =
  let id,dir = U.repr uname in
  let modify _ ptab = remove_path uname ptab dir in
  try Id.Map.modify id modify tab
  with Not_found -> tab

let rec search tree = function
  | modid :: path -> search (ModIdmap.find modid tree.map) path
  | [] -> tree.path

let find_node qid tab =
  let (dir,id) = repr_qualid qid in
    search (Id.Map.find id tab) (DirPath.repr dir)

let locate qid tab =
  let o = match find_node qid tab with
    | (Absolute (uname,o) | Relative (uname,o)) :: _ -> o
    | [] -> raise Not_found
  in
    o

let user_name qid tab =
  let uname = match find_node qid tab with
    | (Absolute (uname,o) | Relative (uname,o)) :: _ -> uname
    | [] -> raise Not_found
  in
    uname

let find uname tab =
  let id,l = U.repr uname in
    match search (Id.Map.find id tab) l with
        Absolute (_,o) :: _ -> o
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
    | (Absolute (u,_) | Relative (u,_)) :: _
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
  | (Absolute (_,o) | Relative (_,o)) :: _
    when not (Util.List.mem_f E.equal o l) -> o::l
  | _ -> l

let rec flatten_tree tree l =
  let f _ tree l = flatten_tree tree l in
  ModIdmap.fold f tree.map (push_node tree.path l)

let rec search_prefixes tree = function
  | modid :: path -> search_prefixes (ModIdmap.find modid tree.map) path
  | [] -> List.rev (flatten_tree tree [])

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

(** Type of nametabs (imperative) *)
module type S = sig

  type elt
  type path

  val push : ?deprecated:Deprecation.t -> visibility -> path -> elt -> unit
  val remove : path -> elt -> unit
  val locate : qualid -> elt
  val locate_all : qualid -> elt list
  val exists : path -> bool

  (* future work *)
  (* val shortest_qualid : *)
end

module type SR = sig
  include S
  val path : elt -> path
  val shortest_qualid : ?loc:Loc.t -> Names.Id.Set.t -> elt -> qualid
end

(***********************************************************************)
(* For Global References *)

(* This is for permanent constructions (never discharged -- but with
   possibly limited visibility, i.e. Theorem, Lemma, Definition,
   Axiom, Parameter but also Remark and Fact) *)

module FullPath =
struct
  type t = full_path
  let equal = eq_full_path
  let to_string = string_of_path
  let repr sp =
    let dir,id = repr_path sp in
    id, (DirPath.repr dir)
end

module ExtRefEqual = Globnames.ExtRefOrdered
module ExtRefTab = Make(FullPath)(ExtRefEqual)
type ccitab = ExtRefTab.t
let the_ccitab = Summary.ref ~name:"ccitab" (ExtRefTab.empty : ccitab)

(* This table translates extended_global_references back to section paths *)
type globrevtab = full_path Globnames.ExtRefMap.t
let the_globrevtab =
  Summary.ref ~name:"globrevtab" (Globnames.ExtRefMap.empty : globrevtab)

let the_globdeprtab = Summary.ref ~name:"globdeprtag" Globnames.ExtRefMap.empty

let extended_global_of_path sp = ExtRefTab.find sp !the_ccitab

let push_xref ?deprecated visibility (sp : Libnames.full_path) (xref : Globnames.extended_global_reference) =
  match visibility with
  | Until _ ->
    the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab;
    the_globrevtab := Globnames.ExtRefMap.add xref sp !the_globrevtab;
    deprecated |> Option.iter (fun depr ->
        the_globdeprtab := Globnames.ExtRefMap.add xref depr !the_globdeprtab)
  | Exactly _ ->
    begin
      assert (Option.is_empty deprecated);
      the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab
    end

let remove_xref (sp : Libnames.full_path) (xref : Globnames.extended_global_reference) : unit =
  the_ccitab := ExtRefTab.remove sp !the_ccitab;
  the_globrevtab := Globnames.ExtRefMap.remove xref !the_globrevtab;
  the_globdeprtab := Globnames.ExtRefMap.remove xref !the_globdeprtab

(* Deprecated extrefs *)
let pr_depr_xref xref =
  let sp = Globnames.ExtRefMap.get xref !the_globrevtab in
  pr_qualid (ExtRefTab.shortest_qualid Id.Set.empty sp !the_ccitab)

let pr_depr_ref ref = pr_depr_xref (TrueGlobal ref)

let warn_deprecated_ref =
  Deprecation.create_warning ~object_name:"Reference" ~warning_name_if_no_since:"deprecated-reference"
    pr_depr_ref

let pr_depr_abbrev a = pr_depr_xref (Abbrev a)

let warn_deprecated_abbreviation =
  Deprecation.create_warning ~object_name:"Notation" ~warning_name_if_no_since:"deprecated-syntactic-definition"
    pr_depr_abbrev

let warn_deprecated_xref ?loc depr = function
  | Globnames.TrueGlobal ref -> warn_deprecated_ref ?loc (ref, depr)
  | Abbrev a -> warn_deprecated_abbreviation ?loc (a, depr)

let is_deprecated_xref xref = Globnames.ExtRefMap.find_opt xref !the_globdeprtab

(* This should be used when syntactic definitions are allowed *)
let locate_extended qid = ExtRefTab.locate qid !the_ccitab

let locate_extended_nowarn qid =
  let xref = ExtRefTab.locate qid !the_ccitab in
  let depr = is_deprecated_xref xref in
  xref, depr

let locate_extended_all qid = ExtRefTab.find_prefixes qid !the_ccitab
let full_name_cci qid = ExtRefTab.user_name qid !the_ccitab

module GlobRef : SR
  with type elt := GlobRef.t and type path := full_path =
struct

  let push ?deprecated visibility sp ref =
    push_xref ?deprecated visibility sp (TrueGlobal ref)

  let remove sp ref = remove_xref sp (TrueGlobal ref)

  (* This should be used when no syntactic definitions is expected *)
  let locate qid = match locate_extended qid with
    | TrueGlobal ref -> ref
    | Abbrev _ -> raise Not_found

  let locate_all qid =
    locate_extended_all qid
    |> List.filter_map (fun x -> match x with Globnames.TrueGlobal a -> Some a | _ -> None)

  let exists sp = ExtRefTab.exists sp !the_ccitab
  let path ref =
    let open GlobRef in
    match ref with
    | VarRef id -> make_path DirPath.empty id
    | _ -> Globnames.ExtRefMap.find (TrueGlobal ref) !the_globrevtab

  (* XXX: refactor with the above *)
  let shortest_qualid ?loc ctx ref =
    match ref with
    | GlobRef.VarRef id -> make_qualid ?loc DirPath.empty id
    | _ ->
      let sp =  Globnames.ExtRefMap.find (TrueGlobal ref) !the_globrevtab in
      ExtRefTab.shortest_qualid ?loc ctx sp !the_ccitab
end

(* Completion *)
let completion_canditates qualid = ExtRefTab.match_prefixes qualid !the_ccitab

let global_of_path sp =
  match extended_global_of_path sp with
  | TrueGlobal ref -> ref
  | _ -> raise Not_found

let global qid =
  try match locate_extended qid with
    | TrueGlobal ref -> ref
    | Abbrev _ ->
      CErrors.user_err ?loc:qid.CAst.loc
        Pp.(str "Unexpected reference to a notation: " ++
           pr_qualid qid ++ str ".")
  with
  | Not_found as exn ->
    let _, info = Exninfo.capture exn in
    error_global_not_found ~info qid

let pr_global_env env ref =
  try pr_qualid (GlobRef.shortest_qualid env ref)
  with Not_found as exn ->
    let exn, info = Exninfo.capture exn in
    if CDebug.(get_flag misc) then Feedback.msg_debug (Pp.str "pr_global_env not found");
    Exninfo.iraise (exn, info)

let global_inductive qid =
  match global qid with
  | IndRef ind -> ind
  | ref ->
    CErrors.user_err ?loc:qid.CAst.loc
      Pp.(pr_qualid qid ++ spc () ++ str "is not an inductive type.")

(* Reverse locate functions ***********************************************)
let dirpath_of_global ref = fst (repr_path (GlobRef.path ref))
let basename_of_global ref = snd (repr_path (GlobRef.path ref))

(***********************************************************************)
(* Syntactic Definitions. *)
module Abbrev : SR
  with type elt := Globnames.abbreviation and type path := full_path =
struct

  let push ?deprecated visibility sp kn = push_xref visibility sp (Abbrev kn)

  let remove sp kn = remove_xref sp (Abbrev kn)

  let locate qid = match locate_extended qid with
    | TrueGlobal _ -> raise Not_found
    | Abbrev kn -> kn

  let locate_all qid =
    locate_extended_all qid
    |> List.filter_map (fun x -> match x with Globnames.Abbrev a -> Some a | _ -> None)

  let exists sp = ExtRefTab.exists sp !the_ccitab
  let path kn = Globnames.ExtRefMap.find (Abbrev kn) !the_globrevtab

  let shortest_qualid ?loc ctx kn =
    let sp = path kn in
    ExtRefTab.shortest_qualid ?loc ctx sp !the_ccitab
end

(***********************************************************************)
(* For modules *)
module MPEqual = Names.ModPath
module MPTab = Make(FullPath)(MPEqual)

module DirPath' =
struct
  include DirPath
  let repr dir = match DirPath.repr dir with
    | [] -> CErrors.anomaly (Pp.str "Empty dirpath.")
    | id :: l -> (id, l)
end

module MPDTab = Make(DirPath')(MPEqual)
module DirTab = Make(DirPath')(GlobDirRef)

(** Module-related nametab *)
module Modules = struct

  type t =
    { modtypetab : MPTab.t
    ; modtyperevtab : full_path MPmap.t

    ; modtab : MPDTab.t
    ; modrevtab : DirPath.t MPmap.t

    ; dirtab : DirTab.t
    }

  let initial =
    { modtypetab = MPTab.empty
    ; modtyperevtab = MPmap.empty
    ; modtab = MPDTab.empty
    ; modrevtab = MPmap.empty
    ; dirtab = DirTab.empty
    }

  let nametab, summary_tag =
    Summary.ref_tag ~stage:Summary.Stage.Synterp ~name:"MODULES-NAMETAB" initial

  let freeze () = !nametab
  let unfreeze v = nametab := v

end

(***********************************************************************)
(* Module types *)
module ModType : SR
  with type elt := ModPath.t and type path := full_path =
struct
  let push ?deprecated vis sp kn =
    let open Modules in
    nametab := { !nametab with
                 modtypetab = MPTab.push vis sp kn !nametab.modtypetab
               ; modtyperevtab = MPmap.add kn sp !nametab.modtyperevtab
               }

  let remove sp kn =
    let open Modules in
    nametab := { !nametab with
                 modtypetab = MPTab.remove sp !nametab.modtypetab
               ; modtyperevtab = MPmap.remove kn !nametab.modtyperevtab
               }

  let locate qid = MPTab.locate qid Modules.(!nametab.modtypetab)
  let locate_all qid = MPTab.find_prefixes qid Modules.(!nametab.modtypetab)

  let exists sp = MPTab.exists sp Modules.(!nametab.modtypetab)
  let path mp = MPmap.find mp Modules.(!nametab.modtyperevtab)
  let shortest_qualid ?loc ctx kn =
    let sp = path kn in
    MPTab.shortest_qualid ?loc ctx sp Modules.(!nametab.modtypetab)
end

(***********************************************************************)
(* Module implementations *)
module Module : SR
  with type elt := ModPath.t and type path := DirPath.t =
struct
  let push ?deprecated vis dir mp =
    let open Modules in
    nametab := { !nametab with
                 modtab = MPDTab.push vis dir mp !nametab.modtab
               ; modrevtab = MPmap.add mp dir !nametab.modrevtab;
               }

  let remove dir mp =
    let open Modules in
    nametab := { !nametab with
                 modtab = MPDTab.remove dir !nametab.modtab
               ; modrevtab = MPmap.remove mp !nametab.modrevtab;
               }

  let locate qid = MPDTab.locate qid Modules.(!nametab.modtab)

  let locate_all qid = MPDTab.find_prefixes qid Modules.(!nametab.modtab)

  let exists dir = MPDTab.exists dir Modules.(!nametab.modtab)

  let path mp = MPmap.find mp Modules.(!nametab.modrevtab)

  let shortest_qualid ?loc ctx mp =
    let dir = path mp in
    MPDTab.shortest_qualid ?loc ctx dir Modules.(!nametab.modtab)

end


(***********************************************************************)
(* For ... *)
module Dir : S
  with type elt := GlobDirRef.t and type path := DirPath.t =
struct

  (* This is to remember absolute Section/Module names and to avoid redundancy *)
  let push ?deprecated vis dir dir_ref =
    let open Modules in
    nametab := { !nametab with
                 dirtab = DirTab.push vis dir dir_ref !Modules.nametab.dirtab
               }

  let remove dir dir_ref =
    let open Modules in
    nametab := { !nametab with
                 dirtab = DirTab.remove dir !Modules.nametab.dirtab
               }

  let locate qid = DirTab.locate qid Modules.(!nametab.dirtab)
  let locate_all qid = DirTab.find_prefixes qid Modules.(!nametab.dirtab)
  let exists dir = DirTab.exists dir Modules.(!nametab.dirtab)
end

let locate_section qid =
  match Dir.locate qid with
    | GlobDirRef.DirOpenSection dir -> dir
    | _ -> raise Not_found

(* Aux *)
let full_name_modtype qid = MPTab.user_name qid Modules.(!nametab.modtypetab)
let full_name_module qid = MPDTab.user_name qid Modules.(!nametab.modtab)

(***********************************************************************)
(* For global universe names *)
module UnivIdEqual =
struct
  type t = Univ.UGlobal.t
  let equal = Univ.UGlobal.equal
end

module UnivTab = Make(FullPath)(UnivIdEqual)

type univtab = UnivTab.t
let the_univtab = Summary.ref ~name:"univtab" (UnivTab.empty : univtab)

module UnivIdOrdered =
struct
  type t = Univ.UGlobal.t
  let hash = Univ.UGlobal.hash
  let compare = Univ.UGlobal.compare
end

(* Reverse map *)
module UnivIdMap = HMap.Make(UnivIdOrdered)

type univrevtab = full_path UnivIdMap.t
let the_univrevtab = Summary.ref ~name:"univrevtab" (UnivIdMap.empty : univrevtab)

module Universe : SR
  with type elt := Univ.UGlobal.t and type path := full_path =
struct
  let push ?deprecated vis sp univ =
    the_univtab := UnivTab.push vis sp univ !the_univtab;
    the_univrevtab := UnivIdMap.add univ sp !the_univrevtab

  let remove sp univ =
    the_univtab := UnivTab.remove sp !the_univtab;
    the_univrevtab := UnivIdMap.remove univ !the_univrevtab

  let locate qid = UnivTab.locate qid !the_univtab
  let locate_all = Obj.magic
  let exists kn = UnivTab.exists kn !the_univtab
  let path mp = UnivIdMap.find mp !the_univrevtab
  let shortest_qualid ?loc ctx kn =
    let sp = path kn in
    UnivTab.shortest_qualid_gen ?loc (fun id -> Id.Set.mem id ctx) sp !the_univtab
end
