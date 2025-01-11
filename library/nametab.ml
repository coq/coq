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

   The [shortest_qualid] function given a user_name Mylib.A.B.x, tries
   to find the shortest among x, B.x, A.B.x and Mylib.A.B.x that denotes
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

let coq_id = Id.of_string "Coq"
let stdlib_id = Id.of_string "Stdlib"
let init_id = Id.of_string "Corelib"

let warn_deprecated_dirpath_Coq =
  CWarnings.create_with_quickfix ~name:"deprecated-dirpath-Coq"
    ~category:Deprecation.Version.v9_0
    (fun (old_id, new_id) ->
      Pp.(old_id ++ spc () ++ str "has been replaced by" ++ spc () ++ new_id ++ str "."))

(* We shadow as to create the quickfix and message at the same time *)
let fix_coq_id coq_repl l =
  (match l with
   | _coq_id :: l -> coq_repl :: l
   | _ -> l)

(* [l] is reversed, thus [Corelib.ssr.bool] for example *)
let warn_deprecated_dirpath_Coq ?loc (coq_repl, l, id) =
  let dp l = DirPath.make (List.rev l) in
  let old_id = pr_qualid @@ Libnames.make_qualid (DirPath.make l) id in
  let new_id = pr_qualid @@ Libnames.make_qualid (dp @@ fix_coq_id coq_repl (List.rev l)) id in
  let quickfix = Option.map (fun loc -> [ Quickfix.make ~loc new_id ]) loc in
  warn_deprecated_dirpath_Coq ?loc ?quickfix (old_id, new_id)

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

let rec search coq_repl tree = function
  | [modid] when Id.equal modid coq_id ->
     let _warn, p =
       match ModIdmap.find_opt coq_repl tree.map with
       | None -> None, None
       | Some modid -> search coq_repl modid [] in
     Some coq_repl, p
  | modid :: path ->
     begin match ModIdmap.find_opt modid tree.map with
     | None -> None, None
     | Some modid -> search coq_repl modid path end
  | [] -> None, Some tree.path

let search ?loc id tree dir =
  let warn, p = search stdlib_id tree dir in
  let warn, p =
    match p with Some _ -> warn, p | None -> search init_id tree dir in
  begin match warn with None -> () | Some coq_repl ->
    warn_deprecated_dirpath_Coq ?loc (coq_repl, dir, id) end;
  match p with Some p -> p | None -> raise Not_found

let find_node qid tab =
  let loc = qid.CAst.loc in
  let (dir,id) = repr_qualid qid in
  search ?loc id (Id.Map.find id tab) (DirPath.repr dir)

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
    match search id (Id.Map.find id tab) l with
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
      (* Rocq's flatten is "magical", so this is not so bad perf-wise *)
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

module DirPath' =
struct
  include DirPath
  let repr dir = match DirPath.repr dir with
    | [] -> CErrors.anomaly (Pp.str "Empty dirpath.")
    | id :: l -> (id, l)
end

module MPDTab = Make(DirPath')(MPEqual)
module DirTab = Make(DirPath')(GlobDirRef)

module UnivTab = Make(FullPath)(Univ.UGlobal)
type univtab = UnivTab.t
let the_univtab = Summary.ref ~name:"univtab" (UnivTab.empty : univtab)

(* Reversed name tables ***************************************************)

(* This table translates extended_global_references back to section paths *)
type globrevtab = full_path ExtRefMap.t
let the_globrevtab =
  Summary.ref ~name:"globrevtab" (ExtRefMap.empty : globrevtab)

let the_globwarntab = Summary.ref ~name:"globwarntag" ExtRefMap.empty

type mprevtab = DirPath.t MPmap.t

type mptrevtab = full_path MPmap.t

module UnivIdMap = HMap.Make(Univ.UGlobal)

type univrevtab = full_path UnivIdMap.t
let the_univrevtab = Summary.ref ~name:"univrevtab" (UnivIdMap.empty : univrevtab)

(** Module-related nametab *)
module Modules = struct

  type t = {
    modtypetab : MPTab.t;
    modtab : MPDTab.t;
    dirtab : DirTab.t;
    modrevtab : mprevtab;
    modtyperevtab : mptrevtab;
  }

  let initial = {
    modtypetab = MPTab.empty;
    modtab = MPDTab.empty;
    dirtab = DirTab.empty;
    modrevtab = MPmap.empty;
    modtyperevtab = MPmap.empty
  }

  let nametab, summary_tag =
    Summary.ref_tag ~stage:Summary.Stage.Synterp ~name:"MODULES-NAMETAB" initial

  let freeze () = !nametab
  let unfreeze v = nametab := v

end

(* Push functions *********************************************************)

(* This is for permanent constructions (never discharged -- but with
   possibly limited visibility, i.e. Theorem, Lemma, Definition, Axiom,
   Parameter but also Remark and Fact) *)

let push_xref ?user_warns visibility sp xref =
  match visibility with
    | Until _ ->
        the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab;
        the_globrevtab := ExtRefMap.add xref sp !the_globrevtab;
        user_warns |> Option.iter (fun warn ->
            the_globwarntab := ExtRefMap.add xref warn !the_globwarntab)
    | Exactly _ ->
      begin
        assert (Option.is_empty user_warns);
        the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab
      end

let remove_xref sp xref =
  the_ccitab := ExtRefTab.remove sp !the_ccitab;
  the_globrevtab := ExtRefMap.remove xref !the_globrevtab;
  the_globwarntab := ExtRefMap.remove xref !the_globwarntab

let push_cci ?user_warns visibility sp ref =
  push_xref ?user_warns visibility sp (TrueGlobal ref)

(* This is for Syntactic Definitions *)
let push_abbreviation ?user_warns visibility sp kn =
  push_xref ?user_warns visibility sp (Abbrev kn)

let remove_abbreviation sp kn =
  remove_xref sp (Abbrev kn)

let push = push_cci

let push_modtype vis sp kn =
  let open Modules in
  nametab := { !nametab with
    modtypetab = MPTab.push vis sp kn !nametab.modtypetab;
    modtyperevtab = MPmap.add kn sp !nametab.modtyperevtab;
  }

let push_module vis dir mp =
  let open Modules in
  nametab := { !nametab with
    modtab = MPDTab.push vis dir mp !nametab.modtab;
    modrevtab = MPmap.add mp dir !nametab.modrevtab;
  }

(* This is to remember absolute Section/Module names and to avoid redundancy *)
let push_dir vis dir dir_ref =
  let open Modules in
  nametab := { !nametab with
    dirtab = DirTab.push vis dir dir_ref !Modules.nametab.dirtab;
  }

(* This is for global universe names *)

let push_universe vis sp univ =
  the_univtab := UnivTab.push vis sp univ !the_univtab;
  the_univrevtab := UnivIdMap.add univ sp !the_univrevtab

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

let path_of_abbreviation kn =
  ExtRefMap.find (Abbrev kn) !the_globrevtab

let dirpath_of_module mp =
  MPmap.find mp Modules.(!nametab.modrevtab)

let path_of_modtype mp =
  MPmap.find mp Modules.(!nametab.modtyperevtab)

let path_of_universe mp =
  UnivIdMap.find mp !the_univrevtab

(* Shortest qualid functions **********************************************)

let shortest_qualid_of_global ?loc ctx ref =
  let open GlobRef in
  match ref with
    | VarRef id -> make_qualid ?loc DirPath.empty id
    | _ ->
        let sp =  ExtRefMap.find (TrueGlobal ref) !the_globrevtab in
        ExtRefTab.shortest_qualid ?loc ctx sp !the_ccitab

let shortest_qualid_of_abbreviation ?loc ctx kn =
  let sp = path_of_abbreviation kn in
    ExtRefTab.shortest_qualid ?loc ctx sp !the_ccitab

let shortest_qualid_of_module ?loc mp =
  let dir = MPmap.find mp Modules.(!nametab.modrevtab) in
  MPDTab.shortest_qualid ?loc Id.Set.empty dir Modules.(!nametab.modtab)

let shortest_qualid_of_modtype ?loc kn =
  let sp = MPmap.find kn Modules.(!nametab.modtyperevtab) in
    MPTab.shortest_qualid ?loc Id.Set.empty sp Modules.(!nametab.modtypetab)

let shortest_qualid_of_universe ?loc ctx kn =
  let sp = UnivIdMap.find kn !the_univrevtab in
  UnivTab.shortest_qualid_gen ?loc (fun id -> Id.Map.mem id ctx) sp !the_univtab

let pr_global_env env ref =
  try pr_qualid (shortest_qualid_of_global env ref)
  with Not_found as exn ->
    let exn, info = Exninfo.capture exn in
    if !Flags.in_debugger then GlobRef.print ref
    else begin
      let () = if CDebug.(get_flag misc)
        then Feedback.msg_debug (Pp.str "pr_global_env not found")
      in
      Exninfo.iraise (exn, info)
    end

(* Locate functions *******************************************************)

let pr_depr_xref xref =
  let sp = ExtRefMap.get xref !the_globrevtab in
  pr_qualid (ExtRefTab.shortest_qualid Id.Set.empty sp !the_ccitab)

let pr_depr_ref ref = pr_depr_xref (TrueGlobal ref)

let warn_deprecated_ref =
  Deprecation.create_warning_with_qf ~object_name:"Reference" ~warning_name_if_no_since:"deprecated-reference"
  ~pp_qf:pr_depr_xref pr_depr_ref

let pr_depr_abbrev a = pr_depr_xref (Abbrev a)

let warn_deprecated_abbreviation =
  Deprecation.create_warning_with_qf ~object_name:"Notation" ~warning_name_if_no_since:"deprecated-syntactic-definition"
  ~pp_qf:pr_depr_xref pr_depr_abbrev

let warn_deprecated_xref ?loc depr = function
  | TrueGlobal ref -> warn_deprecated_ref ?loc (ref, depr)
  | Abbrev a -> warn_deprecated_abbreviation ?loc (a, depr)

let warn_user_warn =
  UserWarn.create_warning ~warning_name_if_no_cats:"warn-reference" ()

let is_warned_xref xref : extended_global_reference UserWarn.with_qf option = ExtRefMap.find_opt xref !the_globwarntab

let warn_user_warn_xref ?loc user_warns xref =
  user_warns.UserWarn.depr_qf
    |> Option.iter (fun depr -> warn_deprecated_xref ?loc depr xref);
  user_warns.UserWarn.warn_qf |> List.iter (warn_user_warn ?loc)

let locate_extended_nowarn qid =
  let xref = ExtRefTab.locate qid !the_ccitab in
  xref

(* This should be used when abbreviations are allowed *)
let locate_extended qid =
  let xref = locate_extended_nowarn qid in
  let warn = is_warned_xref xref in
  let () = warn |> Option.iter (fun warn ->
      warn_user_warn_xref ?loc:qid.loc warn xref) in
  xref

(* This should be used when no abbreviations are expected *)
let locate qid = match locate_extended qid with
  | TrueGlobal ref -> ref
  | Abbrev _ -> raise Not_found

let locate_abbreviation qid = match locate_extended qid with
  | TrueGlobal _ -> raise Not_found
  | Abbrev kn -> kn

let locate_modtype qid = MPTab.locate qid Modules.(!nametab.modtypetab)
let full_name_modtype qid = MPTab.user_name qid Modules.(!nametab.modtypetab)

let locate_universe qid = UnivTab.locate qid !the_univtab

let locate_dir qid = DirTab.locate qid Modules.(!nametab.dirtab)

let locate_module qid = MPDTab.locate qid Modules.(!nametab.modtab)

let full_name_module qid = MPDTab.user_name qid Modules.(!nametab.modtab)

let locate_section qid =
  match locate_dir qid with
    | GlobDirRef.DirOpenSection dir -> dir
    | _ -> raise Not_found

(* Users of locate_all don't seem to need deprecation info *)
let locate_all qid =
  List.fold_right (fun a l ->
    match a with
    | TrueGlobal a -> a::l
    | _ -> l)
    (ExtRefTab.find_prefixes qid !the_ccitab) []

let locate_extended_all qid = ExtRefTab.find_prefixes qid !the_ccitab

let locate_extended_all_dir qid = DirTab.find_prefixes qid Modules.(!nametab.dirtab)

let locate_extended_all_modtype qid = MPTab.find_prefixes qid Modules.(!nametab.modtypetab)

let locate_extended_all_module qid = MPDTab.find_prefixes qid Modules.(!nametab.modtab)

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
    | Abbrev _ ->
        CErrors.user_err ?loc:qid.CAst.loc
          Pp.(str "Unexpected reference to a notation: " ++
           pr_qualid qid ++ str ".")
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    error_global_not_found ~info qid

let global_inductive qid =
  let open GlobRef in
  match global qid with
  | IndRef ind -> ind
  | ref ->
      CErrors.user_err ?loc:qid.CAst.loc
        Pp.(pr_qualid qid ++ spc () ++ str "is not an inductive type.")

(* Exists functions ********************************************************)

let exists_cci sp = ExtRefTab.exists sp !the_ccitab

let exists_dir dir = DirTab.exists dir Modules.(!nametab.dirtab)

let exists_module dir = MPDTab.exists dir Modules.(!nametab.modtab)

let exists_modtype sp = MPTab.exists sp Modules.(!nametab.modtypetab)

let exists_universe kn = UnivTab.exists kn !the_univtab

(* Source locations *)

open Globnames

let cci_loc_table : Loc.t ExtRefMap.t ref = Summary.ref ~name:"constant-loc-table" ExtRefMap.empty

let set_cci_src_loc kn loc = cci_loc_table := ExtRefMap.add kn loc !cci_loc_table

let cci_src_loc kn = ExtRefMap.find_opt kn !cci_loc_table
