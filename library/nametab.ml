(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Pp
open Names
open Libnames
open Globnames


exception GlobalizationError of qualid

let error_global_not_found_loc loc q =
  Loc.raise loc (GlobalizationError q)

let error_global_not_found q = raise (GlobalizationError q)

(* Kinds of global names *)

type ltac_constant = kernel_name

(* The visibility can be registered either
   - for all suffixes not shorter then a given int - when the object
     is loaded inside a module
   or
   - for a precise suffix, when the module containing (the module
     containing ...) the object is open (imported)
*)
type visibility = Until of int | Exactly of int


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
  val shortest_qualid : Id.Set.t -> user_name -> t -> qualid
  val find_prefixes : qualid -> t -> elt list
end

module Make (U : UserName) (E : EqualityType) : NAMETREE
  with type user_name = U.t and type elt = E.t =
struct
  type elt = E.t

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
		    msg_warning (str ("Trying to mask the absolute name \""
			     ^ U.to_string n ^ "\"!"));
		  tree.path
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
		error ("Cannot mask the absolute name \""
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
              msg_warning (str ("Trying to mask the absolute name \""
                        ^ U.to_string n ^ "\"!"));
            tree.path
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

let shortest_qualid ctx uname tab =
  let id,dir = U.repr uname in
  let hidden = Id.Set.mem id ctx in
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
    make_qualid (DirPath.make found_dir) id

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
module KnEqual = Names.KerName
module MPEqual = Names.ModPath

module ExtRefTab = Make(FullPath)(ExtRefEqual)
module KnTab = Make(FullPath)(KnEqual)
module MPTab = Make(FullPath)(MPEqual)

type ccitab = ExtRefTab.t
let the_ccitab = ref (ExtRefTab.empty : ccitab)

type kntab = KnTab.t
let the_tactictab = ref (KnTab.empty : kntab)

type mptab = MPTab.t
let the_modtypetab = ref (MPTab.empty : mptab)

module DirPath' =
struct
  include DirPath
  let repr dir = match DirPath.repr dir with
    | [] -> anomaly (Pp.str "Empty dirpath")
    | id :: l -> (id, l)
end

module GlobDir =
struct
  type t = global_dir_reference
  let equal = eq_global_dir_reference
end

module DirTab = Make(DirPath')(GlobDir)

(* If we have a (closed) module M having a submodule N, than N does not
   have the entry in [the_dirtab]. *)
type dirtab = DirTab.t
let the_dirtab = ref (DirTab.empty : dirtab)


(* Reversed name tables ***************************************************)

(* This table translates extended_global_references back to section paths *)
module Globrevtab = HMap.Make(ExtRefOrdered)

type globrevtab = full_path Globrevtab.t
let the_globrevtab = ref (Globrevtab.empty : globrevtab)


type mprevtab = DirPath.t MPmap.t
let the_modrevtab = ref (MPmap.empty : mprevtab)

type mptrevtab = full_path MPmap.t
let the_modtyperevtab = ref (MPmap.empty : mptrevtab)

type knrevtab = full_path KNmap.t
let the_tacticrevtab = ref (KNmap.empty : knrevtab)


(* Push functions *********************************************************)

(* This is for permanent constructions (never discharged -- but with
   possibly limited visibility, i.e. Theorem, Lemma, Definition, Axiom,
   Parameter but also Remark and Fact) *)

let push_xref visibility sp xref =
  match visibility with
    | Until _ ->
	the_ccitab := ExtRefTab.push visibility sp xref !the_ccitab;
	the_globrevtab := Globrevtab.add xref sp !the_globrevtab
    | _ ->
	begin
	  if ExtRefTab.exists sp !the_ccitab then
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

(* This is for tactic definition names *)

let push_tactic vis sp kn =
  the_tactictab := KnTab.push vis sp kn !the_tactictab;
  the_tacticrevtab := KNmap.add kn sp !the_tacticrevtab


(* This is to remember absolute Section/Module names and to avoid redundancy *)
let push_dir vis dir dir_ref =
  the_dirtab := DirTab.push vis dir dir_ref !the_dirtab;
  match dir_ref with
      DirModule (_,(mp,_)) -> the_modrevtab := MPmap.add mp dir !the_modrevtab
    | _ -> ()


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

let locate_tactic qid = KnTab.locate qid !the_tactictab

let locate_dir qid = DirTab.locate qid !the_dirtab

let locate_module qid =
  match locate_dir qid with
    | DirModule (_,(mp,_)) -> mp
    | _ -> raise Not_found

let full_name_module qid =
  match locate_dir qid with
    | DirModule (dir,_) -> dir
    | _ -> raise Not_found

let locate_section qid =
  match locate_dir qid with
    | DirOpenSection (dir, _)
    | DirClosedSection dir -> dir
    | _ -> raise Not_found

let locate_all qid =
  List.fold_right (fun a l -> match a with TrueGlobal a -> a::l | _ -> l)
    (ExtRefTab.find_prefixes qid !the_ccitab) []

let locate_extended_all qid = ExtRefTab.find_prefixes qid !the_ccitab

let locate_extended_all_tactic qid = KnTab.find_prefixes qid !the_tactictab

let locate_extended_all_dir qid = DirTab.find_prefixes qid !the_dirtab

let locate_extended_all_modtype qid = MPTab.find_prefixes qid !the_modtypetab

(* Derived functions *)

let locate_constant qid =
  match locate_extended qid with
    | TrueGlobal (ConstRef kn) -> kn
    | _ -> raise Not_found

let global_of_path sp =
  match ExtRefTab.find sp !the_ccitab with
    | TrueGlobal ref -> ref
    | _ -> raise Not_found

let extended_global_of_path sp = ExtRefTab.find sp !the_ccitab

let global r =
  let (loc,qid) = qualid_of_reference r in
  try match locate_extended qid with
    | TrueGlobal ref -> ref
    | SynDef _ ->
        user_err_loc (loc,"global",
          str "Unexpected reference to a notation: " ++
          pr_qualid qid)
  with Not_found ->
    error_global_not_found_loc loc qid

(* Exists functions ********************************************************)

let exists_cci sp = ExtRefTab.exists sp !the_ccitab

let exists_dir dir = DirTab.exists dir !the_dirtab

let exists_section = exists_dir

let exists_module = exists_dir

let exists_modtype sp = MPTab.exists sp !the_modtypetab

let exists_tactic kn = KnTab.exists kn !the_tactictab

(* Reverse locate functions ***********************************************)

let path_of_global ref =
  match ref with
    | VarRef id -> make_path DirPath.empty id
    | _ -> Globrevtab.find (TrueGlobal ref) !the_globrevtab

let dirpath_of_global ref =
  fst (repr_path (path_of_global ref))

let basename_of_global ref =
  snd (repr_path (path_of_global ref))

let path_of_syndef kn =
  Globrevtab.find (SynDef kn) !the_globrevtab

let dirpath_of_module mp =
  MPmap.find mp !the_modrevtab

let path_of_tactic kn =
  KNmap.find kn !the_tacticrevtab

let path_of_modtype mp =
  MPmap.find mp !the_modtyperevtab

(* Shortest qualid functions **********************************************)

let shortest_qualid_of_global ctx ref =
  match ref with
    | VarRef id -> make_qualid DirPath.empty id
    | _ ->
        let sp = Globrevtab.find (TrueGlobal ref) !the_globrevtab in
        ExtRefTab.shortest_qualid ctx sp !the_ccitab

let shortest_qualid_of_syndef ctx kn =
  let sp = path_of_syndef kn in
    ExtRefTab.shortest_qualid ctx sp !the_ccitab

let shortest_qualid_of_module mp =
  let dir = MPmap.find mp !the_modrevtab in
    DirTab.shortest_qualid Id.Set.empty dir !the_dirtab

let shortest_qualid_of_modtype kn =
  let sp = MPmap.find kn !the_modtyperevtab in
    MPTab.shortest_qualid Id.Set.empty sp !the_modtypetab

let shortest_qualid_of_tactic kn =
  let sp = KNmap.find kn !the_tacticrevtab in
    KnTab.shortest_qualid Id.Set.empty sp !the_tactictab

let pr_global_env env ref =
  try str (string_of_qualid (shortest_qualid_of_global env ref))
  with Not_found as e -> prerr_endline "pr_global_env not found"; raise e

let global_inductive r =
  match global r with
  | IndRef ind -> ind
  | ref ->
      user_err_loc (loc_of_reference r,"global_inductive",
        pr_reference r ++ spc () ++ str "is not an inductive type")


(********************************************************************)

(********************************************************************)
(* Registration of tables as a global table and rollback            *)

type frozen = ccitab * dirtab * mptab * kntab
    * globrevtab * mprevtab * mptrevtab * knrevtab

let freeze _ : frozen =
  !the_ccitab,
  !the_dirtab,
  !the_modtypetab,
  !the_tactictab,
  !the_globrevtab,
  !the_modrevtab,
  !the_modtyperevtab,
  !the_tacticrevtab

let unfreeze (ccit,dirt,mtyt,tact,globr,modr,mtyr,tacr) =
  the_ccitab := ccit;
  the_dirtab := dirt;
  the_modtypetab := mtyt;
  the_tactictab := tact;
  the_globrevtab := globr;
  the_modrevtab := modr;
  the_modtyperevtab := mtyr;
  the_tacticrevtab := tacr

let _ =
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = Summary.nop }

(* Deprecated synonyms *)

let extended_locate = locate_extended
let absolute_reference = global_of_path
