(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Libnames
open Nameops
open Declarations


exception GlobalizationError of qualid
exception GlobalizationConstantError of qualid

let error_global_not_found_loc loc q =
  Stdpp.raise_with_loc loc (GlobalizationError q)

let error_global_constant_not_found_loc loc q =
  Stdpp.raise_with_loc loc (GlobalizationConstantError q)

let error_global_not_found q = raise (GlobalizationError q)



(* The visibility can be registered either 
   - for all suffixes not shorter then a given int - when the object
     is loaded inside a module
   or
   - for a precise suffix, when the module containing (the module
     containing ...) the object is open (imported) 
*)
type visibility = Until of int | Exactly of int


(* Data structure for nametabs *******************************************)


(* This module type will be instantiated by [section_path] of [dir_path] *)
(* The [repr] function is assumed to return the reversed list of idents. *)
module type UserName = sig 
  type t
  val to_string : t -> string
  val repr : t -> identifier * module_ident list
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
  type 'a t
  type user_name
  
  val empty : 'a t
  val push : visibility -> user_name -> 'a -> 'a t -> 'a t
  val locate : qualid -> 'a t -> 'a
  val find : user_name -> 'a t -> 'a
  val exists : user_name -> 'a t -> bool
  val user_name : qualid -> 'a t -> user_name
  val shortest_qualid : Idset.t -> user_name -> 'a t -> qualid
  val find_prefixes : qualid -> 'a t -> 'a list
end

module Make(U:UserName) : NAMETREE with type user_name = U.t 
				     = 
struct

  type user_name = U.t

  type 'a path_status = 
      Nothing 
    | Relative of user_name * 'a 
    | Absolute of user_name * 'a

  (* Dictionaries of short names *)
  type 'a nametree = ('a path_status * 'a nametree ModIdmap.t)

  type 'a t = 'a nametree Idmap.t

  let empty = Idmap.empty
		
  (* [push_until] is used to register [Until vis] visibility and 
     [push_exactly] to [Exactly vis] and [push_tree] chooses the right one*)

  let rec push_until uname o level (current,dirmap) = function
    | modid :: path ->
	let mc = 
	  try ModIdmap.find modid dirmap
	  with Not_found -> (Nothing, ModIdmap.empty)
	in
	let this =
          if level <= 0 then
	    match current with
	      | Absolute (n,_) -> 
		  (* This is an absolute name, we must keep it 
		     otherwise it may become unaccessible forever *)
		  Flags.if_verbose
		    warning ("Trying to mask the absolute name \"" 
			     ^ U.to_string n ^ "\"!"); 
		  current
	      | Nothing
	      | Relative _ -> Relative (uname,o)
          else current 
	in
	let ptab' = push_until uname o (level-1) mc path in
	  (this, ModIdmap.add modid ptab' dirmap)
    | [] -> 
	match current with
	  | Absolute (uname',o') -> 
	      if o'=o then begin
		assert (uname=uname');
		current, dirmap 
		  (* we are putting the same thing for the second time :) *)
	      end
	      else
		(* This is an absolute name, we must keep it otherwise it may
		   become unaccessible forever *)
		(* But ours is also absolute! This is an error! *)
		error ("Cannot mask the absolute name \""
  		       ^ U.to_string uname' ^ "\"!")
	  | Nothing
	  | Relative _ -> Absolute (uname,o), dirmap


let rec push_exactly uname o level (current,dirmap) = function
  | modid :: path ->
      let mc = 
	try ModIdmap.find modid dirmap
	with Not_found -> (Nothing, ModIdmap.empty)
      in
        if level = 0 then
	  let this =
	    match current with
	      | Absolute (n,_) -> 
		  (* This is an absolute name, we must keep it 
		     otherwise it may become unaccessible forever *)
		  Flags.if_verbose
		    warning ("Trying to mask the absolute name \""
  			     ^ U.to_string n ^ "\"!");
		  current
	      | Nothing
	      | Relative _ -> Relative (uname,o)
	  in
	    (this, dirmap)
	else (* not right level *)
	  let ptab' = push_exactly uname o (level-1) mc path in
	    (current, ModIdmap.add modid ptab' dirmap)
  | [] -> 
      anomaly "Prefix longer than path! Impossible!"


let push visibility uname o tab =
  let id,dir = U.repr uname in
  let ptab =
    try Idmap.find id tab
    with Not_found -> (Nothing, ModIdmap.empty) 
  in
  let ptab' = match visibility with
    | Until i -> push_until uname o (i-1) ptab dir
    | Exactly i -> push_exactly uname o (i-1) ptab dir
  in
    Idmap.add id ptab' tab


let rec search (current,modidtab) = function
  | modid :: path -> search (ModIdmap.find modid modidtab) path
  | [] -> current
      
let find_node qid tab =
  let (dir,id) = repr_qualid qid in
    search (Idmap.find id tab) (repr_dirpath dir)

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
    match search (Idmap.find id tab) l with
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
  let hidden = Idset.mem id ctx in
  let rec find_uname pos dir (path,tab) = match path with
    | Absolute (u,_) | Relative (u,_)
          when u=uname && not(pos=[] && hidden) -> List.rev pos
    | _ -> 
	match dir with 
	    [] -> raise Not_found
	  | id::dir -> find_uname (id::pos) dir (ModIdmap.find id tab)
  in
  let ptab = Idmap.find id tab in
  let found_dir = find_uname [] dir ptab in
    make_qualid (make_dirpath found_dir) id

let push_node node l =
  match node with
  | Absolute (_,o) | Relative (_,o) when not (List.mem o l) -> o::l
  | _ -> l

let rec flatten_idmap tab l =
  ModIdmap.fold (fun _ (current,idtab) l ->
    flatten_idmap idtab (push_node current l)) tab l

let rec search_prefixes (current,modidtab) = function
  | modid :: path -> search_prefixes (ModIdmap.find modid modidtab) path
  | [] -> List.rev (flatten_idmap  modidtab (push_node current []))
      
let find_prefixes qid tab =
  try
    let (dir,id) = repr_qualid qid in
    search_prefixes (Idmap.find id tab) (repr_dirpath dir)
  with Not_found -> []

end



(* Global name tables *************************************************)

module SpTab = Make (struct 
		       type t = section_path
		       let to_string = string_of_path
		       let repr sp = 
			 let dir,id = repr_path sp in
			   id, (repr_dirpath dir)
		     end)


type ccitab = extended_global_reference SpTab.t
let the_ccitab = ref (SpTab.empty : ccitab)

type kntab = kernel_name SpTab.t
let the_modtypetab = ref (SpTab.empty : kntab)
let the_tactictab = ref (SpTab.empty : kntab)

type objtab = unit SpTab.t
let the_objtab = ref (SpTab.empty : objtab)


module DirTab = Make(struct 
		       type t = dir_path
		       let to_string = string_of_dirpath
		       let repr dir = match repr_dirpath dir with
			 | [] -> anomaly "Empty dirpath"
			 | id::l -> (id,l)
		     end)

(* If we have a (closed) module M having a submodule N, than N does not
   have the entry in [the_dirtab]. *)
type dirtab = global_dir_reference DirTab.t
let the_dirtab = ref (DirTab.empty : dirtab)


(* Reversed name tables ***************************************************)

(* This table translates extended_global_references back to section paths *)
module Globrevtab = Map.Make(struct 
			       type t=extended_global_reference 
			       let compare = compare 
			     end)

type globrevtab = section_path Globrevtab.t
let the_globrevtab = ref (Globrevtab.empty : globrevtab)


type mprevtab = dir_path MPmap.t
let the_modrevtab = ref (MPmap.empty : mprevtab)

type knrevtab = section_path KNmap.t
let the_modtyperevtab = ref (KNmap.empty : knrevtab)
let the_tacticrevtab = ref (KNmap.empty : knrevtab)


(* Push functions *********************************************************)

(* This is for permanent constructions (never discharged -- but with
   possibly limited visibility, i.e. Theorem, Lemma, Definition, Axiom,
   Parameter but also Remark and Fact) *)

let push_xref visibility sp xref =
  the_ccitab := SpTab.push visibility sp xref !the_ccitab;
  match visibility with
    | Until _ -> 
	the_globrevtab := Globrevtab.add xref sp !the_globrevtab
    | _ -> ()

let push_cci visibility sp ref =
  push_xref visibility sp (TrueGlobal ref)

(* This is for Syntactic Definitions *)
let push_syntactic_definition visibility sp kn =
  push_xref visibility sp (SyntacticDef kn)

let push = push_cci

let push_modtype vis sp kn = 
  the_modtypetab := SpTab.push vis sp kn !the_modtypetab;
  the_modtyperevtab := KNmap.add kn sp !the_modtyperevtab

(* This is for tactic definition names *)

let push_tactic vis sp kn = 
  the_tactictab := SpTab.push vis sp kn !the_tactictab;
  the_tacticrevtab := KNmap.add kn sp !the_tacticrevtab


(* This is for dischargeable non-cci objects (removed at the end of the
   section -- i.e. Hints, Grammar ...) *) (* --> Unused *)

let push_object visibility sp =
  the_objtab := SpTab.push visibility sp () !the_objtab

(* This is to remember absolute Section/Module names and to avoid redundancy *)
let push_dir vis dir dir_ref = 
  the_dirtab := DirTab.push vis dir dir_ref !the_dirtab;
  match dir_ref with
      DirModule (_,(mp,_)) -> the_modrevtab := MPmap.add mp dir !the_modrevtab
    | _ -> ()


(* Locate functions *******************************************************)


(* This should be used when syntactic definitions are allowed *)
let extended_locate qid = SpTab.locate qid !the_ccitab

(* This should be used when no syntactic definitions is expected *)
let locate qid = match extended_locate qid with
  | TrueGlobal ref -> ref
  | SyntacticDef _ -> raise Not_found
let full_name_cci qid = SpTab.user_name qid !the_ccitab

let locate_syntactic_definition qid = match extended_locate qid with
  | TrueGlobal _ -> raise Not_found
  | SyntacticDef kn -> kn

let locate_modtype qid = SpTab.locate qid !the_modtypetab
let full_name_modtype qid = SpTab.user_name qid !the_modtypetab

let locate_obj qid = SpTab.user_name qid !the_objtab

type ltac_constant = kernel_name
let locate_tactic qid = SpTab.locate qid !the_tactictab
let full_name_tactic qid = SpTab.user_name qid !the_tactictab

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
    (SpTab.find_prefixes qid !the_ccitab) []

let extended_locate_all qid = SpTab.find_prefixes qid !the_ccitab

(* Derived functions *)

let locate_constant qid =
  match extended_locate qid with
    | TrueGlobal (ConstRef kn) -> kn
    | _ -> raise Not_found

let locate_mind qid = 
  match extended_locate qid with
    | TrueGlobal (IndRef (kn,0)) -> kn
    | _ -> raise Not_found


let absolute_reference sp =
  match SpTab.find sp !the_ccitab with
    | TrueGlobal ref -> ref
    | _ -> raise Not_found

let locate_in_absolute_module dir id =
  absolute_reference (make_path dir id)

let global r =
  let (loc,qid) = qualid_of_reference r in
  try match extended_locate qid with
    | TrueGlobal ref -> ref
    | SyntacticDef _ -> 
        user_err_loc (loc,"global",
          str "Unexpected reference to a notation: " ++
          pr_qualid qid)
  with Not_found ->
    error_global_not_found_loc loc qid

(* Exists functions ********************************************************)

let exists_cci sp = SpTab.exists sp !the_ccitab
      
let exists_dir dir = DirTab.exists dir !the_dirtab

let exists_section = exists_dir

let exists_module = exists_dir

let exists_modtype sp = SpTab.exists sp !the_modtypetab

let exists_tactic sp = SpTab.exists sp !the_tactictab

(* Reverse locate functions ***********************************************)

let sp_of_global ref = 
  match ref with
    | VarRef id -> make_path empty_dirpath id
    | _ -> Globrevtab.find (TrueGlobal ref) !the_globrevtab


let id_of_global ref = 
  let (_,id) = repr_path (sp_of_global ref) in 
  id

let sp_of_syntactic_definition kn = 
  Globrevtab.find (SyntacticDef kn) !the_globrevtab

let dir_of_mp mp =
  MPmap.find mp !the_modrevtab


(* Shortest qualid functions **********************************************)

let shortest_qualid_of_global ctx ref = 
  match ref with
    | VarRef id -> make_qualid empty_dirpath id
    | _ ->
        let sp = Globrevtab.find (TrueGlobal ref) !the_globrevtab in
        SpTab.shortest_qualid ctx sp !the_ccitab

let shortest_qualid_of_syndef ctx kn = 
  let sp = sp_of_syntactic_definition kn in
    SpTab.shortest_qualid ctx sp !the_ccitab

let shortest_qualid_of_module mp = 
  let dir = MPmap.find mp !the_modrevtab in
    DirTab.shortest_qualid Idset.empty dir !the_dirtab

let shortest_qualid_of_modtype kn =
  let sp = KNmap.find kn !the_modtyperevtab in
    SpTab.shortest_qualid Idset.empty sp !the_modtypetab

let shortest_qualid_of_tactic kn =
  let sp = KNmap.find kn !the_tacticrevtab in
    SpTab.shortest_qualid Idset.empty sp !the_tactictab

let pr_global_env env ref =
  (* Il est important de laisser le let-in, car les streams s'�valuent
  paresseusement : il faut forcer l'�valuation pour capturer
  l'�ventuelle lev�e d'une exception (le cas �choit dans le debugger) *)
  let s = string_of_qualid (shortest_qualid_of_global env ref) in
  (str s)

let inductive_of_reference r =
  match global r with
  | IndRef ind -> ind
  | ref ->
      user_err_loc (loc_of_reference r,"global_inductive",
        pr_reference r ++ spc () ++ str "is not an inductive type")

(********************************************************************)

(********************************************************************)
(* Registration of tables as a global table and rollback            *)

type frozen = ccitab * dirtab * objtab * kntab * kntab
    * globrevtab * mprevtab * knrevtab * knrevtab

let init () = 
  the_ccitab := SpTab.empty; 
  the_dirtab := DirTab.empty;
  the_objtab := SpTab.empty;
  the_modtypetab := SpTab.empty;
  the_tactictab := SpTab.empty;
  the_globrevtab := Globrevtab.empty;
  the_modrevtab := MPmap.empty;
  the_modtyperevtab := KNmap.empty;
  the_tacticrevtab := KNmap.empty


let freeze () =
  !the_ccitab, 
  !the_dirtab,
  !the_objtab,
  !the_modtypetab,
  !the_tactictab,
  !the_globrevtab,
  !the_modrevtab,
  !the_modtyperevtab,
  !the_tacticrevtab

let unfreeze (ccit,dirt,objt,mtyt,tact,globr,modr,mtyr,tacr) =
  the_ccitab := ccit;
  the_dirtab := dirt;
  the_objtab := objt;
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
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = false }
