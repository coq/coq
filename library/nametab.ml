(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

type visibility = Until of int | Exactly of int

(************************ Data structure for nametabs *********************)

module type UserName = sig 
  type t
  val to_string : t -> string
  val repr : t -> identifier * module_ident list
end

module type S = sig
  type 'a t
  type user_name
  
  val empty : 'a t
  val push : visibility -> user_name -> 'a -> 'a t -> 'a t
  val locate : qualid -> 'a t -> 'a
  val find : user_name -> 'a t -> 'a
  val exists : user_name -> 'a t -> bool
  val user_name : qualid -> 'a t -> user_name
  val shortest_qualid : user_name -> 'a t -> qualid
end

module Make(U:UserName) : S with type user_name = U.t 
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

  let push_many vis tab dir uname o = 
    let rec push level (current,dirmap) = function
      | modid :: path as dir ->
	  let mc = 
	    try ModIdmap.find modid dirmap
	    with Not_found -> (Nothing, ModIdmap.empty)
	  in
	  let this =
            if level >= vis then
	      match current with
		| Absolute (n,_) -> 
		    (* This is an absolute name, we must keep it otherwise it may
		       become unaccessible forever *)
		    warning ("Trying to mask the absolute name \"" 
			     ^ U.to_string n ^ "\"!"); 
		    current
		| Nothing
		| Relative _ -> Relative (uname,o)
            else current 
	  in
	    (this, ModIdmap.add modid (push (level+1) mc path) dirmap)
      | [] -> 
	  match current with
	    | Absolute (n,_) -> 
		(* This is an absolute name, we must keep it otherwise it may
		   become unaccessible forever *)
		(* But ours is also absolute! This is an error! *)
		error ("Trying to mask an absolute name \""
  		       ^ U.to_string n ^ "\"!")
	    | Nothing
	    | Relative _ -> Absolute (uname,o), dirmap
    in
      push 0 tab dir

let push_one vis tab dir uname o =
  let rec push level (current,dirmap) = function
    | modid :: path as dir ->
	let mc = 
	  try ModIdmap.find modid dirmap
	  with Not_found -> (Nothing, ModIdmap.empty)
	in
          if level = vis then
	    let this =
	      match current with
		| Absolute _ -> 
	(* This is an absolute name, we must keep it otherwise it may
           become unaccessible forever *)
		    error "Trying to mask an absolute name!"
		| Nothing
		| Relative _ -> Relative (uname,o)
	    in
	      (this, dirmap)
	  else
	    (current, ModIdmap.add modid (push (level+1) mc path) dirmap)
    | [] -> anomaly "We should never come to this point"
  in
    push 0 tab dir


let push_tree = function 
  | Until i -> push_many (i-1)
  | Exactly i -> push_one (i-1)


let push visibility uname o tab =
  let id,dir = U.repr uname in
  let modtab =
    try Idmap.find id tab
    with Not_found -> (Nothing, ModIdmap.empty) 
  in
    Idmap.add id (push_tree visibility modtab dir uname o) tab


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

let shortest_qualid uname tab = 
  let rec find_uname pos dir (path,tab) = match path with
    | Absolute (u,_) | Relative (u,_) when u=uname -> List.rev pos 
    | _ -> 
	match dir with 
	    [] -> raise Not_found
	  | id::dir -> find_uname (id::pos) dir (ModIdmap.find id tab)
  in
  let id,dir = U.repr uname in
  let ptab = Idmap.find id tab in
  let found_dir = find_uname [] dir ptab in
    make_qualid (make_dirpath found_dir) id
    

end
(******** End of nametab data structure ************************)

  
module DirTab = Make(struct 
		       type t = dir_path
		       let to_string = string_of_dirpath
		       let repr dir = match repr_dirpath dir with
			 | [] -> anomaly "Empty dirpath"
			 | id::l -> (id,l)
		     end)

module SpTab = Make (struct 
		       type t = section_path
		       let to_string = string_of_path
		       let repr sp = 
			 let dir,id = repr_path sp in
			   id, (repr_dirpath dir)
		     end)

type 'a path_status = Nothing | Relative of 'a | Absolute of 'a

(* Dictionaries of short names *)
type ccitab = extended_global_reference SpTab.t
type kntab = kernel_name SpTab.t
type objtab = unit SpTab.t
type dirtab = global_dir_reference DirTab.t

let the_ccitab = ref (SpTab.empty : ccitab)
let the_dirtab = ref (DirTab.empty : dirtab)
let the_objtab = ref (SpTab.empty : objtab)
let the_modtypetab = ref (SpTab.empty : kntab)

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


let sp_of_global ctx_opt ref = 
  match (ctx_opt,ref) with
    | Some ctx, VarRef id -> 
	let _ = Sign.lookup_named id ctx in
	  make_path empty_dirpath id
    | _ -> Globrevtab.find (TrueGlobal ref) !the_globrevtab


let full_name = sp_of_global None

let id_of_global ctx_opt ref = 
  let (_,id) = repr_path (sp_of_global ctx_opt ref) in 
  id

let sp_of_syntactic_definition kn = 
  Globrevtab.find (SyntacticDef kn) !the_globrevtab

(******************************************************************)
(* the_dirpath is the table matching dir_paths to toplevel
   modules/files or sections

   If we have a closed module M having a submodule N, than N does not
   have the entry here.

*)

(*
(* is the short name visible? tests for 1 *)
let is_short_visible v sp = match v with
    Until 1 | Exactly 1 -> true
  | _ -> false

(* In general, directories and sections are always open and modules
   (and files) are open on request only *)

(* We add a binding of ["modid1.....modidn.id"] to [o] in the table *)
(* Using the fact that the reprezentation of a [dir_path] is already
   reversed, we proceed in the reverse way, looking first for [id] *)

(* [push_many] is used to register [Until vis] visibility and 
   [push_one] to [Exactly vis] and [push_tree] chooses the right one*)

let push_many vis tab dir o = 
  let rec push level (current,dirmap) = function
    | modid :: path as dir ->
	let mc = 
	  try ModIdmap.find modid dirmap
	  with Not_found -> (Nothing, ModIdmap.empty)
	in
	let this =
          if level >= vis then
	    match current with
	      | Absolute _ -> 
            (* This is an absolute name, we must keep it otherwise it may
               become unaccessible forever *)
		  warning "Trying to mask an absolute name!"; current
	      | Nothing
	      | Relative _ -> Relative o
          else current 
	in
	  (this, ModIdmap.add modid (push (level+1) mc path) dirmap)
    | [] -> 
	match current with
	  | Absolute _ -> 
              (* This is an absolute name, we must keep it otherwise it may
		 become unaccessible forever *)
	      (* But ours is also absolute! This is an error! *)
	      error "Trying to mask an absolute name!"
	  | Nothing
	  | Relative _ -> Absolute o, dirmap
  in
    push 0 tab (repr_dirpath dir)

let push_one vis tab dir o =
  let rec push level (current,dirmap) = function
    | modid :: path as dir ->
	let mc = 
	  try ModIdmap.find modid dirmap
	  with Not_found -> (Nothing, ModIdmap.empty)
	in
          if level = vis then
	    let this =
	      match current with
		| Absolute _ -> 
	(* This is an absolute name, we must keep it otherwise it may
           become unaccessible forever *)
		    error "Trying to mask an absolute name!"
		| Nothing
		| Relative _ -> Relative o
	    in
	      (this, dirmap)
	  else
	    (current, ModIdmap.add modid (push (level+1) mc path) dirmap)
    | [] -> anomaly "We should never come to this point"
  in
    push 0 tab (repr_dirpath dir)


let push_tree = function 
  | Until i -> push_many (i-1)
  | Exactly i -> push_one (i-1)



let push_idtree tab visibility sp o =
  let dir,id = repr_path sp in
  let modtab =
    try Idmap.find id !tab
    with Not_found -> (Nothing, ModIdmap.empty) in
  tab := 
    Idmap.add id (push_tree visibility modtab dir o) !tab


let push_modidtree tab visibility dirpath o =
  let dir,id = split_dirpath dirpath in
  let modtab =
    try ModIdmap.find id !tab
    with Not_found -> (Nothing, ModIdmap.empty) in
  tab := ModIdmap.add id (push_tree visibility modtab dir o) !tab
*)



(* These are entry points for new declarations at toplevel *)

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


(* This is for dischargeable non-cci objects (removed at the end of the
   section -- i.e. Hints, Grammar ...) *) (* --> Unused *)

let push_object visibility sp =
  the_objtab := SpTab.push visibility sp () !the_objtab

(* This is for tactic definition names *)

let push_tactic = push_object

(* This is to remember absolute Section/Module names and to avoid redundancy *)
let push_dir vis dir dir_ref = 
  the_dirtab := DirTab.push vis dir dir_ref !the_dirtab;
  match dir_ref with
      DirModule (_,(mp,_)) -> the_modrevtab := MPmap.add mp dir !the_modrevtab
    | _ -> ()

(* As before we start with generic functions *)
(*
let find_in_tree tab dir =
  let rec search (current,modidtab) = function
    | modid :: path -> search (ModIdmap.find modid modidtab) path
    | [] -> current
  in
  search tab dir

let find_in_idtree tab qid =
  let (dir,id) = repr_qualid qid in
    find_in_tree (Idmap.find id !tab) (repr_dirpath dir)

let find_in_modidtree tab qid = 
  let (dir,id) = repr_qualid qid in
    find_in_tree (ModIdmap.find id !tab) (repr_dirpath dir)

let get = function
    Absolute o | Relative o -> o
  | Nothing -> raise Not_found                                            

let absolute = function
    Absolute _ -> true
  | Relative _ 
  | Nothing -> false
*)

(* These are entry points to locate different things *)

let find_dir qid = DirTab.locate qid !the_dirtab

(* This should be used when syntactic definitions are allowed *)
let extended_locate qid = SpTab.locate qid !the_ccitab

(* This should be used when no syntactic definitions is expected *)
let locate qid = match extended_locate qid with
  | TrueGlobal ref -> ref
  | SyntacticDef _ -> raise Not_found

let locate_syntactic_definition qid = match extended_locate qid with
  | TrueGlobal _ -> raise Not_found
  | SyntacticDef kn -> kn

let locate_modtype qid = SpTab.locate qid !the_modtypetab
let full_name_modtype qid = SpTab.user_name qid !the_modtypetab

let locate_obj qid = SpTab.user_name qid !the_objtab

let locate_tactic = locate_obj 

let locate_dir qid = DirTab.locate qid !the_dirtab

let locate_module qid = 
  match locate_dir qid with
    | DirModule (_,(mp,_)) -> mp
    | _ -> raise Not_found

let locate_loaded_library qid = 
  match locate_dir qid with
    | DirModule (dir,_) -> dir
    | _ -> raise Not_found

let locate_section qid =
  match locate_dir qid with
    | DirOpenSection (dir, _) 
    | DirClosedSection dir -> dir
    | _ -> raise Not_found

(* Derived functions *)

let locate_constant qid =
  match extended_locate qid with
    | TrueGlobal (ConstRef kn) -> kn
    | _ -> raise Not_found

let locate_mind qid = 
  match extended_locate qid with
    | TrueGlobal (IndRef (kn,0)) -> kn
    | _ -> raise Not_found

(*
let sp_of_id id = match locate_cci (make_short_qualid id) with
  | TrueGlobal ref -> ref
  | SyntacticDef _ ->
      anomaly ("sp_of_id: "^(string_of_id id)
	       ^" is not a true global reference but a syntactic definition")

let constant_sp_of_id id =
  match locate_cci (make_short_qualid id) with
    | TrueGlobal (ConstRef sp) -> sp
    | _ -> raise Not_found
*)

let absolute_reference sp =
  match SpTab.find sp !the_ccitab with
    | TrueGlobal ref -> ref
    | _ -> raise Not_found

let locate_in_absolute_module dir id =
  absolute_reference (make_path dir id)

let global (loc,qid) =
  try match extended_locate qid with
    | TrueGlobal ref -> ref
    | SyntacticDef _ -> 
        user_err_loc (loc,"global",
          str "Unexpected reference to a syntactic definition: " ++
          pr_qualid qid)
  with Not_found ->
    error_global_not_found_loc loc qid

let exists_cci sp = SpTab.exists sp !the_ccitab
      
let exists_dir dir = DirTab.exists dir !the_dirtab

let exists_section = exists_dir

let exists_module = exists_dir

let exists_modtype sp = SpTab.exists sp !the_modtypetab

(* For a sp Coq.A.B.x, try to find the shortest among x, B.x, A.B.x
   and Coq.A.B.x is a qualid that denotes the same object. *)
let shortest_qualid locate ref dir_path id =  
  let rec find_visible dir qdir =
    let qid = make_qualid qdir id in
    if (try locate qid = ref with Not_found -> false) then qid
    else match dir with
      | [] -> make_qualid dir_path id
      | a::l -> find_visible l (add_dirpath_prefix a qdir)
  in
  find_visible (repr_dirpath dir_path) empty_dirpath

let shortest_qualid_of_global env ref = 
  let sp = sp_of_global env ref in
  let (pth,id) = repr_path sp in
    shortest_qualid locate ref pth id

let shortest_qualid_of_module mp = 
  let dir = MPmap.find mp !the_modrevtab in
  let dir,id = split_dirpath dir in
    shortest_qualid locate_module mp dir id

let shortest_qualid_of_modtype kn =
  let sp = KNmap.find kn !the_modtyperevtab in
  let dir,id = repr_path sp in
    shortest_qualid locate_modtype kn dir id

let pr_global_env env ref =
  (* Il est important de laisser le let-in, car les streams s'évaluent
  paresseusement : il faut forcer l'évaluation pour capturer
  l'éventuelle levée d'une exception (le cas échoit dans le debugger) *)
  let s = string_of_qualid (shortest_qualid_of_global env ref) in
  (str s)

let global_inductive (loc,qid as locqid) =
  match global locqid with
  | IndRef ind -> ind
  | ref ->
      user_err_loc (loc,"global_inductive",
        pr_qualid qid ++ spc () ++ str "is not an inductive type")

(********************************************************************)

(********************************************************************)
(* Registration of tables as a global table and rollback            *)

type frozen = ccitab * dirtab * objtab * kntab 
    * globrevtab * mprevtab * knrevtab

let init () = 
  the_ccitab := SpTab.empty; 
  the_dirtab := DirTab.empty;
  the_objtab := SpTab.empty;
  the_modtypetab := SpTab.empty;
  the_globrevtab := Globrevtab.empty;
  the_modrevtab := MPmap.empty;
  the_modtyperevtab := KNmap.empty

let freeze () =
  !the_ccitab, 
  !the_dirtab,
  !the_objtab,
  !the_modtypetab,
  !the_globrevtab,
  !the_modrevtab,
  !the_modtyperevtab

let unfreeze (mc,md,mo,mt,gt,mrt,mtrt) =
  the_ccitab := mc;
  the_dirtab := md;
  the_objtab := mo;
  the_modtypetab := mt;
  the_globrevtab := gt;
  the_modrevtab := mrt;
  the_modtyperevtab := mtrt

let _ = 
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }

