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

type 'a path_status = Nothing | Relative of 'a | Absolute of 'a

(* Dictionaries of short names *)
type 'a nametree = ('a path_status * 'a nametree ModIdmap.t)
type ccitab = extended_global_reference nametree Idmap.t
type kntab = kernel_name nametree Idmap.t
type objtab = section_path nametree Idmap.t
type dirtab = global_dir_reference nametree ModIdmap.t

let the_ccitab = ref (Idmap.empty : ccitab)
let the_dirtab = ref (ModIdmap.empty : dirtab)
let the_objtab = ref (Idmap.empty : objtab)
let the_modtypetab = ref (Idmap.empty : kntab)

(* This table translates extended_global_references back to section paths *)
module Globtab = Map.Make(struct type t=extended_global_reference 
				 let compare = compare end)

type globtab = section_path Globtab.t

let the_globtab = ref (Globtab.empty : globtab)


let sp_of_global ctx_opt ref = 
  match (ctx_opt,ref) with
    | Some ctx, VarRef id -> 
	let _ = Sign.lookup_named id ctx in
	  make_path empty_dirpath id
    | _ -> Globtab.find (TrueGlobal ref) !the_globtab


let full_name = sp_of_global None

let id_of_global ctx_opt ref = 
  let (_,id) = repr_path (sp_of_global ctx_opt ref) in 
  id

let sp_of_syntactic_definition kn = 
  Globtab.find (SyntacticDef kn) !the_globtab

(******************************************************************)
(* the_dirpath is the table matching dir_paths to toplevel
   modules/files or sections

   If we have a closed module M having a submodule N, than N does not
   have the entry here.

*)

type visibility = Until of int | Exactly of int

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
		  warning "Trying to zaslonic an absolute name!"; current
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
	      error "Trying to zaslonic an absolute name!"
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
		    error "Trying to zaslonic an absolute name!"
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


(* These are entry points for new declarations at toplevel *)

(* This is for permanent constructions (never discharged -- but with
   possibly limited visibility, i.e. Theorem, Lemma, Definition, Axiom,
   Parameter but also Remark and Fact) *)

let push_xref visibility sp xref =
  push_idtree the_ccitab visibility sp xref;
  match visibility with
    | Until _ -> 
	the_globtab := Globtab.add xref sp !the_globtab
    | _ -> ()

let push_cci visibility sp ref =
  push_xref visibility sp (TrueGlobal ref)

(* This is for Syntactic Definitions *)
let push_syntactic_definition visibility sp kn =
  push_xref visibility sp (SyntacticDef kn)

let push = push_cci

let push_modtype = push_idtree the_modtypetab


(* This is for dischargeable non-cci objects (removed at the end of the
   section -- i.e. Hints, Grammar ...) *) (* --> Unused *)

let push_object visibility sp =
  push_idtree the_objtab visibility sp sp

(* This is for tactic definition names *)

let push_tactic = push_object

(* This is to remember absolute Section/Module names and to avoid redundancy *)
let push_dir = push_modidtree the_dirtab


(* As before we start with generic functions *)

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


(* These are entry points to locate different things *)
let find_cci = find_in_idtree the_ccitab

let find_dir = find_in_modidtree the_dirtab

let find_modtype = find_in_idtree the_modtypetab

(* This should be used when syntactic definitions are allowed *)
let extended_locate qid = get (find_cci qid)

(* This should be used when no syntactic definitions is expected *)
let locate qid = match extended_locate qid with
  | TrueGlobal ref -> ref
  | SyntacticDef _ -> raise Not_found

let locate_syntactic_definition qid = match extended_locate qid with
  | TrueGlobal _ -> raise Not_found
  | SyntacticDef kn -> kn

let locate_modtype qid = get (find_modtype qid)

let locate_obj qid = get (find_in_idtree the_objtab qid)

let locate_tactic qid = get (find_in_idtree the_objtab qid)

let locate_dir qid = get (find_dir qid)

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
  match find_cci (qualid_of_sp sp) with
    | Absolute (TrueGlobal ref) -> ref
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

let exists_cci sp =
  try 
    absolute (find_cci (qualid_of_sp sp))
  with Not_found -> false
      
let exists_dir dir =
  try 
    absolute (find_dir (qualid_of_dirpath dir))
  with Not_found -> false

let exists_section = exists_dir

let exists_module = exists_dir

let exists_modtype sp = 
  try 
    absolute (find_modtype (qualid_of_sp sp))
  with Not_found -> false

(* For a sp Coq.A.B.x, try to find the shortest among x, B.x, A.B.x
   and Coq.A.B.x is a qualid that denotes the same object. *)
let shortest_qualid_of_global env ref =  
  let sp = sp_of_global env ref in
  let (pth,id) = repr_path sp in
  let rec find_visible dir qdir =
    let qid = make_qualid qdir id in
    if (try locate qid = ref with Not_found -> false) then qid
    else match dir with
      | [] -> qualid_of_sp sp
      | a::l -> find_visible l (add_dirpath_prefix a qdir)
  in
  find_visible (repr_dirpath pth) (make_dirpath [])

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

type frozen = ccitab * dirtab * objtab * globtab

let init () = 
  the_ccitab := Idmap.empty; 
  the_dirtab := ModIdmap.empty;
  the_objtab := Idmap.empty;
  the_globtab := Globtab.empty

let freeze () =
  !the_ccitab, 
  !the_dirtab,
  !the_objtab,
  !the_globtab

let unfreeze (mc,md,mo,gt) =
  the_ccitab := mc;
  the_dirtab := md;
  the_objtab := mo;
  the_globtab := gt

let _ = 
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }

