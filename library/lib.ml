(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Identifier
open Names
open Libnames
open Libobject
open Summary

type node = 
  | Leaf of obj
  | CompUnit of dir_path
  | OpenedModule of module_ident * Summary.frozen
  | OpenedModtype of module_ident * Summary.frozen
  | OpenedSection of module_ident * Summary.frozen
  (* bool is to tell if the section must be opened automatically *)
  | ClosedSection of bool * module_ident * library_segment
  | FrozenState of Summary.frozen

and library_entry = section_path * node

and library_segment = library_entry list


let rec iter_leaves f seg =
  match seg with
    | [] -> ()
    | (sp,Leaf obj)::segtl ->
	f (sp,obj);
	iter_leaves f segtl
    | _ -> anomaly "We should have leaves only here"


let open_segment = iter_leaves open_object

let load_segment = iter_leaves load_object


let rec subst_segment subst seg =
  match seg with
    | [] -> []
    | (sp,Leaf obj)::segtl -> 
	let obj' = subst_object subst obj in
	let segtl' = subst_segment subst segtl in
	  if obj'==obj && segtl'==segtl then 
	    seg
	  else 
	    (sp,Leaf obj')::segtl'
    | _ -> anomaly "We should have leaves only here"

(* We keep trace of operations in the stack [lib_stk]. 
   [path_prefix] is the current path of sections, where sections are stored in 
   ``correct'' order, the oldest coming first in the list. It may seems 
   costly, but in practice there is not so many openings and closings of
   sections, but on the contrary there are many constructions of section
   paths based on the library path. *) 

let lib_stk = ref ([] : (section_path * node) list)

let default_module = make_dirpath [id_of_string "Scratch"]
let comp_name = ref None
let path_prefix = ref (default_module : dir_path)

let module_sp () =
  match !comp_name with Some m -> m | None -> default_module

let recalc_path_prefix () =
  let rec recalc = function
    | (sp, OpenedSection (modid,_)) :: _  -> (dirpath sp)@[modid]
    | (sp, OpenedModule (modid,_)) :: _  -> (dirpath sp)@[modid]
    | (sp, OpenedModtype (modid,_)) :: _ -> (dirpath sp)@[modid]
    | _::l -> recalc l
    | [] -> module_sp ()
  in
  path_prefix := recalc !lib_stk

let pop_path_prefix () =
  let rec pop = function
    | [] -> assert false
    | [_] -> []
    | s::l -> s :: (pop l)
  in
  path_prefix := pop !path_prefix

let make_path id k = Libnames.make_path !path_prefix id k

let cwd () = !path_prefix

let find_entry_p p = 
  let rec find = function
    | [] -> raise Not_found
    | ent::l -> if p ent then ent else find l
  in
  find !lib_stk

let split_lib sp = 
  let rec collect after equal = function
    | ((sp',_) as hd)::before ->
      	if sp = sp' then collect after (hd::equal) before else after,equal,hd::before
    | [] -> after,equal,[]
  in
  let rec findeq after = function
    | ((sp',_) as hd)::before ->
      	if sp = sp' then collect after [hd] before else findeq (hd::after) before
    | [] -> error "no such entry"
  in 
  findeq [] !lib_stk

(* Adding operations. *)

let add_entry sp node =
  lib_stk := (sp,node) :: !lib_stk

let anonymous_id = 
  let n = ref 0 in
  fun () -> incr n; id_of_string ("_" ^ (string_of_int !n))

let add_anonymous_entry node =
  let sp = make_path (anonymous_id()) OBJ in
  add_entry sp node;
  sp

let add_leaf id kind obj =
  let sp = make_path id kind in
  cache_object (sp,obj);
  add_entry sp (Leaf obj);
  sp

let add_leaves stack id kind obj =
  let sp = make_path id kind in
  load_segment stack;
  List.iter (function (_,Leaf obj) -> add_entry sp (Leaf obj) 
	       | _ -> anomaly "Only leaves expected in add_leaves")
    stack;
  cache_object (sp,obj);
  add_entry sp (Leaf obj);
  sp

let add_anonymous_leaf obj =
  let sp = make_path (anonymous_id()) OBJ in
  cache_object (sp,obj);
  add_entry sp (Leaf obj)

let add_frozen_state () =
  let _ = add_anonymous_entry (FrozenState (freeze_summaries())) in ()

let contents_after = function
  | None -> !lib_stk
  | Some sp -> let (after,_,_) = split_lib sp in after

(* Modules. *)

let is_something_opened = function 
    (_,OpenedSection _) -> true 
  | (_,OpenedModule _) -> true
  | (_,OpenedModtype _) -> true
  | _ -> false

(* b is ignored for now. It is supposed for Keep true and Keep false
discrimination *)
let classify_segment b seg =
  let rec clean ((substl,keepl,anticipl) as acc) = function
    | (_,CompUnit _) :: _ | [] -> acc
    | (sp,Leaf o) as node :: stk -> 
	(match classify_object (sp,o) with 
	   | Dispose -> clean acc stk
	   | Keep (_,o') -> 
	       clean (substl, (sp,Leaf o')::keepl, anticipl) stk
	   | Substitute o' -> 
	       clean ((sp,Leaf o')::substl, keepl, anticipl) stk
	   | Anticipate o' ->
	       clean (substl, keepl, (sp,Leaf o')::anticipl) stk)
    | (sp,ClosedSection _ as item) :: stk -> clean acc stk
    | (_,OpenedSection _) :: _ -> error "there are still opened sections"
    | (_,OpenedModule _) :: _ -> error "there are still opened modules"
    | (_,OpenedModtype _) :: _ -> error "there are still opened module types"
    | (_,FrozenState _) :: stk -> clean acc stk
  in
  clean ([],[],[]) seg

let export_segment seg =
  let rec clean acc = function
    | (_,CompUnit _) :: _ | [] -> acc
    | (sp,Leaf o) as node :: stk ->
	(match export_object o with
	   | None -> clean acc stk
	   | Some o' -> clean ((sp,Leaf o') :: acc) stk)
    | (sp,ClosedSection _ as item) :: stk -> clean (item :: acc) stk
    | (_,OpenedSection _) :: _ -> error "there are still opened sections"
    | (_,OpenedModule _) :: _ -> error "there are still opened modules"
    | (_,OpenedModtype _) :: _ -> error "there are still opened module types"
    | (_,FrozenState _) :: stk -> clean acc stk
  in
    clean [] seg

let begin_module id nametab = 
  let dir = !path_prefix @ [id] in
  let sp = make_path id CCI in
  if Nametab.exists_module dir then
    errorlabstrm "open_module" (pr_id id ++ str " already exists") ;
  add_entry sp (OpenedModule (id,nametab));
  path_prefix := dir;
  sp
 
let end_module id = 
  let sp,nametab = 
    try match find_entry_p is_something_opened with
      | sp,OpenedModule (id',nametab) -> 
	  if id<>id' then error "this is not the last opened module"; 
	  sp,nametab
      | _,OpenedModtype _ ->
	  error "there are some open module types"
      | _,OpenedSection _ ->
	  error "there are some open sections"
      | _ -> assert false
    with Not_found ->
      error "no opened modules"
  in
  let (after,_,before) = split_lib sp in
  lib_stk := before;
  let substitute, keep, special = classify_segment false after in
  let dir = !path_prefix in
  pop_path_prefix ();
(*  add_entry sp (ClosedModule id);*)
  (* add_frozen_state must be called after processing the module, 
     because we cannot recache Interactive Modules  *) 
  (sp,dir,nametab,substitute,keep,special)

let begin_modtype id nametab = 
  let dir = !path_prefix @ [id] in
  let sp = make_path id CCI in
  if Nametab.exists_cci sp then
    errorlabstrm "open_modtype" (pr_id id ++ str " already exists") ;
  add_entry sp (OpenedModtype (id,nametab));
  add_frozen_state ();
  path_prefix := dir;
  sp
 
let end_modtype id = 
  let sp,nametab = 
    try match find_entry_p is_something_opened with
      | sp,OpenedModtype (id',nametab) -> 
	  if id<>id' then error "this is not the last opened module"; 
	  sp,nametab
      | _,OpenedModule _ ->
	  error "there are some open modules"
      | _,OpenedSection _ ->
	  error "there are some open sections"
      | _ -> assert false
    with Not_found ->
      error "no opened module types"
  in
  let (after,_,before) = split_lib sp in
  lib_stk := before;
  let substitute,_,special = classify_segment false after in
  let dir = !path_prefix in
  pop_path_prefix ();
(*  add_entry sp (ClosedModtype id);*)
  (* add_frozen_state must be called after storing [after']
     This is because we cannot recache ClosedModule  *) 
  (sp,dir,nametab,substitute,special)


(* Sections. *)

let open_section id =
  let dir = !path_prefix @ [id] in
  let sp = make_path id OBJ in
  if Nametab.exists_section dir then
    errorlabstrm "open_section" (pr_id id ++ str " already exists") ;
  add_entry sp (OpenedSection (id, freeze_summaries()));
  path_prefix := dir;
  sp

let check_for_comp_unit () =
  let is_decl = function (_,FrozenState _) -> false | _ -> true in
  try
    let _ = find_entry_p is_decl in
    error "a module can not be started after some declarations"
  with Not_found -> ()

let start_comp_unit s =
  if !comp_name <> None then
    error "compilation unit is already started";
  if !path_prefix <> default_module then
    error "some sections are already opened";
  comp_name := Some s;
  (match split_dirpath s with [],id -> Nametab.push_library_root id | _ -> ());
  Univ.set_module (MPcomp s);
  let _ = add_anonymous_entry (CompUnit s) in
  path_prefix := s

let comp_unit_name s =
  match !comp_name with
    | None -> error "no module declared"
    | Some m ->
	let bm = snd (split_dirpath m) in
	if bm <> s then
	  error ("The current open module has basename "^(string_of_id bm));
	m

let sections_are_opened () =
  try 
    match find_entry_p is_something_opened with
      | (_,OpenedSection _) -> true
      | (_,OpenedModule _) -> false
      | _ -> false
  with Not_found -> false

let close_section export id =
  let sp,fs = 
    try match find_entry_p is_something_opened with
      | sp,OpenedSection (id',fs) -> 
	  if id<>id' then error "this is not the last opened section"; (sp,fs)
      | _,OpenedModule _ ->
	  error "there are some open modules"
      | _ -> assert false
    with Not_found ->
      error "no opened section"
  in
  let (after,_,before) = split_lib sp in
  lib_stk := before;
  let after' = export_segment after in
  pop_path_prefix ();
  add_entry (make_path id OBJ) (ClosedSection (export, id, after'));
  (sp,after,fs)

(* The following function exports the whole library segment, that will be 
   saved as a module. Objects are presented in chronological order, and
   frozen states are removed. *)

let export_comp_unit s =
  let substitute, keep, _ = classify_segment true !lib_stk in
    substitute, keep

(* Backtracking. *)

let recache_decl = function
  | (sp, Leaf o) -> cache_object (sp,o)
  | _ -> ()

let recache_context ctx =
  List.iter recache_decl ctx


let is_frozen_state = function (_,FrozenState _) -> true | _ -> false

let reset_to sp =
  let (_,_,before) = split_lib sp in
  lib_stk := before;
  recalc_path_prefix ();
  let spf = match find_entry_p is_frozen_state with
    | (sp, FrozenState f) -> unfreeze_summaries f; sp
    | _ -> assert false
  in
  let (after,_,_) = split_lib spf in
  recache_context after

let reset_name id =
  let (sp,_) = 
    try
      find_entry_p (fun (sp,_) -> id = basename sp)
    with Not_found ->
      error (string_of_id id ^ ": no such entry")
  in
  reset_to sp

(* [dir] is a section dir if [module] < [dir] <= [path_prefix] *)
let is_section_p sp =
  not (is_dirpath_prefix_of sp (module_sp ()))
  & (is_dirpath_prefix_of sp !path_prefix)

(* State and initialization. *)

type frozen = dir_path option * library_segment

let freeze () = (!comp_name, !lib_stk)

let unfreeze (mn,stk) =
  comp_name := mn;
  lib_stk := stk;
  recalc_path_prefix ()

let init () =
  lib_stk := [];
  add_frozen_state ();
  comp_name := None;
  path_prefix := default_module;
  init_summaries()

(* Initial state. *)

let initial_state = ref (None : section_path option)

let declare_initial_state () = 
  let sp = add_anonymous_entry (FrozenState (freeze_summaries())) in
  initial_state := Some sp

let reset_initial () =
  match !initial_state with
    | None -> init ()
    | Some sp -> 
  	begin match split_lib sp with
	  | (_,[_,FrozenState fs as hd],before) ->
	      lib_stk := hd::before;
	      recalc_path_prefix ();
	      comp_name:=None;
	      unfreeze_summaries fs
	  | _ -> assert false
	end


