(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Libnames
open Nameops
open Libobject
open Summary



type node = 
  | Leaf of obj
  | CompilingLibrary of object_prefix
  | OpenedModule of object_prefix * Summary.frozen
  | OpenedModtype of object_prefix * Summary.frozen
  | OpenedSection of object_prefix * Summary.frozen
  (* bool is to tell if the section must be opened automatically *)
  | ClosedSection of bool * dir_path * library_segment
  | FrozenState of Summary.frozen

and library_entry = object_name * node

and library_segment = library_entry list

type lib_objects =  (identifier * obj) list

let iter_objects f i prefix =
  List.iter (fun (id,obj) -> f i (make_oname prefix id, obj))

let load_objects = iter_objects load_object
let open_objects = iter_objects open_object

let subst_objects prefix subst seg = 
  let subst_one = fun (id,obj as node) ->
    let obj' = subst_object (make_oname prefix id, subst, obj) in
      if obj' == obj then node else
	(id, obj')
  in
    list_smartmap subst_one seg

let classify_segment seg =
  let rec clean ((substl,keepl,anticipl) as acc) = function
    | (_,CompilingLibrary _) :: _ | [] -> acc
    | ((sp,kn as oname),Leaf o) as node :: stk -> 
	let id = id_of_label (label kn) in
	  (match classify_object (oname,o) with 
	     | Dispose -> clean acc stk
	     | Keep o' -> 
		 clean (substl, (id,o')::keepl, anticipl) stk
	     | Substitute o' -> 
		 clean ((id,o')::substl, keepl, anticipl) stk
	     | Anticipate o' ->
		 clean (substl, keepl, o'::anticipl) stk)
    | (oname,ClosedSection _ as item) :: stk -> clean acc stk
    | (_,OpenedSection _) :: _ -> error "there are still opened sections"
    | (_,OpenedModule _) :: _ -> error "there are still opened modules"
    | (_,OpenedModtype _) :: _ -> error "there are still opened module types"
    | (_,FrozenState _) :: stk -> clean acc stk
  in
    clean ([],[],[]) (List.rev seg)


let segment_of_objects prefix =
  List.map (fun (id,obj) -> (make_oname prefix id, Leaf obj))

(* We keep trace of operations in the stack [lib_stk]. 
   [path_prefix] is the current path of sections, where sections are stored in 
   ``correct'' order, the oldest coming first in the list. It may seems 
   costly, but in practice there is not so many openings and closings of
   sections, but on the contrary there are many constructions of section
   paths based on the library path. *) 

let initial_prefix = default_library,(initial_path,empty_dirpath)

let lib_stk = ref ([] : library_segment)

let comp_name = ref None

let library_dp () =
  match !comp_name with Some m -> m | None -> default_library

(* [path_prefix] is a pair of absolute dirpath and a pair of current
   module path and relative section path *)
let path_prefix = ref initial_prefix


let cwd () = fst !path_prefix

let make_path id = Libnames.make_path (cwd ()) id


let current_prefix () = snd !path_prefix

let make_kn id = 
  let mp,dir = current_prefix () in
    Names.make_kn mp dir (label_of_id id)


let make_oname id = make_path id, make_kn id


let sections_depth () =
  List.length (repr_dirpath (snd (snd !path_prefix)))

let sections_are_opened () =
  match repr_dirpath (snd (snd !path_prefix)) with
      [] -> false
    | _ -> true


let recalc_path_prefix () =
  let rec recalc = function
    | (sp, OpenedSection (dir,_)) :: _ -> dir
    | (sp, OpenedModule (dir,_)) :: _ -> dir
    | (sp, OpenedModtype (dir,_)) :: _ -> dir
    | (sp, CompilingLibrary dir) :: _ -> dir
    | _::l -> recalc l
    | [] -> initial_prefix
  in
  path_prefix := recalc !lib_stk

let pop_path_prefix () = 
  let dir,(mp,sec) = !path_prefix in
    path_prefix := fst (split_dirpath dir), (mp, fst (split_dirpath sec))

let find_entry_p p = 
  let rec find = function
    | [] -> raise Not_found
    | ent::l -> if p ent then ent else find l
  in
  find !lib_stk

let find_split_p p = 
  let rec find = function
    | [] -> raise Not_found
    | ent::l -> if p ent then ent,l else find l
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
  let id = anonymous_id () in
  let name = make_oname id in
  add_entry name node;
  name

let add_absolutely_named_leaf sp obj =
  cache_object (sp,obj);
  add_entry sp (Leaf obj)

let add_leaf id obj =
  let oname = make_oname id in
  cache_object (oname,obj);
  add_entry oname (Leaf obj);
  oname

let add_leaves id objs =
  let oname = make_oname id in
  let add_obj obj = 
    add_entry oname (Leaf obj);
    load_object 1 (oname,obj) 
  in
  List.iter add_obj objs;
  oname

let add_anonymous_leaf obj =
  let id = anonymous_id () in
  let oname = make_oname id in
  cache_object (oname,obj);
  add_entry oname (Leaf obj)

let add_frozen_state () =
  let _ = add_anonymous_entry (FrozenState (freeze_summaries())) in ()

(* Modules. *)

let is_something_opened = function 
    (_,OpenedSection _) -> true 
  | (_,OpenedModule _) -> true
  | (_,OpenedModtype _) -> true
  | _ -> false

let export_segment seg =
  let rec clean acc = function
    | (_,CompilingLibrary _) :: _ | [] -> acc
    | (oname,Leaf o) as node :: stk ->
	(match export_object o with
	   | None -> clean acc stk
	   | Some o' -> clean ((oname,Leaf o') :: acc) stk)
    | (oname,ClosedSection _ as item) :: stk -> clean (item :: acc) stk
    | (_,OpenedSection _) :: _ -> error "there are still opened sections"
    | (_,OpenedModule _) :: _ -> error "there are still opened modules"
    | (_,OpenedModtype _) :: _ -> error "there are still opened module types"
    | (_,FrozenState _) :: stk -> clean acc stk
  in
    clean [] seg


let start_module id mp nametab = 
  let dir = extend_dirpath (fst !path_prefix) id in
  let prefix = dir,(mp,empty_dirpath) in
  let oname = make_path id, make_kn id in
  if Nametab.exists_module dir then
    errorlabstrm "open_module" (pr_id id ++ str " already exists") ;
  add_entry oname (OpenedModule (prefix,nametab));
  path_prefix := prefix;
  prefix
(*  add_frozen_state () must be called in declaremods *)
 
let end_module id = 
  let oname,nametab = 
    try match find_entry_p is_something_opened with
      | oname,OpenedModule (_,nametab) -> 
	  let sp = fst oname in
	  let id' = basename sp in
	  if id<>id' then error "this is not the last opened module"; 
	  oname,nametab
      | _,OpenedModtype _ ->
	  error "there are some open module types"
      | _,OpenedSection _ ->
	  error "there are some open sections"
      | _ -> assert false
    with Not_found ->
      error "no opened modules"
  in
  let (after,_,before) = split_lib oname in
  lib_stk := before;
  let prefix = !path_prefix in
  recalc_path_prefix ();
  (* add_frozen_state must be called after processing the module, 
     because we cannot recache interactive modules  *) 
  (oname, prefix, nametab,after)

let start_modtype id mp nametab = 
  let dir = extend_dirpath (fst !path_prefix) id in
  let prefix = dir,(mp,empty_dirpath) in
  let sp = make_path id in
  let name = sp, make_kn id in
  if Nametab.exists_cci sp then
    errorlabstrm "open_modtype" (pr_id id ++ str " already exists") ;
  add_entry name (OpenedModtype (prefix,nametab));
  path_prefix := prefix;
  prefix

let end_modtype id = 
  let sp,nametab = 
    try match find_entry_p is_something_opened with
      | sp,OpenedModtype (_,nametab) -> 
	  let id' = basename (fst sp) in
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
  let dir = !path_prefix in
  recalc_path_prefix ();
  (* add_frozen_state must be called after processing the module type.
     This is because we cannot recache interactive module types *) 
  (sp,dir,nametab,after)



let contents_after = function
  | None -> !lib_stk
  | Some sp -> let (after,_,_) = split_lib sp in after

(* Modules. *)

let check_for_comp_unit () =
  let is_decl = function (_,FrozenState _) -> false | _ -> true in
  try
    let _ = find_entry_p is_decl in
    error "a module cannot be started after some declarations"
  with Not_found -> ()

(* TODO: use check_for_module ? *)
let start_compilation s mp =
  if !comp_name <> None then
    error "compilation unit is already started";
  if snd (snd (!path_prefix)) <> empty_dirpath then
    error "some sections are already opened";
  let prefix = s, (mp, empty_dirpath) in
  let _ = add_anonymous_entry (CompilingLibrary prefix) in
  comp_name := Some s;
  path_prefix := prefix

let end_compilation dir =
  let _ =
    try match find_entry_p is_something_opened with
      | _, OpenedSection _ -> error "There are some open sections"
      | _, OpenedModule _ -> error "There are some open modules"
      | _, OpenedModtype _ -> error "There are some open module types"
      | _ -> assert false
    with
	Not_found -> ()
  in
  let module_p =
    function (_,CompilingLibrary _) -> true | x -> is_something_opened x
  in
  let oname = 
    try match find_entry_p module_p with
	(oname, CompilingLibrary prefix) -> oname
      | _ -> assert false
    with
	Not_found -> anomaly "No module declared"
  in
  let _ =  match !comp_name with
      | None -> anomaly "There should be a module name..."
      | Some m ->
	  if m <> dir then anomaly 
	    ("The current open module has name "^ (string_of_dirpath m) ^ 
	     " and not " ^ (string_of_dirpath m));
  in
  let (after,_,before) = split_lib oname in
  comp_name := None;
  !path_prefix,after

(* Returns true if we are inside an opened module type *)
let is_modtype () = 
  let opened_p = function
    | _, OpenedModtype _ -> true 
    | _ -> false
  in
    try 
      let _ = find_entry_p opened_p in true
    with
	Not_found -> false

(* Returns true if we are inside an opened module *)
let is_module () = 
  let opened_p = function
    | _, OpenedModule _ -> true 
    | _ -> false
  in
    try 
      let _ = find_entry_p opened_p in true
    with
	Not_found -> false


(* Returns the most recent OpenedThing node *)
let what_is_opened () = find_entry_p is_something_opened

(* XML output hooks *)
let xml_open_section = ref (fun id -> ())
let xml_close_section = ref (fun id -> ())

let set_xml_open_section f = xml_open_section := f
let set_xml_close_section f = xml_close_section := f

(* Sections. *)

let open_section id =
  let olddir,(mp,oldsec) = !path_prefix in
  let dir = extend_dirpath olddir id in
  let prefix = dir, (mp, extend_dirpath oldsec id) in
  let name = make_path id, make_kn id (* this makes little sense however *) in
  if Nametab.exists_section dir then
    errorlabstrm "open_section" (pr_id id ++ str " already exists");
  let sum = freeze_summaries() in
  add_entry name (OpenedSection (prefix, sum));
  (*Pushed for the lifetime of the section: removed by unfrozing the summary*)
  Nametab.push_dir (Nametab.Until 1) dir (DirOpenSection prefix);
  path_prefix := prefix;
  if !Options.xml_export then !xml_open_section id;
  prefix


(* Restore lib_stk and summaries as before the section opening, and
   add a ClosedSection object. *)
let close_section ~export id =
  let oname,fs = 
    try match find_entry_p is_something_opened with
      | oname,OpenedSection (_,fs) -> 
	  if id <> basename (fst oname) then
	    error "this is not the last opened section";
	  (oname,fs)
      | _ -> assert false 
    with Not_found ->
      error "no opened section"
  in
  let (after,_,before) = split_lib oname in
  lib_stk := before;
  let prefix = !path_prefix in
  pop_path_prefix ();
  let closed_sec = 
    ClosedSection (export, (fst prefix), export_segment after)
  in
  let name = make_path id, make_kn id in
  add_entry name closed_sec;
  if !Options.xml_export then !xml_close_section id;
  (prefix, after, fs)

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

let reset_name (loc,id) =
  let (sp,_) = 
    try
      find_entry_p (fun (sp,_) -> let (_,spi) = repr_path (fst sp) in id = spi)
    with Not_found ->
      user_err_loc (loc,"reset_name",pr_id id ++ str ": no such entry")
  in
  reset_to sp

let is_mod_node = function 
  | OpenedModule _ | OpenedModtype _ | OpenedSection _ 
  | ClosedSection _ -> true 
  | Leaf o -> let t = object_tag o in t = "MODULE" || t = "MODULE TYPE"
  | _ -> false

(* Reset on a module or section name in order to bypass constants with 
   the same name *) 

let reset_mod (loc,id) =
  let (ent,before) = 
    try
      find_split_p (fun (sp,node) -> 
                    let (_,spi) = repr_path (fst sp) in id = spi 
                    && is_mod_node node)
    with Not_found ->
      user_err_loc (loc,"reset_mod",pr_id id ++ str ": no such entry")
  in
  lib_stk := before;
  recalc_path_prefix ();
  let spf = match find_entry_p is_frozen_state with
    | (sp, FrozenState f) -> unfreeze_summaries f; sp
    | _ -> assert false
  in
  let (after,_,_) = split_lib spf in
  recache_context after


let point_obj =
  let (f,_) = declare_object {(default_object "DOT") with
				classify_function = (fun _ -> Dispose)} in
    f()

let mark_end_of_command () =
  match !lib_stk with
      (_,Leaf o)::_ when object_tag o = "DOT" -> ()
    | _ -> add_anonymous_leaf point_obj

let rec back_stk n stk =
  match stk with
      (sp,Leaf o)::tail when object_tag o = "DOT" ->
        if n=0 then sp else back_stk (n-1) tail
    | _::tail -> back_stk n tail
    | [] -> error "Reached begin of command history"

let back n = reset_to (back_stk n !lib_stk)

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
  path_prefix := initial_prefix;
  init_summaries()

(* Initial state. *)

let initial_state = ref None

let declare_initial_state () = 
  let name = add_anonymous_entry (FrozenState (freeze_summaries())) in
  initial_state := Some name

let reset_initial () =
  match !initial_state with
    | None -> 
        error "Resetting to the initial state is possible only interactively"
    | Some sp -> 
  	begin match split_lib sp with
	  | (_,[_,FrozenState fs as hd],before) ->
	      lib_stk := hd::before;
	      recalc_path_prefix ();
	      unfreeze_summaries fs
	  | _ -> assert false
	end


(* Misc *)

let library_part ref =
  let sp = Nametab.sp_of_global ref in
  let dir,_ = repr_path sp in
  match ref with
  | VarRef id -> 
      anomaly "TODO";
      extract_dirpath_prefix (sections_depth ()) (cwd ())
  | _ ->
      if is_dirpath_prefix_of dir (cwd ()) then
        (* Not yet (fully) discharged *)
        extract_dirpath_prefix (sections_depth ()) (cwd ())
      else
	(* Theorem/Lemma outside its outer section of definition *)
	dir


let rec file_of_mp = function
  | MPfile dir -> Some dir
  | MPself _ -> Some (library_dp ())
  | MPbound _ -> None
  | MPdot (mp,_) -> file_of_mp mp

let file_part = function
  | VarRef id -> anomaly "TODO";
  | ConstRef kn | ConstructRef ((kn,_),_) | IndRef (kn,_) -> 
      file_of_mp (modpath kn)
