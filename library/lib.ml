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
  | OpenedModule of bool option * object_prefix * Summary.frozen
  | ClosedModule  of library_segment
  | OpenedModtype of object_prefix * Summary.frozen
  | ClosedModtype of library_segment
  | OpenedSection of object_prefix * Summary.frozen
  | ClosedSection of library_segment
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
    | ((sp,kn as oname),Leaf o) :: stk -> 
	let id = id_of_label (label kn) in
	  (match classify_object (oname,o) with 
	     | Dispose -> clean acc stk
	     | Keep o' -> 
		 clean (substl, (id,o')::keepl, anticipl) stk
	     | Substitute o' -> 
		 clean ((id,o')::substl, keepl, anticipl) stk
	     | Anticipate o' ->
		 clean (substl, keepl, o'::anticipl) stk)
    | (_,ClosedSection _) :: stk -> clean acc stk
    (* LEM; TODO: Understand what this does and see if what I do is the
                  correct thing for ClosedMod(ule|type) *)
    | (_,ClosedModule _) :: stk -> clean acc stk
    | (_,ClosedModtype _) :: stk -> clean acc stk
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

let make_con id = 
  let mp,dir = current_prefix () in
    Names.make_con mp dir (label_of_id id)


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
    | (sp, OpenedModule (_,dir,_)) :: _ -> dir
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

let split_lib_gen test = 
  let rec collect after equal = function
    | hd::strict_before as before ->
      	if test hd then collect after (hd::equal) strict_before else after,equal,before
    | [] as before -> after,equal,before
  in
  let rec findeq after = function
    | hd :: before ->
      	if test hd
	then Some (collect after [hd] before)
	else (match hd with
		| (sp,ClosedModule  seg)
		| (sp,ClosedModtype seg)
		| (sp,ClosedSection seg) ->
		    (match findeq after seg with
		       | None -> findeq (hd::after) before
		       | Some (sub_after,sub_equal,sub_before) ->
			   Some (sub_after, sub_equal, (List.append sub_before before)))
		| _ -> findeq (hd::after) before)
    | [] -> None
  in
    match findeq [] !lib_stk with
      | None -> error "no such entry"
      | Some r -> r

let split_lib sp = split_lib_gen (fun x -> (fst x) = sp)

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
  if fst (current_prefix ()) = initial_path then 
    error ("No session module started (use -top dir)");
  let oname = make_oname id in
  cache_object (oname,obj);
  add_entry oname (Leaf obj);
  oname

let add_discharged_leaf id obj =
  let oname = make_oname id in
  let newobj = rebuild_object obj in
  cache_object (oname,newobj);
  add_entry oname (Leaf newobj)

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

let start_module export id mp nametab = 
  let dir = extend_dirpath (fst !path_prefix) id in
  let prefix = dir,(mp,empty_dirpath) in
  let oname = make_path id, make_kn id in
  if Nametab.exists_module dir then
    errorlabstrm "open_module" (pr_id id ++ str " already exists") ;
  add_entry oname (OpenedModule (export,prefix,nametab));
  path_prefix := prefix;
  prefix
(*  add_frozen_state () must be called in declaremods *)
 
let end_module id = 
  let oname,nametab = 
    try match find_entry_p is_something_opened with
      | oname,OpenedModule (_,_,nametab) -> 
	  let id' = basename (fst oname) in
	    if id<>id' then 
	      errorlabstrm "end_module" (str "last opened module is " ++ pr_id id'); 
	    oname,nametab
      | oname,OpenedModtype _ ->
	  let id' = basename (fst oname) in
	    errorlabstrm "end_module" 
	      (str "module type " ++ pr_id id' ++ str " is still opened")
      | oname,OpenedSection _ ->
	  let id' = basename (fst oname) in
	    errorlabstrm  "end_module" 
	      (str "section " ++ pr_id id' ++ str " is still opened")
      | _ -> assert false
    with Not_found ->
      error "no opened modules"
  in
  let (after,modopening,before) = split_lib oname in
  lib_stk := before;
  add_entry (make_oname id) (ClosedModule (List.rev_append after (List.rev modopening)));
  let prefix = !path_prefix in
  (* LEM: This module business seems more complicated than sections;
          shouldn't a backtrack into a closed module also do something
          with global.ml, given that closing a module does?
     TODO
   *)
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
      | oname,OpenedModtype (_,nametab) -> 
	  let id' = basename (fst oname) in
	  if id<>id' then 
	    errorlabstrm "end_modtype" (str "last opened module type is " ++ pr_id id'); 
	    oname,nametab
      | oname,OpenedModule _ ->
	  let id' = basename (fst oname) in
	    errorlabstrm "end_modtype" 
	      (str "module " ++ pr_id id' ++ str " is still opened")
      | oname,OpenedSection _ ->
	  let id' = basename (fst oname) in
	    errorlabstrm "end_modtype" 
	      (str "section " ++ pr_id id' ++ str " is still opened")
      | _ -> assert false
    with Not_found ->
      error "no opened module types"
  in
  let (after,modtypeopening,before) = split_lib sp in
  lib_stk := before;
  add_entry (make_oname id) (ClosedModtype (List.rev_append after (List.rev modtypeopening)));
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
  let _ =  
    match !comp_name with
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

(* Discharge tables *)

(* At each level of section, we remember
   - the list of variables in this section
   - the list of variables on which each constant depends in this section
   - the list of variables on which each inductive depends in this section
   - the list of substitution to do at section closing 
*)

type abstr_list = Sign.named_context Cmap.t * Sign.named_context KNmap.t

let sectab =
  ref ([] : (identifier list * Cooking.work_list * abstr_list) list)

let add_section () =
  sectab := ([],(Cmap.empty,KNmap.empty),(Cmap.empty,KNmap.empty)) :: !sectab

let add_section_variable id =
  match !sectab with
    | [] -> () (* because (Co-)Fixpoint temporarily uses local vars *)
    | (vars,repl,abs)::sl -> sectab := (id::vars,repl,abs)::sl

let rec extract_hyps = function
  | (id::idl,(id',_,_ as d)::hyps) when id=id' -> d :: extract_hyps (idl,hyps)
  | (id::idl,hyps) -> extract_hyps (idl,hyps)
  | [], _ -> []

let add_section_replacement f g hyps =
  match !sectab with
  | [] -> ()
  | (vars,exps,abs)::sl ->
    let sechyps = extract_hyps (vars,hyps) in
    let args = Sign.instance_from_named_context (List.rev sechyps) in
    sectab := (vars,f (Array.map Term.destVar args) exps,g sechyps abs)::sl
	
let add_section_kn kn =
  let f = (fun x (l1,l2) -> (l1,KNmap.add kn x l2)) in
  add_section_replacement f f

let add_section_constant kn =
  let f = (fun x (l1,l2) -> (Cmap.add kn x l1,l2)) in
  add_section_replacement f f

let replacement_context () = pi2 (List.hd !sectab)

let section_segment_of_constant con =
  Cmap.find con (fst (pi3 (List.hd !sectab)))

let section_segment_of_mutual_inductive kn =
  KNmap.find kn (snd (pi3 (List.hd !sectab)))

let section_instance = function
  | VarRef id -> [||]
  | ConstRef con ->
      Cmap.find con (fst (pi2 (List.hd !sectab)))
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
      KNmap.find kn (snd (pi2 (List.hd !sectab)))

let init () = sectab := []
let freeze () = !sectab
let unfreeze s = sectab := s

let _ = 
  Summary.declare_summary "section-context"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = false }

(*************)
(* Sections. *)

(* XML output hooks *)
let xml_open_section = ref (fun id -> ())
let xml_close_section = ref (fun id -> ())

let set_xml_open_section f = xml_open_section := f
let set_xml_close_section f = xml_close_section := f

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
      add_section ()


(* Restore lib_stk and summaries as before the section opening, and
   add a ClosedSection object. *)

let discharge_item ((sp,_ as oname),e) =
  match e with
  | Leaf lobj ->
      Option.map (fun o -> (basename sp,o)) (discharge_object (oname,lobj))
  | FrozenState _ -> None
  | ClosedSection _ | ClosedModtype _ | ClosedModule _ -> None
  | OpenedSection _ | OpenedModtype _ | OpenedModule _ | CompilingLibrary _ ->
      anomaly "discharge_item"

let close_section id =
  let oname,fs = 
    try match find_entry_p is_something_opened with
      | oname,OpenedSection (_,fs) -> 
	  let id' = basename (fst oname) in 
	    if id <> id' then 
	      errorlabstrm "close_section" (str "last opened section is " ++ pr_id id');
	    (oname,fs)
      | _ -> assert false 
    with Not_found ->
      error "no opened section"
  in
  let (secdecls,secopening,before) = split_lib oname in
  lib_stk := before;
  let full_olddir = fst !path_prefix in
  pop_path_prefix ();
  add_entry (make_oname id) (ClosedSection (List.rev_append secdecls (List.rev secopening)));
  if !Options.xml_export then !xml_close_section id;
  let newdecls = List.map discharge_item secdecls in
  Summary.section_unfreeze_summaries fs;
  List.iter (Option.iter (fun (id,o) -> add_discharged_leaf id o)) newdecls;
  Cooking.clear_cooking_sharing ();
  Nametab.push_dir (Nametab.Until 1) full_olddir (DirClosedSection full_olddir)

(*****************)
(* Backtracking. *)

let (inLabel,outLabel) =
  declare_object {(default_object "DOT") with
				classify_function = (fun _ -> Dispose)}

let recache_decl = function
  | (sp, Leaf o) -> cache_object (sp,o)
  | (_,OpenedSection _) -> add_section ()
  | _ -> ()

let recache_context ctx =
  List.iter recache_decl ctx

let is_frozen_state = function (_,FrozenState _) -> true | _ -> false

let reset_to_gen test =
  let (_,_,before) = split_lib_gen test in
  lib_stk := before;
  recalc_path_prefix ();
  let spf = match find_entry_p is_frozen_state with
    | (sp, FrozenState f) -> unfreeze_summaries f; sp
    | _ -> assert false
  in
  let (after,_,_) = split_lib spf in
  let res = recache_context after in
  res

let reset_to sp = reset_to_gen (fun x -> (fst x) = sp)

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
  | ClosedModule _ | ClosedModtype _ | ClosedSection _  -> true 
  | Leaf o -> let t = object_tag o in t = "MODULE" || t = "MODULE TYPE"
  | _ -> false

(* Reset on a module or section name in order to bypass constants with 
   the same name *) 

let reset_mod (loc,id) =
  let (_,before) = 
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


let mark_end_of_command, current_command_label, set_command_label =
  let n = ref 0 in
  (fun () ->
    match !lib_stk with
        (_,Leaf o)::_ when object_tag o = "DOT" -> ()
      | _ -> incr n;add_anonymous_leaf (inLabel !n)),
  (fun () -> !n),
  (fun x -> n:=x)

let is_label_n n x =
  match x with
    | (sp,Leaf o) when object_tag o = "DOT" && n = outLabel o -> true
    | _ -> false

(* Reset the label registered by [mark_end_of_command()] with number n. *)
let reset_label n = 
  let current = current_command_label() in
  if n < current then
    let res = reset_to_gen (is_label_n n) in
    set_command_label (n-1); (* forget state numbers after n only if reset succeeded *)
    res
  else (* optimisation to avoid recaching when not necessary (why is it so long??) *)
    match !lib_stk with
      | [] -> ()
      | x :: ls -> (lib_stk := ls;set_command_label (n-1))
    
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
			set_command_label 0;
	      unfreeze_summaries fs
	  | _ -> assert false
	end


(* Misc *)

let mp_of_global ref = 
  match ref with
    | VarRef id -> fst (current_prefix ())
    | ConstRef cst -> con_modpath cst
    | IndRef ind -> ind_modpath ind
    | ConstructRef constr -> constr_modpath constr

let rec dp_of_mp modp =
  match modp with
    | MPfile dp -> dp
    | MPbound _ | MPself _ -> library_dp ()
    | MPdot (mp,_) -> dp_of_mp mp

let library_part ref =
  match ref with 
    | VarRef id -> library_dp ()
    | _ -> dp_of_mp (mp_of_global ref)

let remove_section_part ref =
  let sp = Nametab.sp_of_global ref in
  let dir,_ = repr_path sp in
  match ref with
  | VarRef id -> 
      anomaly "remove_section_part not supported on local variables"
  | _ ->
      if is_dirpath_prefix_of dir (cwd ()) then
        (* Not yet (fully) discharged *)
        extract_dirpath_prefix (sections_depth ()) (cwd ())
      else
	(* Theorem/Lemma outside its outer section of definition *)
	dir

(************************)
(* Discharging names *)

let pop_kn kn =
  let (mp,dir,l) = Names.repr_kn kn in
  Names.make_kn mp (dirpath_prefix dir) l

let pop_con con = 
  let (mp,dir,l) = Names.repr_con con in
  Names.make_con mp (dirpath_prefix dir) l

let con_defined_in_sec kn = 
  let _,dir,_ = repr_con kn in
  dir <> empty_dirpath && fst (split_dirpath dir) = snd (current_prefix ())

let defined_in_sec kn = 
  let _,dir,_ = repr_kn kn in
  dir <> empty_dirpath && fst (split_dirpath dir) = snd (current_prefix ())

let discharge_global = function
  | ConstRef kn when con_defined_in_sec kn ->
      ConstRef (pop_con kn)
  | IndRef (kn,i) when defined_in_sec kn ->
      IndRef (pop_kn kn,i)
  | ConstructRef ((kn,i),j) when defined_in_sec kn ->
      ConstructRef ((pop_kn kn,i),j)
  | r -> r

let discharge_kn kn = 
  if defined_in_sec kn then pop_kn kn else kn

let discharge_con cst = 
  if con_defined_in_sec cst then pop_con cst else cst

let discharge_inductive (kn,i) =
  (discharge_kn kn,i)
