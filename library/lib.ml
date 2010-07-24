(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
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

type lib_objects =  (Names.identifier * obj) list

let iter_objects f i prefix =
  List.iter (fun (id,obj) -> f i (make_oname prefix id, obj))

let load_objects = iter_objects load_object
let open_objects = iter_objects open_object

let subst_objects subst seg = 
  let subst_one = fun (id,obj as node) ->
    let obj' = subst_object (subst,obj) in
      if obj' == obj then node else
	(id, obj')
  in
    list_smartmap subst_one seg

(*let load_and_subst_objects i prefix subst seg =
  List.rev (List.fold_left (fun seg (id,obj as node) ->
    let obj' =  subst_object (make_oname prefix id, subst, obj) in
    let node = if obj == obj' then node else (id, obj') in
    load_object i (make_oname prefix id, obj');
    node :: seg) [] seg)
*)
let classify_segment seg =
  let rec clean ((substl,keepl,anticipl) as acc) = function
    | (_,CompilingLibrary _) :: _ | [] -> acc
    | ((sp,kn),Leaf o) :: stk ->
	let id = Names.id_of_label (Names.label kn) in
	  (match classify_object o with
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

let initial_prefix = default_library,(Names.initial_path,Names.empty_dirpath)

let lib_stk = ref ([] : library_segment)

let comp_name = ref None

let library_dp () =
  match !comp_name with Some m -> m | None -> default_library

(* [path_prefix] is a pair of absolute dirpath and a pair of current
   module path and relative section path *)
let path_prefix = ref initial_prefix

let sections_depth () =
  List.length (Names.repr_dirpath (snd (snd !path_prefix)))

let sections_are_opened () =
  match Names.repr_dirpath (snd (snd !path_prefix)) with
      [] -> false
    | _ -> true

let cwd () = fst !path_prefix

let cwd_except_section () =
  Libnames.pop_dirpath_n (sections_depth ()) (cwd ())

let current_dirpath sec =
  Libnames.drop_dirpath_prefix (library_dp ())
    (if sec then cwd () else cwd_except_section ())

let make_path id = Libnames.make_path (cwd ()) id

let make_path_except_section id = Libnames.make_path (cwd_except_section ()) id

let path_of_include () =
  let dir = Names.repr_dirpath (cwd ()) in
  let new_dir = List.tl dir in
  let id = List.hd dir in
    Libnames.make_path (Names.make_dirpath new_dir) id

let current_prefix () = snd !path_prefix

let make_kn id =
  let mp,dir = current_prefix () in
    Names.make_kn mp dir (Names.label_of_id id)

let make_con id =
  let mp,dir = current_prefix () in
    Names.make_con mp dir (Names.label_of_id id)


let make_oname id = make_path id, make_kn id

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
    | hd::before when test hd -> collect after (hd::equal) before
    | before -> after,equal,before
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

let split_lib sp = split_lib_gen (fun x -> fst x = sp)

let split_lib_at_opening sp =
  let a,s,b = split_lib_gen (function
    | x,(OpenedSection _|OpenedModule _|OpenedModtype _|CompilingLibrary _) ->
	x = sp
    | _ ->
	false) in
  assert (List.tl s = []);
  (a,List.hd s,b)

(* Adding operations. *)

let add_entry sp node =
  lib_stk := (sp,node) :: !lib_stk

let anonymous_id =
  let n = ref 0 in
  fun () -> incr n; Names.id_of_string ("_" ^ (string_of_int !n))

let add_anonymous_entry node =
  let id = anonymous_id () in
  let name = make_oname id in
  add_entry name node;
  name

let add_leaf id obj =
  if fst (current_prefix ()) = Names.initial_path then
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


let is_opened id = function
    oname,(OpenedSection _ | OpenedModule _ | OpenedModtype _) when
      basename (fst oname) = id -> true
  | _ -> false

let is_opening_node = function
    _,(OpenedSection _ | OpenedModule _ | OpenedModtype _) -> true
  | _ -> false

let is_opening_node_or_lib = function
    _,(CompilingLibrary _ | OpenedSection _ 
    | OpenedModule _ | OpenedModtype _) -> true
  | _ -> false

let current_mod_id () =
  try match find_entry_p is_opening_node_or_lib with
    | oname,OpenedModule (_,_,fs) ->
	basename (fst oname)
    | oname,OpenedModtype (_,fs) ->
	basename (fst oname)
    | oname,CompilingLibrary _ ->
       basename (fst oname)
    | _ -> error "you are not in a module"
  with Not_found ->
    error "no opened modules"


let start_module export id mp fs =
  let dir = add_dirpath_suffix (fst !path_prefix) id in
  let prefix = dir,(mp,Names.empty_dirpath) in
  let oname = make_path id, make_kn id in
  if Nametab.exists_module dir then
    errorlabstrm "open_module" (pr_id id ++ str " already exists") ;
  add_entry oname (OpenedModule (export,prefix,fs));
  path_prefix := prefix;
  prefix
(*  add_frozen_state () must be called in declaremods *)

let error_still_opened string oname =
  let id = basename (fst oname) in
  errorlabstrm "" (str string ++ spc () ++ pr_id id ++ str " is still opened.")

let end_module () =
  let oname,fs =
    try match find_entry_p is_opening_node with
      | oname,OpenedModule (_,_,fs) -> oname,fs
      | oname,OpenedModtype _ -> error_still_opened "Module Type" oname
      | oname,OpenedSection _ -> error_still_opened "Section" oname
      | _ -> assert false
    with Not_found ->
      error "No opened modules."
  in
  let (after,mark,before) = split_lib_at_opening oname in
  lib_stk := before;
  add_entry oname (ClosedModule (List.rev (mark::after)));
  let prefix = !path_prefix in
  (* LEM: This module business seems more complicated than sections;
          shouldn't a backtrack into a closed module also do something
          with global.ml, given that closing a module does?
     TODO
   *)
  recalc_path_prefix ();
  (* add_frozen_state must be called after processing the module,
     because we cannot recache interactive modules  *)
  (oname, prefix, fs, after)

let start_modtype id mp fs =
  let dir = add_dirpath_suffix (fst !path_prefix) id in
  let prefix = dir,(mp,Names.empty_dirpath) in
  let sp = make_path id in
  let name = sp, make_kn id in
  if Nametab.exists_cci sp then
    errorlabstrm "open_modtype" (pr_id id ++ str " already exists") ;
  add_entry name (OpenedModtype (prefix,fs));
  path_prefix := prefix;
  prefix

let end_modtype () =
  let oname,fs =
    try match find_entry_p is_opening_node with
      | oname,OpenedModtype (_,fs) -> oname,fs
      | oname,OpenedModule _ -> error_still_opened "Module" oname
      | oname,OpenedSection _ -> error_still_opened "Section" oname
      | _ -> assert false
    with Not_found ->
      error "no opened module types"
  in
  let (after,mark,before) = split_lib_at_opening oname in
  lib_stk := before;
  add_entry oname (ClosedModtype (List.rev (mark::after)));
  let dir = !path_prefix in
  recalc_path_prefix ();
  (* add_frozen_state must be called after processing the module type.
     This is because we cannot recache interactive module types *)
  (oname,dir,fs,after)


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
  if snd (snd (!path_prefix)) <> Names.empty_dirpath then
    error "some sections are already opened";
  let prefix = s, (mp, Names.empty_dirpath) in
  let _ = add_anonymous_entry (CompilingLibrary prefix) in
  comp_name := Some s;
  path_prefix := prefix

let end_compilation dir =
  let _ =
    try match snd (find_entry_p is_opening_node) with
      | OpenedSection _ -> error "There are some open sections."
      | OpenedModule _ -> error "There are some open modules."
      | OpenedModtype _ -> error "There are some open module types."
      | _ -> assert false
    with
	Not_found -> ()
  in
  let module_p =
    function (_,CompilingLibrary _) -> true | x -> is_opening_node x
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
	    ("The current open module has name "^ (Names.string_of_dirpath m) ^
	       " and not " ^ (Names.string_of_dirpath m));
  in
  let (after,mark,before) = split_lib_at_opening oname in
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


(* Returns the opening node of a given name *)
let find_opening_node id =
  try
    let oname,entry = find_entry_p is_opening_node in
    let id' = basename (fst oname) in
    if id <> id' then
      error ("Last block to end has name "^(Names.string_of_id id')^".");
    entry
  with Not_found -> error "There is nothing to end."

(* Discharge tables *)

(* At each level of section, we remember
   - the list of variables in this section
   - the list of variables on which each constant depends in this section
   - the list of variables on which each inductive depends in this section
   - the list of substitution to do at section closing
*)
type binding_kind = Explicit | Implicit

type variable_info = Names.identifier * binding_kind * Term.constr option * Term.types
type variable_context = variable_info list
type abstr_list = variable_context Names.Cmap.t * variable_context Names.Mindmap.t

let sectab =
  ref ([] : ((Names.identifier * binding_kind) list * Cooking.work_list * abstr_list) list)

let add_section () =
  sectab := ([],(Names.Cmap.empty,Names.Mindmap.empty),(Names.Cmap.empty,Names.Mindmap.empty)) :: !sectab

let add_section_variable id impl =
  match !sectab with
    | [] -> () (* because (Co-)Fixpoint temporarily uses local vars *)
    | (vars,repl,abs)::sl ->
	sectab := ((id,impl)::vars,repl,abs)::sl

let extract_hyps (secs,ohyps) =
  let rec aux = function
    | ((id,impl)::idl,(id',b,t)::hyps) when id=id' -> (id',impl,b,t) :: aux (idl,hyps)
    | (id::idl,hyps) -> aux (idl,hyps)
    | [], _ -> []
  in aux (secs,ohyps)

let instance_from_variable_context sign =
  let rec inst_rec = function
    | (id,b,None,_) :: sign -> id :: inst_rec sign
    | _ :: sign -> inst_rec sign
    | [] -> [] in
  Array.of_list (inst_rec sign)

let named_of_variable_context = List.map (fun (id,_,b,t) -> (id,b,t))

let add_section_replacement f g hyps =
  match !sectab with
  | [] -> ()
  | (vars,exps,abs)::sl ->
    let sechyps = extract_hyps (vars,hyps) in
    let args = instance_from_variable_context (List.rev sechyps) in
    sectab := (vars,f args exps,g sechyps abs)::sl

let add_section_kn kn =
  let f x (l1,l2) = (l1,Names.Mindmap.add kn x l2) in
  add_section_replacement f f

let add_section_constant kn =
  let f x (l1,l2) = (Names.Cmap.add kn x l1,l2) in
  add_section_replacement f f

let replacement_context () = pi2 (List.hd !sectab)

let variables_context () = pi1 (List.hd !sectab)

let section_segment_of_constant con =
  Names.Cmap.find con (fst (pi3 (List.hd !sectab)))

let section_segment_of_mutual_inductive kn =
  Names.Mindmap.find kn (snd (pi3 (List.hd !sectab)))

let rec list_mem_assoc x = function
  | [] -> raise Not_found
  | (a,_)::l -> compare a x = 0 or list_mem_assoc x l

let section_instance = function
  | VarRef id ->
      if list_mem_assoc id (pi1 (List.hd !sectab)) then [||]
      else raise Not_found
  | ConstRef con ->
      Names.Cmap.find con (fst (pi2 (List.hd !sectab)))
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
      Names.Mindmap.find kn (snd (pi2 (List.hd !sectab)))

let is_in_section ref =
  try ignore (section_instance ref); true with Not_found -> false

let init_sectab () = sectab := []
let freeze_sectab () = !sectab
let unfreeze_sectab s = sectab := s

let _ =
  Summary.declare_summary "section-context"
    { Summary.freeze_function = freeze_sectab;
      Summary.unfreeze_function = unfreeze_sectab;
      Summary.init_function = init_sectab }

(*************)
(* Sections. *)

(* XML output hooks *)
let xml_open_section = ref (fun id -> ())
let xml_close_section = ref (fun id -> ())

let set_xml_open_section f = xml_open_section := f
let set_xml_close_section f = xml_close_section := f

let open_section id =
  let olddir,(mp,oldsec) = !path_prefix in
  let dir = add_dirpath_suffix olddir id in
  let prefix = dir, (mp, add_dirpath_suffix oldsec id) in
  let name = make_path id, make_kn id (* this makes little sense however *) in
  if Nametab.exists_section dir then
    errorlabstrm "open_section" (pr_id id ++ str " already exists.");
  let fs = freeze_summaries() in
  add_entry name (OpenedSection (prefix, fs));
  (*Pushed for the lifetime of the section: removed by unfrozing the summary*)
  Nametab.push_dir (Nametab.Until 1) dir (DirOpenSection prefix);
  path_prefix := prefix;
  if !Flags.xml_export then !xml_open_section id;
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

let close_section () =
  let oname,fs =
    try match find_entry_p is_opening_node with
      | oname,OpenedSection (_,fs) -> oname,fs
      | _ -> assert false
    with Not_found ->
      error "No opened section."
  in
  let (secdecls,mark,before) = split_lib_at_opening oname in
  lib_stk := before;
  let full_olddir = fst !path_prefix in
  pop_path_prefix ();
  add_entry oname (ClosedSection (List.rev (mark::secdecls)));
  if !Flags.xml_export then !xml_close_section (basename (fst oname));
  let newdecls = List.map discharge_item secdecls in
  Summary.unfreeze_summaries fs;
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

let has_top_frozen_state () =
  let rec aux = function
  | (sp, FrozenState _)::_ -> Some sp
  | (sp, Leaf o)::t when object_tag o = "DOT" -> aux t
  | _ -> None
  in aux !lib_stk

let set_lib_stk new_lib_stk =
  lib_stk := new_lib_stk;
  recalc_path_prefix ();
  let spf = match find_entry_p is_frozen_state with
    | (sp, FrozenState f) -> unfreeze_summaries f; sp
    | _ -> assert false
  in
  let (after,_,_) = split_lib spf in
  try
    recache_context after
  with
    | Not_found -> error "Tried to set environment to an incoherent state."

let reset_to_gen test =
  let (_,_,before) = split_lib_gen test in
  set_lib_stk before

let reset_to sp = reset_to_gen (fun x -> fst x = sp)

let reset_to_state sp =
  let (_,eq,before) = split_lib sp in
  (* if eq a frozen state, we'll reset to it *)
  match eq with
  | [_,FrozenState f] -> lib_stk := eq@before; recalc_path_prefix (); unfreeze_summaries f
  | _ -> error "Not a frozen state"


(* LEM: TODO
 * We will need to muck with frozen states in after, too!
 * Not only FrozenState, but also those embedded in Opened(Section|Module|Modtype)
 *)
let delete_gen test =
  let (after,equal,before) = split_lib_gen test in
  let rec chop_at_dot = function
    | [] as l -> l
    | (_, Leaf o)::t when object_tag o = "DOT" -> t
    | _::t -> chop_at_dot t
  and chop_before_dot = function
    | [] as l -> l
    | (_, Leaf o)::t as l when object_tag o = "DOT" -> l
    | _::t -> chop_before_dot t
 in
  set_lib_stk (List.rev_append (chop_at_dot after) (chop_before_dot before))

let delete sp = delete_gen (fun x -> fst x = sp)

let reset_name (loc,id) =
  let (sp,_) =
    try
      find_entry_p (fun (sp,_) -> let (_,spi) = repr_path (fst sp) in id = spi)
    with Not_found ->
      user_err_loc (loc,"reset_name",pr_id id ++ str ": no such entry")
  in
  reset_to sp

let remove_name (loc,id) =
  let (sp,_) =
    try
      find_entry_p (fun (sp,_) -> let (_,spi) = repr_path (fst sp) in id = spi)
    with Not_found ->
      user_err_loc (loc,"remove_name",pr_id id ++ str ": no such entry")
  in
    delete sp

let is_mod_node = function
  | OpenedModule _ | OpenedModtype _ | OpenedSection _
  | ClosedModule _ | ClosedModtype _ | ClosedSection _  -> true
  | Leaf o -> let t = object_tag o in t = "MODULE" || t = "MODULE TYPE"
	|| t = "MODULE ALIAS"
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
  set_lib_stk before

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

type frozen = Names.dir_path option * library_segment

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
    | ConstRef cst -> Names.con_modpath cst
    | IndRef ind -> Names.ind_modpath ind
    | ConstructRef constr -> Names.constr_modpath constr

let rec dp_of_mp modp =
  match modp with
    | Names.MPfile dp -> dp
    | Names.MPbound _ -> library_dp ()
    | Names.MPdot (mp,_) -> dp_of_mp mp

let rec split_mp mp =
  match mp with
    | Names.MPfile dp -> dp,  Names.empty_dirpath
    | Names.MPdot (prfx, lbl) ->
	let mprec, dprec = split_mp prfx in
	  mprec, Names.make_dirpath (Names.id_of_string (Names.string_of_label lbl) :: (Names.repr_dirpath dprec))
    | Names.MPbound mbid -> let (_, id, dp) = Names.repr_mbid mbid in  library_dp(), Names.make_dirpath [Names.id_of_string id]

let split_modpath mp =
  let rec aux = function
    | Names.MPfile dp -> dp, []
    | Names.MPbound mbid ->
	library_dp (), [Names.id_of_mbid mbid]
    | Names.MPdot (mp,l) -> let (mp', lab) = aux mp in
			      (mp', Names.id_of_label l :: lab)
  in
  let (mp, l) = aux mp in
    mp, l

let library_part ref =
  match ref with
    | VarRef id -> library_dp ()
    | _ -> dp_of_mp (mp_of_global ref)

let remove_section_part ref =
  let sp = Nametab.path_of_global ref in
  let dir,_ = repr_path sp in
  match ref with
  | VarRef id ->
      anomaly "remove_section_part not supported on local variables"
  | _ ->
      if is_dirpath_prefix_of dir (cwd ()) then
        (* Not yet (fully) discharged *)
        pop_dirpath_n (sections_depth ()) (cwd ())
      else
	(* Theorem/Lemma outside its outer section of definition *)
	dir

(************************)
(* Discharging names *)

let pop_kn kn =
  let (mp,dir,l) = Names.repr_mind kn in
  Names.make_mind mp (pop_dirpath dir) l

let pop_con con =
  let (mp,dir,l) = Names.repr_con con in
  Names.make_con mp (pop_dirpath dir) l

let con_defined_in_sec kn =
  let _,dir,_ = Names.repr_con kn in
  dir <> Names.empty_dirpath && fst (split_dirpath dir) = snd (current_prefix ())

let defined_in_sec kn =
  let _,dir,_ = Names.repr_mind kn in
  dir <> Names.empty_dirpath && fst (split_dirpath dir) = snd (current_prefix ())

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
