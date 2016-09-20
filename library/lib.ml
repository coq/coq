(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Libnames
open Globnames
open Nameops
open Libobject

type is_type = bool (* Module Type or just Module *)
type export = bool option (* None for a Module Type *)

type node =
  | Leaf of obj
  | CompilingLibrary of object_prefix
  | OpenedModule of is_type * export * object_prefix * Summary.frozen
  | ClosedModule  of library_segment
  | OpenedSection of object_prefix * Summary.frozen
  | ClosedSection of library_segment
  | FrozenState of Summary.frozen

and library_entry = object_name * node

and library_segment = library_entry list

type lib_objects =  (Names.Id.t * obj) list

let module_kind is_type =
  if is_type then "module type" else "module"

let iter_objects f i prefix =
  List.iter (fun (id,obj) -> f i (make_oname prefix id, obj))

let load_objects i pr = iter_objects load_object i pr
let open_objects i pr = iter_objects open_object i pr

let subst_objects subst seg = 
  let subst_one = fun (id,obj as node) ->
    let obj' = subst_object (subst,obj) in
      if obj' == obj then node else
	(id, obj')
  in
    List.smartmap subst_one seg

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
	let id = Names.Label.to_id (Names.label kn) in
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
    | (_,OpenedSection _) :: _ -> error "there are still opened sections"
    | (_,OpenedModule (ty,_,_,_)) :: _ ->
      errorlabstrm "Lib.classify_segment"
        (str "there are still opened " ++ str (module_kind ty) ++ str "s")
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

let initial_prefix = default_library,(Names.initial_path,Names.DirPath.empty)

let lib_stk = ref ([] : library_segment)

let comp_name = ref None

let library_dp () =
  match !comp_name with Some m -> m | None -> default_library

(* [path_prefix] is a pair of absolute dirpath and a pair of current
   module path and relative section path *)
let path_prefix = ref initial_prefix

let cwd () = fst !path_prefix
let current_prefix () = snd !path_prefix
let current_mp () = fst (snd !path_prefix)
let current_sections () = snd (snd !path_prefix)

let sections_depth () = List.length (Names.DirPath.repr (current_sections ()))
let sections_are_opened () = not (Names.DirPath.is_empty (current_sections ()))

let cwd_except_section () =
  Libnames.pop_dirpath_n (sections_depth ()) (cwd ())

let current_dirpath sec =
  Libnames.drop_dirpath_prefix (library_dp ())
    (if sec then cwd () else cwd_except_section ())

let make_path id = Libnames.make_path (cwd ()) id

let make_path_except_section id =
  Libnames.make_path (cwd_except_section ()) id

let make_kn id =
  let mp,dir = current_prefix () in
  Names.make_kn mp dir (Names.Label.of_id id)

let make_oname id = Libnames.make_oname !path_prefix id

let recalc_path_prefix () =
  let rec recalc = function
    | (sp, OpenedSection (dir,_)) :: _ -> dir
    | (sp, OpenedModule (_,_,dir,_)) :: _ -> dir
    | (sp, CompilingLibrary dir) :: _ -> dir
    | _::l -> recalc l
    | [] -> initial_prefix
  in
  path_prefix := recalc !lib_stk

let pop_path_prefix () =
  let dir,(mp,sec) = !path_prefix in
  path_prefix := pop_dirpath dir, (mp, pop_dirpath sec)

let find_entry_p p =
  let rec find = function
    | [] -> raise Not_found
    | ent::l -> if p ent then ent else find l
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

let eq_object_name (fp1, kn1) (fp2, kn2) =
  eq_full_path fp1 fp2 && Names.KerName.equal kn1 kn2

let split_lib sp =
  let is_sp (nsp, _) = eq_object_name sp nsp in
  split_lib_gen is_sp

let split_lib_at_opening sp =
  let is_sp (nsp, obj) = match obj with
    | OpenedSection _ | OpenedModule _ | CompilingLibrary _ ->
      eq_object_name nsp sp
    | _ -> false
  in
  let a, s, b = split_lib_gen is_sp in
  match s with
  | [obj] -> (a, obj, b)
  | _ -> assert false

(* Adding operations. *)

let add_entry sp node =
  lib_stk := (sp,node) :: !lib_stk

let pull_to_head oname =
  lib_stk := (oname,List.assoc oname !lib_stk) :: List.remove_assoc oname !lib_stk

let anonymous_id =
  let n = ref 0 in
  fun () -> incr n; Names.Id.of_string ("_" ^ (string_of_int !n))

let add_anonymous_entry node =
  add_entry (make_oname (anonymous_id ())) node

let add_leaf id obj =
  if Names.ModPath.equal (current_mp ()) Names.initial_path then
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
  add_anonymous_entry
    (FrozenState (Summary.freeze_summaries ~marshallable:`No))

(* Modules. *)

let is_opening_node = function
  | _,(OpenedSection _ | OpenedModule _) -> true
  | _ -> false

let is_opening_node_or_lib = function
  | _,(CompilingLibrary _ | OpenedSection _ | OpenedModule _) -> true
  | _ -> false

let current_mod_id () =
  try match find_entry_p is_opening_node_or_lib with
    | oname,OpenedModule (_,_,_,fs) -> basename (fst oname)
    | oname,CompilingLibrary _ -> basename (fst oname)
    | _ -> error "you are not in a module"
  with Not_found -> error "no opened modules"


let start_mod is_type export id mp fs =
  let dir = add_dirpath_suffix (cwd ()) id in
  let prefix = dir,(mp,Names.DirPath.empty) in
  let exists =
    if is_type then Nametab.exists_cci (make_path id)
    else Nametab.exists_module dir
  in
  if exists then
    errorlabstrm "open_module" (pr_id id ++ str " already exists");
  add_entry (make_oname id) (OpenedModule (is_type,export,prefix,fs));
  path_prefix := prefix;
  prefix

let start_module = start_mod false
let start_modtype = start_mod true None

let error_still_opened string oname =
  let id = basename (fst oname) in
  errorlabstrm ""
    (str "The " ++ str string ++ str " " ++ pr_id id ++ str " is still opened.")

let end_mod is_type =
  let oname,fs =
    try match find_entry_p is_opening_node with
      | oname,OpenedModule (ty,_,_,fs) ->
	if ty == is_type then oname, fs
	else error_still_opened (module_kind ty) oname
      | oname,OpenedSection _ -> error_still_opened "section" oname
      | _ -> assert false
    with Not_found -> error "No opened modules."
  in
  let (after,mark,before) = split_lib_at_opening oname in
  lib_stk := before;
  add_entry oname (ClosedModule (List.rev (mark::after)));
  let prefix = !path_prefix in
  recalc_path_prefix ();
  (oname, prefix, fs, after)

let end_module () = end_mod false
let end_modtype () = end_mod true

let contents () = !lib_stk

let contents_after sp = let (after,_,_) = split_lib sp in after

(* Modules. *)

(* TODO: use check_for_module ? *)
let start_compilation s mp =
  if !comp_name != None then
    error "compilation unit is already started";
  if not (Names.DirPath.is_empty (current_sections ())) then
    error "some sections are already opened";
  let prefix = s, (mp, Names.DirPath.empty) in
  let () = add_anonymous_entry (CompilingLibrary prefix) in
  comp_name := Some s;
  path_prefix := prefix

let end_compilation_checks dir =
  let _ =
    try match snd (find_entry_p is_opening_node) with
      | OpenedSection _ -> error "There are some open sections."
      | OpenedModule (ty,_,_,_) ->
	errorlabstrm "Lib.end_compilation_checks"
          (str "There are some open " ++ str (module_kind ty) ++ str "s.")
      | _ -> assert false
    with Not_found -> ()
  in
  let is_opening_lib = function _,CompilingLibrary _ -> true | _ -> false
  in
  let oname =
    try match find_entry_p is_opening_lib with
      |	(oname, CompilingLibrary prefix) -> oname
      | _ -> assert false
    with Not_found -> anomaly (Pp.str "No module declared")
  in
  let _ =
    match !comp_name with
      | None -> anomaly (Pp.str "There should be a module name...")
      | Some m ->
	  if not (Names.DirPath.equal m dir) then anomaly
	    (str "The current open module has name" ++ spc () ++ pr_dirpath m ++
             spc () ++ str "and not" ++ spc () ++ pr_dirpath m);
  in
  oname

let end_compilation oname =
  let (after,mark,before) = split_lib_at_opening oname in
  comp_name := None;
  !path_prefix,after

(* Returns true if we are inside an opened module or module type *)

let is_module_gen which check =
  let test = function
    | _, OpenedModule (ty,_,_,_) -> which ty
    | _ -> false
  in
  try
    match find_entry_p test with
    | _, OpenedModule (ty,_,_,_) -> check ty
    | _ -> assert false
  with Not_found -> false

let is_module_or_modtype () = is_module_gen (fun _ -> true) (fun _ -> true)
let is_modtype () = is_module_gen (fun b -> b) (fun _ -> true)
let is_modtype_strict () = is_module_gen (fun _ -> true) (fun b -> b)
let is_module () = is_module_gen (fun b -> not b) (fun _ -> true)

(* Returns the opening node of a given name *)
let find_opening_node id =
  try
    let oname,entry = find_entry_p is_opening_node in
    let id' = basename (fst oname) in
    if not (Names.Id.equal id id') then
      errorlabstrm "Lib.find_opening_node"
        (str "Last block to end has name " ++ pr_id id' ++ str ".");
    entry
  with Not_found -> error "There is nothing to end."

(* Discharge tables *)

(* At each level of section, we remember
   - the list of variables in this section
   - the list of variables on which each constant depends in this section
   - the list of variables on which each inductive depends in this section
   - the list of substitution to do at section closing
*)

type variable_info = Names.Id.t * Decl_kinds.binding_kind * Term.constr option * Term.types

type variable_context = variable_info list
type abstr_info = variable_context * Univ.universe_level_subst * Univ.UContext.t
		  
type abstr_list = abstr_info Names.Cmap.t * abstr_info Names.Mindmap.t

type secentry =
  | Variable of (Names.Id.t * Decl_kinds.binding_kind *
		   Decl_kinds.polymorphic * Univ.universe_context_set)
  | Context of Univ.universe_context_set

let sectab =
  Summary.ref ([] : (secentry list * Opaqueproof.work_list * abstr_list) list)
    ~name:"section-context"

let add_section () =
  sectab := ([],(Names.Cmap.empty,Names.Mindmap.empty),
                (Names.Cmap.empty,Names.Mindmap.empty)) :: !sectab

let check_same_poly p vars =
  let pred = function Context _ -> p = false | Variable (_, _, poly, _) -> p != poly in
  if List.exists pred vars then
    error "Cannot mix universe polymorphic and monomorphic declarations in sections."

let add_section_variable id impl poly ctx =
  match !sectab with
    | [] -> () (* because (Co-)Fixpoint temporarily uses local vars *)
    | (vars,repl,abs)::sl ->
       List.iter (fun tab -> check_same_poly poly (pi1 tab)) !sectab;
       sectab := (Variable (id,impl,poly,ctx)::vars,repl,abs)::sl

let add_section_context ctx =
  match !sectab with
    | [] -> () (* because (Co-)Fixpoint temporarily uses local vars *)
    | (vars,repl,abs)::sl ->
       check_same_poly true vars;
       sectab := (Context ctx :: vars,repl,abs)::sl

let extract_hyps (secs,ohyps) =
  let open Context.Named.Declaration in
  let rec aux = function
    | (Variable (id,impl,poly,ctx)::idl, decl::hyps) when Names.Id.equal id (get_id decl) ->
      let (id',b,t) = to_tuple decl in
      let l, r = aux (idl,hyps) in 
	(id',impl,b,t) :: l, if poly then Univ.ContextSet.union r ctx else r
    | (Variable (_,_,poly,ctx)::idl,hyps) ->
        let l, r = aux (idl,hyps) in
          l, if poly then Univ.ContextSet.union r ctx else r
    | (Context ctx :: idl, hyps) ->
       let l, r = aux (idl, hyps) in
       l, Univ.ContextSet.union r ctx
    | [], _ -> [],Univ.ContextSet.empty
  in aux (secs,ohyps)

let instance_from_variable_context sign =
  let rec inst_rec = function
    | (id,b,None,_) :: sign -> id :: inst_rec sign
    | _ :: sign -> inst_rec sign
    | [] -> [] in
  Array.of_list (inst_rec sign)

let named_of_variable_context ctx = let open Context.Named.Declaration in
                                    List.map (function id,_,None,t -> LocalAssum (id,t)
                                                     | id,_,Some b,t -> LocalDef (id,b,t))
                                             ctx
  
let add_section_replacement f g poly hyps =
  match !sectab with
  | [] -> ()
  | (vars,exps,abs)::sl ->
    let () = check_same_poly poly vars in
    let sechyps,ctx = extract_hyps (vars,hyps) in
    let ctx = Univ.ContextSet.to_context ctx in
    let subst, ctx = Univ.abstract_universes true ctx in
    let args = instance_from_variable_context (List.rev sechyps) in
    sectab := (vars,f (Univ.UContext.instance ctx,args) exps,
	      g (sechyps,subst,ctx) abs)::sl

let add_section_kn poly kn =
  let f x (l1,l2) = (l1,Names.Mindmap.add kn x l2) in
    add_section_replacement f f poly

let add_section_constant poly kn =
  let f x (l1,l2) = (Names.Cmap.add kn x l1,l2) in
    add_section_replacement f f poly

let replacement_context () = pi2 (List.hd !sectab)

let section_segment_of_constant con =
  Names.Cmap.find con (fst (pi3 (List.hd !sectab)))

let section_segment_of_mutual_inductive kn =
  Names.Mindmap.find kn (snd (pi3 (List.hd !sectab)))

let variable_section_segment_of_reference = function
  | ConstRef con -> pi1 (section_segment_of_constant con)
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
      pi1 (section_segment_of_mutual_inductive kn)
  | _ -> []
                     
let section_instance = function
  | VarRef id ->
     let eq = function
       | Variable (id',_,_,_) -> Names.id_eq id id'
       | Context _ -> false
     in
     if List.exists eq (pi1 (List.hd !sectab))
     then Univ.Instance.empty, [||]
     else raise Not_found
  | ConstRef con ->
      Names.Cmap.find con (fst (pi2 (List.hd !sectab)))
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
      Names.Mindmap.find kn (snd (pi2 (List.hd !sectab)))

let is_in_section ref =
  try ignore (section_instance ref); true with Not_found -> false

(*************)
(* Sections. *)

(* XML output hooks *)
let (f_xml_open_section, xml_open_section) = Hook.make ~default:ignore ()
let (f_xml_close_section, xml_close_section) = Hook.make ~default:ignore ()

let open_section id =
  let olddir,(mp,oldsec) = !path_prefix in
  let dir = add_dirpath_suffix olddir id in
  let prefix = dir, (mp, add_dirpath_suffix oldsec id) in
  if Nametab.exists_section dir then
    errorlabstrm "open_section" (pr_id id ++ str " already exists.");
  let fs = Summary.freeze_summaries ~marshallable:`No in
  add_entry (make_oname id) (OpenedSection (prefix, fs));
  (*Pushed for the lifetime of the section: removed by unfrozing the summary*)
  Nametab.push_dir (Nametab.Until 1) dir (DirOpenSection prefix);
  path_prefix := prefix;
  if !Flags.xml_export then Hook.get f_xml_open_section id;
  add_section ()


(* Restore lib_stk and summaries as before the section opening, and
   add a ClosedSection object. *)

let discharge_item ((sp,_ as oname),e) =
  match e with
  | Leaf lobj ->
      Option.map (fun o -> (basename sp,o)) (discharge_object (oname,lobj))
  | FrozenState _ -> None
  | ClosedSection _ | ClosedModule _ -> None
  | OpenedSection _ | OpenedModule _ | CompilingLibrary _ ->
      anomaly (Pp.str "discharge_item")

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
  if !Flags.xml_export then Hook.get f_xml_close_section (basename (fst oname));
  let newdecls = List.map discharge_item secdecls in
  Summary.unfreeze_summaries fs;
  List.iter (Option.iter (fun (id,o) -> add_discharged_leaf id o)) newdecls;
  Nametab.push_dir (Nametab.Until 1) full_olddir (DirClosedSection full_olddir)

(* State and initialization. *)

type frozen = Names.DirPath.t option * library_segment

let freeze ~marshallable =
  match marshallable with
  | `Shallow ->
    (* TASSI: we should do something more sensible here *)
    let lib_stk =
      CList.map_filter (function
        | _, Leaf _ -> None
        | n, (CompilingLibrary _ as x) -> Some (n,x)
        | n, OpenedModule (it,e,op,_) ->
               Some(n,OpenedModule(it,e,op,Summary.empty_frozen))
        | n, ClosedModule _ -> Some (n,ClosedModule [])
        | n, OpenedSection (op, _) ->
               Some(n,OpenedSection(op,Summary.empty_frozen))
        | n, ClosedSection _ -> Some (n,ClosedSection [])
        | _, FrozenState _ -> None)
      !lib_stk in
    !comp_name, lib_stk
  | _ ->
    !comp_name, !lib_stk

let unfreeze (mn,stk) =
  comp_name := mn;
  lib_stk := stk;
  recalc_path_prefix ()

let init () =
  unfreeze (None,[]);
  Summary.init_summaries ();
  add_frozen_state () (* Stores e.g. the keywords declared in g_*.ml4 *)

(* Misc *)

let mp_of_global = function
  |VarRef id -> current_mp ()
  |ConstRef cst -> Names.con_modpath cst
  |IndRef ind -> Names.ind_modpath ind
  |ConstructRef constr -> Names.constr_modpath constr

let rec dp_of_mp = function
  |Names.MPfile dp -> dp
  |Names.MPbound _ -> library_dp ()
  |Names.MPdot (mp,_) -> dp_of_mp mp

let rec split_modpath = function
  |Names.MPfile dp -> dp, []
  |Names.MPbound mbid -> library_dp (), [Names.MBId.to_id mbid]
  |Names.MPdot (mp,l) ->
    let (dp,ids) = split_modpath mp in
    (dp, Names.Label.to_id l :: ids)

let library_part = function
  |VarRef id -> library_dp ()
  |ref -> dp_of_mp (mp_of_global ref)

(************************)
(* Discharging names *)

let con_defined_in_sec kn =
  let _,dir,_ = Names.repr_con kn in
  not (Names.DirPath.is_empty dir) &&
  Names.DirPath.equal (pop_dirpath dir) (current_sections ())

let defined_in_sec kn =
  let _,dir,_ = Names.repr_mind kn in
  not (Names.DirPath.is_empty dir) &&
  Names.DirPath.equal (pop_dirpath dir) (current_sections ())

let discharge_global = function
  | ConstRef kn when con_defined_in_sec kn ->
      ConstRef (Globnames.pop_con kn)
  | IndRef (kn,i) when defined_in_sec kn ->
      IndRef (Globnames.pop_kn kn,i)
  | ConstructRef ((kn,i),j) when defined_in_sec kn ->
      ConstructRef ((Globnames.pop_kn kn,i),j)
  | r -> r

let discharge_kn kn =
  if defined_in_sec kn then Globnames.pop_kn kn else kn

let discharge_con cst =
  if con_defined_in_sec cst then Globnames.pop_con cst else cst

let discharge_inductive (kn,i) =
  (discharge_kn kn,i)
