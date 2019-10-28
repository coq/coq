(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Libnames
open Libobject
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

type is_type = bool (* Module Type or just Module *)
type export = bool option (* None for a Module Type *)

(* let make_oname (dirpath,(mp,dir)) id = *)
let make_oname Nametab.{ obj_dir; obj_mp } id =
  Names.(make_path obj_dir id, KerName.make obj_mp (Label.of_id id))

(* let make_oname (dirpath,(mp,dir)) id = *)
type node =
  | Leaf of Libobject.t
  | CompilingLibrary of Nametab.object_prefix
  | OpenedModule of is_type * export * Nametab.object_prefix * Summary.frozen
  | OpenedSection of Nametab.object_prefix * Summary.frozen

type library_entry = object_name * node

type library_segment = library_entry list

type lib_atomic_objects = (Id.t * Libobject.obj) list
type lib_objects =  (Names.Id.t * Libobject.t) list

let module_kind is_type =
  if is_type then "module type" else "module"

let iter_objects f i prefix =
  List.iter (fun (id,obj) -> f i (make_oname prefix id, obj))

let load_atomic_objects i pr = iter_objects load_object i pr
let open_atomic_objects i pr = iter_objects open_object i pr

let subst_atomic_objects subst seg =
  let subst_one = fun (id,obj as node) ->
    let obj' = subst_object (subst,obj) in
      if obj' == obj then node else
	(id, obj')
  in
    List.Smart.map subst_one seg

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
          let id = Names.Label.to_id (Names.KerName.label kn) in
    begin match o with
    | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ ->
      clean ((id,o)::substl, keepl, anticipl) stk
    | KeepObject _ ->
      clean (substl, (id,o)::keepl, anticipl) stk
    | ExportObject _ ->
      clean ((id,o)::substl, keepl, anticipl) stk
    | AtomicObject obj ->
      begin match classify_object obj with
        | Dispose -> clean acc stk
        | Keep o' ->
          clean (substl, (id,AtomicObject o')::keepl, anticipl) stk
        | Substitute o' ->
          clean ((id,AtomicObject o')::substl, keepl, anticipl) stk
        | Anticipate o' ->
          clean (substl, keepl, AtomicObject o'::anticipl) stk
      end
    end
    | (_,OpenedSection _) :: _ -> user_err Pp.(str "there are still opened sections")
    | (_,OpenedModule (ty,_,_,_)) :: _ ->
      user_err ~hdr:"Lib.classify_segment"
        (str "there are still opened " ++ str (module_kind ty) ++ str "s")
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

let initial_prefix = Nametab.{
  obj_dir = default_library;
  obj_mp  = ModPath.initial;
}

type lib_state = {
  comp_name   : DirPath.t option;
  lib_stk     : library_segment;
  path_prefix : Nametab.object_prefix;
}

let initial_lib_state = {
  comp_name   = None;
  lib_stk     = [];
  path_prefix = initial_prefix;
}

let lib_state = ref initial_lib_state

let library_dp () =
  match !lib_state.comp_name with Some m -> m | None -> default_library

(* [path_prefix] is a pair of absolute dirpath and a pair of current
   module path and relative section path *)

let cwd () = !lib_state.path_prefix.Nametab.obj_dir
let current_mp () = !lib_state.path_prefix.Nametab.obj_mp
let current_sections () = Safe_typing.sections_of_safe_env (Global.safe_env())

let sections_depth () = Section.depth (current_sections())
let sections_are_opened = Global.sections_are_opened

let cwd_except_section () =
  Libnames.pop_dirpath_n (sections_depth ()) (cwd ())

let current_dirpath sec =
  Libnames.drop_dirpath_prefix (library_dp ())
    (if sec then cwd () else cwd_except_section ())

let make_path id = Libnames.make_path (cwd ()) id

let make_path_except_section id =
  Libnames.make_path (cwd_except_section ()) id

let make_kn id =
  let mp = current_mp () in
  Names.KerName.make mp (Names.Label.of_id id)

let make_foname id = make_oname !lib_state.path_prefix id

let recalc_path_prefix () =
  let rec recalc = function
    | (sp, OpenedSection (dir,_)) :: _ -> dir
    | (sp, OpenedModule (_,_,dir,_)) :: _ -> dir
    | (sp, CompilingLibrary dir) :: _ -> dir
    | _::l -> recalc l
    | [] -> initial_prefix
  in
  lib_state := { !lib_state with path_prefix = recalc !lib_state.lib_stk }

let pop_path_prefix () =
  let op = !lib_state.path_prefix in
  lib_state := { !lib_state
                 with path_prefix = Nametab.{ op with obj_dir = pop_dirpath op.obj_dir;
                                            } }

let find_entry_p p =
  let rec find = function
    | [] -> raise Not_found
    | ent::l -> if p ent then ent else find l
  in
  find !lib_state.lib_stk

let find_entries_p p =
  let rec find = function
    | [] -> []
    | ent::l -> if p ent then ent::find l else find l
  in
  find !lib_state.lib_stk

let split_lib_gen test =
  let rec collect after equal = function
    | hd::before when test hd -> collect after (hd::equal) before
    | before -> after,equal,before
  in
  let rec findeq after = function
    | hd :: before when test hd -> collect after [hd] before
    | hd :: before -> findeq (hd::after) before
    | [] -> user_err Pp.(str "no such entry")
  in
  findeq [] !lib_state.lib_stk

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
  lib_state := { !lib_state with lib_stk = (sp,node) :: !lib_state.lib_stk }

let anonymous_id =
  let n = ref 0 in
  fun () -> incr n; Names.Id.of_string ("_" ^ (string_of_int !n))

let add_anonymous_entry node =
  add_entry (make_foname (anonymous_id ())) node

let add_leaf id obj =
  if ModPath.equal (current_mp ()) ModPath.initial then
    user_err Pp.(str "No session module started (use -top dir)");
  let oname = make_foname id in
  cache_object (oname,obj);
  add_entry oname (Leaf (AtomicObject obj));
  oname

let add_discharged_leaf id obj =
  let oname = make_foname id in
  let newobj = rebuild_object obj in
  cache_object (oname,newobj);
  add_entry oname (Leaf (AtomicObject newobj))

let add_leaves id objs =
  let oname = make_foname id in
  let add_obj obj =
    add_entry oname (Leaf (AtomicObject obj));
    load_object 1 (oname,obj)
  in
  List.iter add_obj objs;
  oname

let add_anonymous_leaf ?(cache_first = true) obj =
  let id = anonymous_id () in
  let oname = make_foname id in
  if cache_first then begin
    cache_object (oname,obj);
    add_entry oname (Leaf (AtomicObject obj))
  end else begin
    add_entry oname (Leaf (AtomicObject obj));
    cache_object (oname,obj)
  end

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
    | _ -> user_err Pp.(str "you are not in a module")
  with Not_found -> user_err Pp.(str "no opened modules")


let start_mod is_type export id mp fs =
  let dir = add_dirpath_suffix (!lib_state.path_prefix.Nametab.obj_dir) id in
  let prefix = Nametab.{ obj_dir = dir; obj_mp = mp; } in
  let exists =
    if is_type then Nametab.exists_cci (make_path id)
    else Nametab.exists_dir dir
  in
  if exists then
    user_err ~hdr:"open_module" (Id.print id ++ str " already exists");
  add_entry (make_foname id) (OpenedModule (is_type,export,prefix,fs));
  lib_state := { !lib_state with path_prefix = prefix} ;
  prefix

let start_module = start_mod false
let start_modtype = start_mod true None

let error_still_opened string oname =
  let id = basename (fst oname) in
  user_err 
    (str "The " ++ str string ++ str " " ++ Id.print id ++ str " is still opened.")

let end_mod is_type =
  let oname,fs =
    try match find_entry_p is_opening_node with
      | oname,OpenedModule (ty,_,_,fs) ->
	if ty == is_type then oname, fs
	else error_still_opened (module_kind ty) oname
      | oname,OpenedSection _ -> error_still_opened "section" oname
      | _ -> assert false
    with Not_found -> user_err (Pp.str "No opened modules.")
  in
  let (after,mark,before) = split_lib_at_opening oname in
  lib_state := { !lib_state with lib_stk = before };
  let prefix = !lib_state.path_prefix in
  recalc_path_prefix ();
  (oname, prefix, fs, after)

let end_module () = end_mod false
let end_modtype () = end_mod true

let contents () = !lib_state.lib_stk

let contents_after sp = let (after,_,_) = split_lib sp in after

(* Modules. *)

(* TODO: use check_for_module ? *)
let start_compilation s mp =
  if !lib_state.comp_name != None then
    user_err Pp.(str "compilation unit is already started");
  if Global.sections_are_opened () then (* XXX not sure if we need this check *)
    user_err Pp.(str "some sections are already opened");
  let prefix = Nametab.{ obj_dir = s; obj_mp = mp } in
  add_anonymous_entry (CompilingLibrary prefix);
  lib_state := { !lib_state with comp_name = Some s;
                                 path_prefix = prefix }

let open_blocks_message es =
  let open_block_name = function
      | oname, OpenedSection _ -> str "section " ++ Id.print (basename (fst oname))
      | oname, OpenedModule (ty,_,_,_) -> str (module_kind ty) ++ spc () ++ Id.print (basename (fst oname))
      | _ -> assert false in
  str "The " ++ pr_enum open_block_name es ++ spc () ++
  str "need" ++ str (if List.length es == 1 then "s" else "") ++ str " to be closed."

let end_compilation_checks dir =
  let _ = match find_entries_p is_opening_node with
    | [] -> ()
    | es -> user_err ~hdr:"Lib.end_compilation_checks" (open_blocks_message es) in
  let is_opening_lib = function _,CompilingLibrary _ -> true | _ -> false
  in
  let oname =
    try match find_entry_p is_opening_lib with
      |	(oname, CompilingLibrary prefix) -> oname
      | _ -> assert false
    with Not_found -> anomaly (Pp.str "No module declared.")
  in
  let _ =
    match !lib_state.comp_name with
      | None -> anomaly (Pp.str "There should be a module name...")
      | Some m ->
	  if not (Names.DirPath.equal m dir) then anomaly
           (str "The current open module has name" ++ spc () ++ DirPath.print m ++
             spc () ++ str "and not" ++ spc () ++ DirPath.print m ++ str ".");
  in
  oname

let end_compilation oname =
  let (after,mark,before) = split_lib_at_opening oname in
  lib_state := { !lib_state with comp_name = None };
  !lib_state.path_prefix,after

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
      user_err ~hdr:"Lib.find_opening_node"
        (str "Last block to end has name " ++ Id.print id' ++ str ".");
    entry
  with Not_found -> user_err Pp.(str "There is nothing to end.")

(* Discharge tables *)

(* At each level of section, we remember
   - the list of variables in this section
   - the list of variables on which each constant depends in this section
   - the list of variables on which each inductive depends in this section
   - the list of substitution to do at section closing
*)

let instance_from_variable_context =
  List.rev %> List.filter is_local_assum %> List.map NamedDecl.get_id %> Array.of_list

let extract_worklist info =
  let args = instance_from_variable_context info.Section.abstr_ctx in
  info.Section.abstr_subst, args

let sections () = Safe_typing.sections_of_safe_env @@ Global.safe_env ()

let replacement_context () =
  Section.replacement_context (Global.env ()) (sections ())

let section_segment_of_constant con =
  Section.segment_of_constant (Global.env ()) con (sections ())

let section_segment_of_mutual_inductive kn =
  Section.segment_of_inductive (Global.env ()) kn (sections ())

let empty_segment = Section.empty_segment

let section_segment_of_reference = let open GlobRef in function
| ConstRef c -> section_segment_of_constant c
| IndRef (kn,_) | ConstructRef ((kn,_),_) ->
  section_segment_of_mutual_inductive kn
| VarRef _ -> empty_segment

let variable_section_segment_of_reference gr =
  (section_segment_of_reference gr).Section.abstr_ctx

let is_in_section ref =
  Section.is_in_section (Global.env ()) ref (sections ())

let section_instance = let open GlobRef in function
  | VarRef id ->
    if is_in_section (VarRef id) then (Univ.Instance.empty, [||])
    else raise Not_found
  | ConstRef con ->
    let data = section_segment_of_constant con in
    extract_worklist data
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
    let data = section_segment_of_mutual_inductive kn in
    extract_worklist data

(*************)
(* Sections. *)
let open_section id =
  let () = Global.open_section () in
  let opp = !lib_state.path_prefix in
  let obj_dir = add_dirpath_suffix opp.Nametab.obj_dir id in
  let prefix = Nametab.{ obj_dir; obj_mp = opp.obj_mp; } in
  if Nametab.exists_dir obj_dir then
    user_err ~hdr:"open_section" (Id.print id ++ str " already exists.");
  let fs = Summary.freeze_summaries ~marshallable:false in
  add_entry (make_foname id) (OpenedSection (prefix, fs));
  (*Pushed for the lifetime of the section: removed by unfrozing the summary*)
  Nametab.(push_dir (Until 1) obj_dir (GlobDirRef.DirOpenSection prefix));
  lib_state := { !lib_state with path_prefix = prefix }

(* Restore lib_stk and summaries as before the section opening, and
   add a ClosedSection object. *)

let discharge_item ((sp,_ as oname),e) =
  match e with
  | Leaf lobj ->
    begin match lobj with
    | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | KeepObject _
    | ExportObject _ -> None
    | AtomicObject obj ->
      Option.map (fun o -> (basename sp,o)) (discharge_object (oname,obj))
    end
  | OpenedSection _ | OpenedModule _ | CompilingLibrary _ ->
      anomaly (Pp.str "discharge_item.")

let close_section () =
  let oname,fs =
    try match find_entry_p is_opening_node with
      | oname,OpenedSection (_,fs) -> oname,fs
      | _ -> assert false
    with Not_found ->
      user_err Pp.(str  "No opened section.")
  in
  let (secdecls,mark,before) = split_lib_at_opening oname in
  lib_state := { !lib_state with lib_stk = before };
  pop_path_prefix ();
  let newdecls = List.map discharge_item secdecls in
  let () = Global.close_section fs in
  List.iter (Option.iter (fun (id,o) -> add_discharged_leaf id o)) newdecls

(* State and initialization. *)

type frozen = lib_state

let freeze ~marshallable = !lib_state

let unfreeze st = lib_state := st

let drop_objects st =
  let lib_stk =
    CList.map_filter (function
        | _, Leaf _ -> None
        | n, (CompilingLibrary _ as x) -> Some (n,x)
        | n, OpenedModule (it,e,op,_) ->
          Some(n,OpenedModule(it,e,op,Summary.empty_frozen))
        | n, OpenedSection (op, _) ->
          Some(n,OpenedSection(op,Summary.empty_frozen)))
      st.lib_stk in
  { st with lib_stk }

let init () =
  unfreeze initial_lib_state;
  Summary.init_summaries ()

(* Misc *)

let mp_of_global = let open GlobRef in function
  | VarRef id -> !lib_state.path_prefix.Nametab.obj_mp
  | ConstRef cst -> Names.Constant.modpath cst
  | IndRef ind -> Names.ind_modpath ind
  | ConstructRef constr -> Names.constr_modpath constr

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
  | GlobRef.VarRef id -> library_dp ()
  | ref -> dp_of_mp (mp_of_global ref)

let discharge_proj_repr =
  Projection.Repr.map_npars (fun mind npars ->
      if not (is_in_section (GlobRef.IndRef (mind,0))) then mind, npars
      else let modlist = replacement_context () in
      let _, newpars = Mindmap.find mind (snd modlist) in
      mind, npars + Array.length newpars)

let discharge_abstract_universe_context { Section.abstr_subst = subst; abstr_uctx = abs_ctx } auctx =
  let open Univ in
  let ainst = make_abstract_instance auctx in
  let subst = Instance.append subst ainst in
  let subst = make_instance_subst subst in
  let auctx = Univ.subst_univs_level_abstract_universe_context subst auctx in
  subst, AUContext.union abs_ctx auctx
