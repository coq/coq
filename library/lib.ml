(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

type is_type = bool (* Module Type or just Module *)
type export_flag = Export | Import
type export = (export_flag * Libobject.open_filter) option (* None for a Module Type *)

let make_oname Nametab.{ obj_dir; obj_mp } id =
  Names.(make_path obj_dir id, KerName.make obj_mp (Label.of_id id))

let oname_prefix (sp, kn) =
  { Nametab.obj_dir = Libnames.dirpath sp; obj_mp = KerName.modpath kn }

type node =
  | CompilingLibrary of Nametab.object_prefix
  | OpenedModule of is_type * export * Nametab.object_prefix * Summary.frozen
  | OpenedSection of Nametab.object_prefix * Summary.frozen

let node_prefix = function
  | CompilingLibrary prefix
  | OpenedModule (_,_,prefix,_)
  | OpenedSection (prefix,_) -> prefix

let prefix_id prefix = snd (split_dirpath prefix.Nametab.obj_dir)

type library_segment = (node * Libobject.t list) list

type classified_objects = {
  substobjs : Libobject.t list;
  keepobjs : Libobject.t list;
  anticipateobjs : Libobject.t list;
}

let module_kind is_type =
  if is_type then "module type" else "module"

(*let load_and_subst_objects i prefix subst seg =
  List.rev (List.fold_left (fun seg (id,obj as node) ->
    let obj' =  subst_object (make_oname prefix id, subst, obj) in
    let node = if obj == obj' then node else (id, obj') in
    load_object i (make_oname prefix id, obj');
    node :: seg) [] seg)
*)
let classify_segment seg =
  let rec clean ((substl,keepl,anticipl) as acc) = function
    | [] -> acc
    | o :: stk ->
      begin match o with
        | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ ->
          clean (o::substl, keepl, anticipl) stk
        | KeepObject _ ->
          clean (substl, o::keepl, anticipl) stk
        | ExportObject _ ->
          clean (o::substl, keepl, anticipl) stk
        | AtomicObject obj as o ->
          begin match classify_object obj with
            | Dispose -> clean acc stk
            | Keep ->
              clean (substl, o::keepl, anticipl) stk
            | Substitute ->
              clean (o::substl, keepl, anticipl) stk
            | Anticipate ->
              clean (substl, keepl, o::anticipl) stk
          end
      end
  in
  clean ([],[],[]) (List.rev seg)

let classify_segment seg =
  let substobjs, keepobjs, anticipateobjs = classify_segment seg in
  { substobjs; keepobjs; anticipateobjs; }

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

let prefix () = !lib_state.path_prefix
let cwd () = !lib_state.path_prefix.Nametab.obj_dir
let current_mp () = !lib_state.path_prefix.Nametab.obj_mp
let current_sections () = Safe_typing.sections_of_safe_env (Global.safe_env())

let sections_depth () = match current_sections() with
  | None -> 0
  | Some sec -> Section.depth sec

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

let find_entries_p p =
  let rec find = function
    | [] -> []
    | (ent,_)::l -> if p ent then ent::find l else find l
  in
  find !lib_state.lib_stk

(* Adding operations. *)

let add_entry node =
  lib_state := { !lib_state with lib_stk = (node,[]) :: !lib_state.lib_stk }

let dummylib = CompilingLibrary
    {Nametab.obj_dir = DirPath.initial;
     Nametab.obj_mp = ModPath.MPfile DirPath.initial;
    }

let add_leaf_entry leaf =
  let lib_stk = match !lib_state.lib_stk with
    | [] ->
      (* top_printers does set_bool_option_value which adds a leaf *)
      if !Flags.in_debugger then [dummylib, [leaf]] else assert false
    | (node, leaves) :: rest -> (node, leaf :: leaves) :: rest
  in
  lib_state := { !lib_state with lib_stk }

let add_discharged_leaf obj =
  let newobj = rebuild_object obj in
  cache_object (prefix(),newobj);
  add_leaf_entry (AtomicObject newobj)

let add_leaf obj =
  cache_object (prefix(),obj);
  add_leaf_entry (AtomicObject obj)

(* Modules. *)

let is_opening_node = function
  | OpenedSection _ | OpenedModule _ -> true
  | _ -> false

let start_mod is_type export id mp fs =
  let dir = add_dirpath_suffix (!lib_state.path_prefix.Nametab.obj_dir) id in
  let prefix = Nametab.{ obj_dir = dir; obj_mp = mp; } in
  let exists =
    if is_type then Nametab.exists_cci (make_path id)
    else Nametab.exists_module dir
  in
  if exists then
    user_err (Id.print id ++ str " already exists.");
  add_entry (OpenedModule (is_type,export,prefix,fs));
  lib_state := { !lib_state with path_prefix = prefix} ;
  prefix

let start_module = start_mod false
let start_modtype = start_mod true None

let split_lib_at_opening () =
  match !lib_state.lib_stk with
  | [] -> assert false
  | (node,leaves) :: rest -> List.rev leaves, node, rest

let error_still_opened string oname =
  let id = prefix_id oname in
  user_err
    (str "The " ++ str string ++ str " " ++ Id.print id ++ str " is still opened.")

let recalc_path_prefix () =
  let path_prefix = match pi2 (split_lib_at_opening ()) with
    | CompilingLibrary dir
    | OpenedModule (_, _, dir, _)
    | OpenedSection (dir, _) -> dir
  in
  lib_state := { !lib_state with path_prefix }

let pop_path_prefix () =
  let op = !lib_state.path_prefix in
  lib_state := {
    !lib_state
    with path_prefix = Nametab.{
        op with obj_dir = pop_dirpath op.obj_dir;
      } }

let end_mod is_type =
  let (after,mark,before) = split_lib_at_opening () in
  (* The errors here should not happen because we checked in the upper layers *)
  let prefix, fs = match mark with
    | OpenedModule (ty,_,prefix,fs) ->
      if ty == is_type then prefix, fs
      else error_still_opened (module_kind ty) prefix
    | OpenedSection (prefix, _) -> error_still_opened "section" prefix
    | CompilingLibrary _ -> user_err (Pp.str "No opened modules.")
  in
  lib_state := { !lib_state with lib_stk = before };
  recalc_path_prefix ();
  let after = classify_segment after in
  (prefix, fs, after)

let end_module () = end_mod false
let end_modtype () = end_mod true

let contents () = !lib_state.lib_stk

(* Modules. *)

(* TODO: use check_for_module ? *)
let start_compilation s mp =
  if !lib_state.comp_name != None then
    user_err Pp.(str "compilation unit is already started");
  assert (List.is_empty !lib_state.lib_stk);
  if Global.sections_are_opened () then (* XXX not sure if we need this check *)
    user_err Pp.(str "some sections are already opened");
  let prefix = Nametab.{ obj_dir = s; obj_mp = mp } in
  lib_state := {
    comp_name = Some s;
    path_prefix = prefix;
    lib_stk = [ CompilingLibrary prefix, [] ];
  }

let open_blocks_message es =
  let open_block_name = function
    | OpenedSection (prefix,_) ->
      str "section " ++ Id.print (prefix_id prefix)
    | OpenedModule (ty,_,prefix,_) ->
      str (module_kind ty) ++ spc () ++ Id.print (prefix_id prefix)
    | _ -> assert false
  in
  str "The " ++ pr_enum open_block_name es ++ spc () ++
  str "need" ++ str (if List.length es == 1 then "s" else "") ++ str " to be closed."

let end_compilation_checks dir =
  let () = match find_entries_p is_opening_node with
    | [] -> ()
    | es -> user_err (open_blocks_message es) in
  let () =
    match !lib_state.comp_name with
      | None -> anomaly (Pp.str "There should be a module name...")
      | Some m ->
          if not (Names.DirPath.equal m dir) then anomaly
           (str "The current open module has name" ++ spc () ++ DirPath.print m ++
             spc () ++ str "and not" ++ spc () ++ DirPath.print m ++ str ".");
  in
  ()

let end_compilation dir =
  end_compilation_checks dir;
  let (after,mark,before) = split_lib_at_opening () in
  assert (List.is_empty before);
  lib_state := { !lib_state with comp_name = None };
  let after = classify_segment after in
  !lib_state.path_prefix, after

(* Returns true if we are inside an opened module or module type *)
let is_module_or_modtype () =
  match Safe_typing.module_is_modtype (Global.safe_env ()) with
  | [] -> false
  | _ -> true

let is_modtype () =
  let modules = Safe_typing.module_is_modtype (Global.safe_env ()) in
  List.exists (fun x -> x) modules

let is_modtype_strict () =
  match Safe_typing.module_is_modtype (Global.safe_env ()) with
  | b :: _ -> b
  | [] -> false

let is_module () =
  let modules = Safe_typing.module_is_modtype (Global.safe_env ()) in
  List.exists (fun x -> not x) modules

(* Returns the opening node of a given name *)
let find_opening_node id =
  let entry = match !lib_state.lib_stk with
    | [] -> assert false
    | (CompilingLibrary _, _) :: _ -> user_err Pp.(str "There is nothing to end.")
    | (entry, _) :: _ -> entry
  in
  let id' = prefix_id (node_prefix entry) in
  if not (Names.Id.equal id id') then
    user_err
      (str "Last block to end has name " ++ Id.print id' ++ str ".");
  entry

(* Discharge tables *)

(* At each level of section, we remember
   - the list of variables in this section
   - the list of variables on which each constant depends in this section
   - the list of variables on which each inductive depends in this section
   - the list of substitution to do at section closing
*)

let sections () = Safe_typing.sections_of_safe_env @@ Global.safe_env ()

let force_sections () = match Safe_typing.sections_of_safe_env (Global.safe_env()) with
  | Some s -> s
  | None -> CErrors.user_err Pp.(str "No open section.")

let section_segment_of_constant con =
  Section.segment_of_constant con (force_sections ())

let section_segment_of_inductive kn =
  Section.segment_of_inductive kn (force_sections ())

let section_segment_of_reference = let open GlobRef in function
| ConstRef c -> section_segment_of_constant c
| IndRef (kn,_) | ConstructRef ((kn,_),_) ->
  section_segment_of_inductive kn
| VarRef _ -> Cooking.empty_cooking_info

let is_in_section ref = match sections () with
  | None -> false
  | Some sec ->
    Section.is_in_section (Global.env ()) ref sec

let section_instance ref =
  Cooking.instance_of_cooking_info (section_segment_of_reference ref)

(*************)
(* Sections. *)
let open_section id =
  let () = Global.open_section () in
  let opp = !lib_state.path_prefix in
  let obj_dir = add_dirpath_suffix opp.Nametab.obj_dir id in
  let prefix = Nametab.{ obj_dir; obj_mp = opp.obj_mp; } in
  if Nametab.exists_dir obj_dir then
    user_err (Id.print id ++ str " already exists.");
  let fs = Summary.freeze_summaries ~marshallable:false in
  add_entry (OpenedSection (prefix, fs));
  (*Pushed for the lifetime of the section: removed by unfrozing the summary*)
  Nametab.(push_dir (Until 1) obj_dir (GlobDirRef.DirOpenSection prefix));
  lib_state := { !lib_state with path_prefix = prefix }

(* Restore lib_stk and summaries as before the section opening, and
   add a ClosedSection object. *)

let discharge_item = function
  | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | KeepObject _
  | ExportObject _ -> None
  | AtomicObject obj -> discharge_object obj

let close_section () =
  let (secdecls,mark,before) = split_lib_at_opening () in
  let fs = match mark with
    | OpenedSection (_,fs) -> fs
    | _ -> user_err Pp.(str "No opened section.")
  in
  lib_state := { !lib_state with lib_stk = before };
  pop_path_prefix ();
  let newdecls = List.map discharge_item secdecls in
  let () = Global.close_section fs in
  List.iter (Option.iter add_discharged_leaf) newdecls

(* State and initialization. *)

type frozen = lib_state

let freeze () = !lib_state

let unfreeze st = lib_state := st

let drop_objects st =
  let drop_node = function
    | CompilingLibrary _ as x -> x
    | OpenedModule (it,e,op,_) ->
      OpenedModule(it,e,op,Summary.empty_frozen)
    | OpenedSection (op, _) ->
      OpenedSection(op,Summary.empty_frozen)
  in
  let lib_stk = List.map (fun (node,_) -> drop_node node, []) st.lib_stk in
  { st with lib_stk }

let init () =
  unfreeze initial_lib_state;
  Summary.init_summaries ()

(* Misc *)

let mp_of_global = let open GlobRef in function
  | VarRef id -> !lib_state.path_prefix.Nametab.obj_mp
  | ConstRef cst -> Names.Constant.modpath cst
  | IndRef ind -> Names.Ind.modpath ind
  | ConstructRef constr -> Names.Construct.modpath constr

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

let discharge_proj_repr p =
  let ind = Projection.Repr.inductive p in
  let sec = section_segment_of_reference (GlobRef.IndRef ind) in
  Cooking.discharge_proj_repr sec p
