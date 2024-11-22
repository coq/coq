(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

type is_type = bool (* Module Type or just Module *)
type export_flag = Export | Import
type export = (export_flag * Libobject.open_filter) option (* None for a Module Type *)

let make_oname Nametab.{ obj_dir; obj_mp } id =
  Names.(Libnames.make_path obj_dir id, KerName.make obj_mp (Label.of_id id))

let oname_prefix (sp, kn) =
  { Nametab.obj_dir = Libnames.dirpath sp; obj_mp = KerName.modpath kn }

type 'summary node =
  | CompilingLibrary of Nametab.object_prefix
  | OpenedModule of is_type * export * Nametab.object_prefix * 'summary
  | OpenedSection of Nametab.object_prefix * 'summary

let node_prefix = function
  | CompilingLibrary prefix
  | OpenedModule (_,_,prefix,_)
  | OpenedSection (prefix,_) -> prefix

let prefix_id prefix = snd (Libnames.split_dirpath prefix.Nametab.obj_dir)

type 'summary library_segment = ('summary node * Libobject.t list) list

let module_kind is_type =
  if is_type then "module type" else "module"

type classified_objects = {
  substobjs : Libobject.t list;
  keepobjs : Libobject.t list;
  escapeobjs : Libobject.t list;
  anticipateobjs : Libobject.t list;
}

let empty_classified = {
  substobjs = [];
  keepobjs = [];
  escapeobjs = [];
  anticipateobjs = [];
}

let classify_object : Libobject.t -> Libobject.substitutivity = function
  | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | ExportObject _ -> Substitute
  | KeepObject _ -> Keep
  | EscapeObject _ -> Escape
  | AtomicObject o -> Libobject.classify_object o

let classify_segment seg =
  let rec clean acc = function
    | [] -> acc
    | o :: stk ->
      begin match classify_object o with
      | Dispose -> clean acc stk
      | Substitute ->
        clean {acc with substobjs = o :: acc.substobjs} stk
      | Keep ->
        clean {acc with keepobjs = o :: acc.keepobjs} stk
      | Escape ->
        clean {acc with escapeobjs = o :: acc.escapeobjs} stk
      | Anticipate ->
        clean {acc with anticipateobjs = o :: acc.anticipateobjs} stk
      end
  in
  clean empty_classified (List.rev seg)

let find_entries_p p stk =
  let rec find = function
    | [] -> []
    | (ent,_)::l -> if p ent then ent::find l else find l
  in
  find stk

let split_lib_at_opening stk =
  match stk with
  | [] -> assert false
  | (node,leaves) :: rest -> List.rev leaves, node, rest

let is_opening_node = function
  | OpenedSection _ | OpenedModule _ -> true
  | CompilingLibrary _ -> false

let open_blocks_message es =
  let open Pp in
  let open_block_name = function
    | OpenedSection (prefix,_) ->
      str "section " ++ Id.print (prefix_id prefix)
    | OpenedModule (ty,_,prefix,_) ->
      str (module_kind ty) ++ spc () ++ Id.print (prefix_id prefix)
    | _ -> assert false
  in
  str "The " ++ pr_enum open_block_name es ++ spc () ++
  str "need" ++ str (if List.length es == 1 then "s" else "") ++
  str " to be closed."

(* We keep trace of operations in the stack [lib_stk].
   [path_prefix] is the current path of sections, where sections are stored in
   ``correct'' order, the oldest coming first in the list. It may seems
   costly, but in practice there is not so many openings and closings of
   sections, but on the contrary there are many constructions of section
   paths based on the library path. *)

let dummy_prefix = Nametab.{
  obj_dir = DirPath.dummy;
  obj_mp  = ModPath.dummy;
}

type synterp_state = {
  comp_name : DirPath.t option;
  lib_stk : Summary.Synterp.frozen library_segment;
  path_prefix : Nametab.object_prefix;
}

let dummy = {
  comp_name = None;
  lib_stk = [];
  path_prefix = dummy_prefix;
}

(** The lib state is split in two components:
  - The synterp stage state which manages a recording of syntax-related objects and naming-related data (compilation unit name, current prefix).
  - The interp stage state which manages a recording of regular objects.
*)

let synterp_state = ref dummy
let interp_state = ref ([] : Summary.Interp.frozen library_segment)

let library_info = ref UserWarn.empty

let contents () = !interp_state

let start_compilation s mp =
  if !synterp_state.comp_name != None then
    CErrors.user_err Pp.(str "compilation unit is already started");
  assert (List.is_empty !synterp_state.lib_stk);
  assert (List.is_empty !interp_state);
  if Global.sections_are_opened () then (* XXX not sure if we need this check *)
    CErrors.user_err Pp.(str "some sections are already opened");
  let prefix = Nametab.{ obj_dir = s; obj_mp = mp } in
  let initial_stk = [ CompilingLibrary prefix, [] ] in
  let st = {
    comp_name = Some s;
    path_prefix = prefix;
    lib_stk = initial_stk;
  }
  in
  synterp_state := st;
  interp_state := initial_stk

let end_compilation_checks dir =
  let () = match find_entries_p is_opening_node !interp_state with
    | [] -> ()
    | es -> CErrors.user_err (open_blocks_message es) in
  let () =
    match !synterp_state.comp_name with
      | None -> CErrors.anomaly (Pp.str "There should be a module name...")
      | Some m ->
          if not (Names.DirPath.equal m dir) then
            CErrors.anomaly Pp.(str "The current open module has name"
              ++ spc () ++ DirPath.print m ++ spc () ++ str "and not"
              ++ spc () ++ DirPath.print m ++ str ".");
  in
  ()

let library_dp () =
  match !synterp_state.comp_name with Some m -> m | None -> DirPath.dummy

(* [path_prefix] is a pair of absolute dirpath and a pair of current
   module path and relative section path *)

let prefix () = !synterp_state.path_prefix
let cwd () = !synterp_state.path_prefix.Nametab.obj_dir
let current_mp () = !synterp_state.path_prefix.Nametab.obj_mp

let sections_depth () =
  !synterp_state.lib_stk |> List.count (function
      | (OpenedSection _, _) -> true
      | ((OpenedModule _ | CompilingLibrary _), _) -> false)

let sections_are_opened () =
  match split_lib_at_opening !synterp_state.lib_stk with
  | (_, OpenedSection _, _) -> true
  | _ -> false

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

let make_foname id = make_oname !synterp_state.path_prefix id

(* Adding operations. *)

let dummylib = CompilingLibrary dummy_prefix

let error_still_opened s oname =
  CErrors.user_err Pp.(str "The " ++ str s ++ str " "
    ++ Id.print (prefix_id oname) ++ str " is still opened.")

let recalc_path_prefix () =
  let path_prefix = match pi2 (split_lib_at_opening !synterp_state.lib_stk) with
    | CompilingLibrary dir
    | OpenedModule (_, _, dir, _)
    | OpenedSection (dir, _) -> dir
  in
  synterp_state := { !synterp_state with path_prefix }

let pop_path_prefix () =
  let op = !synterp_state.path_prefix in
  synterp_state := {
    !synterp_state
    with path_prefix = Nametab.{
        op with obj_dir = Libnames.pop_dirpath op.obj_dir;
      } }

(* Modules. *)

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

type discharged_item =
  | DischargedExport of Libobject.ExportObj.t
  | DischargedLeaf of Libobject.discharged_obj

let discharge_item = Libobject.(function
  | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | KeepObject _ | EscapeObject _ ->
    assert false
  | ExportObject o -> Some (DischargedExport o)
  | AtomicObject obj ->
    let obj = discharge_object obj in
    Option.map (fun o -> DischargedLeaf o) obj)

(* Misc *)

let mp_of_global = let open GlobRef in function
  | VarRef id -> !synterp_state.path_prefix.Nametab.obj_mp
  | ConstRef cst -> Names.Constant.modpath cst
  | IndRef ind -> Names.Ind.modpath ind
  | ConstructRef constr -> Names.Construct.modpath constr

let rec split_modpath = function
  |Names.MPfile dp -> dp, []
  |Names.MPbound mbid -> library_dp (), [Names.MBId.to_id mbid]
  |Names.MPdot (mp,l) ->
    let (dp,ids) = split_modpath mp in
    (dp, Names.Label.to_id l :: ids)

let library_part = function
  | GlobRef.VarRef id -> library_dp ()
  | ref -> ModPath.dp (mp_of_global ref)

let discharge_section_proj_repr p =
  let ind = Projection.Repr.inductive p in
  let sec = section_segment_of_reference (GlobRef.IndRef ind) in
  Cooking.discharge_proj_repr sec p

let discharge_proj_repr p =
    if is_in_section (Names.GlobRef.IndRef (Names.Projection.Repr.inductive p)) then
      discharge_section_proj_repr p
    else
      p

let debug_object_name = function
  | Libobject.ModuleObject _ -> "ModuleObject"
  | ModuleTypeObject  _-> "ModuleTypeObject"
  | IncludeObject _ -> "IncludeObject"
  | KeepObject _ -> "KeepObject"
  | EscapeObject _ -> "EscapeObject"
  | ExportObject _ -> "ExportObject"
  | AtomicObject (Dyn (tag,_)) -> Libobject.Dyn.repr tag

let anomaly_unitialized_add_leaf stage o =
  CErrors.anomaly
    Pp.(str "cannot add object (" ++ str (debug_object_name o) ++ pr_comma() ++
        str "in " ++ str stage ++ str "): not initialized")

(** The [LibActions] abstraction represent the set of operations on the Lib
    structure that is specific to a given stage. Two instances are defined below,
    for Synterp and Interp. *)
module type LibActions = sig

  type summary
  val stage : Summary.Stage.t
  val check_mod_fresh : is_type:bool -> Nametab.object_prefix -> Id.t -> unit
  val check_section_fresh : DirPath.t -> Id.t -> unit
  val open_section : Id.t -> unit

  val push_section_name : DirPath.t -> unit

  val close_section : summary -> unit

  val add_entry : summary node -> unit
  val add_leaf_entry : Libobject.t -> unit
  val start_mod : is_type:is_type -> export -> Id.t -> ModPath.t -> summary -> Nametab.object_prefix

  val get_lib_stk : unit -> summary library_segment
  val set_lib_stk : summary library_segment -> unit

  val pop_path_prefix : unit -> unit
  val recalc_path_prefix : unit -> unit

  type frozen
  val freeze : unit -> frozen
  val unfreeze : frozen -> unit
  val init : unit -> unit

  val drop_objects : frozen -> frozen

  val declare_info : Library_info.t -> unit

end

module SynterpActions : LibActions with type summary = Summary.Synterp.frozen = struct

  type summary = Summary.Synterp.frozen
  let stage = Summary.Stage.Synterp

  let check_mod_fresh ~is_type prefix id =
    let exists =
      if is_type then Nametab.exists_cci (Libnames.make_path prefix.Nametab.obj_dir id)
      else Nametab.exists_module prefix.Nametab.obj_dir
    in
    if exists then
      CErrors.user_err Pp.(Id.print id ++ str " already exists.")

  let check_section_fresh obj_dir id =
    if Nametab.exists_dir obj_dir then
      CErrors.user_err Pp.(Id.print id ++ str " already exists.")

  let push_section_name obj_dir =
    Nametab.(push_dir (Until 1) obj_dir (GlobDirRef.DirOpenSection obj_dir))

  let close_section fs = Summary.Synterp.unfreeze_summaries fs

  let add_entry node =
    synterp_state := { !synterp_state with lib_stk = (node,[]) :: !synterp_state.lib_stk }

  let add_leaf_entry leaf =
    let lib_stk = match !synterp_state.lib_stk with
      | [] ->
        (* top_printers does set_bool_option_value which adds a leaf *)
        if !Flags.in_debugger then [dummylib, [leaf]] else anomaly_unitialized_add_leaf "synterp" leaf
      | (node, leaves) :: rest -> (node, leaf :: leaves) :: rest
    in
    synterp_state := { !synterp_state with lib_stk }

  (* Returns the opening node of a given name *)
  let start_mod ~is_type export id mp fs =
    let dir = Libnames.add_dirpath_suffix !synterp_state.path_prefix.Nametab.obj_dir id in
    let prefix = Nametab.{ obj_dir = dir; obj_mp = mp; } in
    check_mod_fresh ~is_type prefix id;
    assert (not (sections_are_opened()));
    add_entry (OpenedModule (is_type,export,prefix,fs));
    synterp_state := { !synterp_state with path_prefix = prefix } ;
    prefix

  let get_lib_stk () =
    !synterp_state.lib_stk

  let set_lib_stk stk =
    synterp_state := { !synterp_state with lib_stk = stk }

  let open_section id =
    let opp = !synterp_state.path_prefix in
    let obj_dir = Libnames.add_dirpath_suffix opp.Nametab.obj_dir id in
    let prefix = Nametab.{ obj_dir; obj_mp=opp.obj_mp; } in
    check_section_fresh obj_dir id;
    let fs = Summary.Synterp.freeze_summaries () in
    add_entry (OpenedSection (prefix, fs));
    (*Pushed for the lifetime of the section: removed by unfreezing the summary*)
    push_section_name obj_dir;
    synterp_state := { !synterp_state with path_prefix = prefix }

  let pop_path_prefix () = pop_path_prefix ()
  let recalc_path_prefix () = recalc_path_prefix ()

  type frozen = synterp_state

  let freeze () = !synterp_state

  let unfreeze st =
    synterp_state := st

  let init () =
    synterp_state := dummy

  let drop_objects st =
    let drop_node = function
      | CompilingLibrary _ as x -> x
      | OpenedModule (it,e,op,_) ->
        OpenedModule(it,e,op,Summary.Synterp.empty_frozen)
      | OpenedSection (op, _) ->
        OpenedSection(op,Summary.Synterp.empty_frozen)
    in
    let lib_synterp_stk = List.map (fun (node,_) -> drop_node node, []) st.lib_stk in
    { st with lib_stk = lib_synterp_stk }

  let declare_info info =
    let open UserWarn in
    let depr = match !library_info.depr, info.depr with
      | None, depr | depr, None -> depr
      | Some _, Some _ ->
         CErrors.user_err Pp.(str "Library file is already deprecated.") in
    let warn = !library_info.warn @ info.warn in
    library_info := { depr; warn }

end

module InterpActions : LibActions with type summary = Summary.Interp.frozen = struct

  type summary = Summary.Interp.frozen

  let stage = Summary.Stage.Interp

  let check_mod_fresh ~is_type prefix id = ()
  let check_section_fresh _ _ = ()

  let push_section_name _ = ()
  let close_section fs = Global.close_section fs

  let add_entry node =
    interp_state := (node,[]) :: !interp_state

  let add_leaf_entry leaf =
    let lib_stk = match !interp_state with
      | [] ->
        (* top_printers does set_bool_option_value which adds a leaf *)
        if !Flags.in_debugger then [dummylib, [leaf]] else anomaly_unitialized_add_leaf "interp" leaf
      | (node, leaves) :: rest -> (node, leaf :: leaves) :: rest
    in
    interp_state := lib_stk

  (* Returns the opening node of a given name *)
  let start_mod ~is_type export id mp fs =
    let prefix = !synterp_state.path_prefix in
    add_entry (OpenedModule (is_type,export,prefix,fs));
    prefix

  let get_lib_stk () =
    !interp_state

  let set_lib_stk stk =
    interp_state := stk

  let open_section id =
    Global.open_section ();
    let prefix = !synterp_state.path_prefix in
    let fs = Summary.Interp.freeze_summaries () in
    add_entry (OpenedSection (prefix, fs))

  let pop_path_prefix () = ()
  let recalc_path_prefix () = ()

  type frozen = summary library_segment

  let freeze () = !interp_state

  let unfreeze st =
    interp_state := st

  let init () =
    interp_state := []

  let drop_objects interp_state =
    let drop_node = function
      | CompilingLibrary _ as x -> x
      | OpenedModule (it,e,op,_) ->
        OpenedModule(it,e,op,Summary.Interp.empty_frozen)
      | OpenedSection (op, _) ->
        OpenedSection(op,Summary.Interp.empty_frozen)
    in
    List.map (fun (node,_) -> drop_node node, []) interp_state

  let declare_info _ = ()

end

let add_discharged_leaf obj =
  let newobj = Libobject.rebuild_object obj in
  Libobject.cache_object (prefix(),newobj);
  match Libobject.object_stage newobj with
  | Summary.Stage.Synterp ->
    SynterpActions.add_leaf_entry (AtomicObject newobj)
  | Summary.Stage.Interp ->
    InterpActions.add_leaf_entry (AtomicObject newobj)

let add_leaf obj =
  Libobject.cache_object (prefix(),obj);
  match Libobject.object_stage obj with
  | Summary.Stage.Synterp ->
    SynterpActions.add_leaf_entry (AtomicObject obj)
  | Summary.Stage.Interp ->
    InterpActions.add_leaf_entry (AtomicObject obj)

module type StagedLibS = sig

  type summary

  val find_opening_node : ?loc:Loc.t -> Id.t -> summary node

  val add_entry : summary node -> unit
  val add_leaf_entry : Libobject.t -> unit

  (** {6 Sections } *)
  val open_section : Id.t -> unit
  val close_section : unit -> discharged_item list

  (** {6 Modules and module types } *)
  val start_module :
    export -> module_ident -> ModPath.t ->
    summary -> Nametab.object_prefix

  val start_modtype :
    module_ident -> ModPath.t ->
    summary -> Nametab.object_prefix

  val end_module :
    unit ->
    Nametab.object_prefix * summary * classified_objects

  val end_modtype :
    unit ->
    Nametab.object_prefix * summary * classified_objects

  type frozen

  val freeze : unit -> frozen
  val unfreeze : frozen -> unit
  val init : unit -> unit

  val drop_objects : frozen -> frozen

  val declare_info : Library_info.t -> unit

end

(** The [StagedLib] abstraction factors out the code dealing with Lib structure
    that is common to all stages. *)
module StagedLib(Actions : LibActions) : StagedLibS with type summary = Actions.summary = struct

type summary = Actions.summary

let add_entry node = Actions.add_entry node
let add_leaf_entry obj = Actions.add_leaf_entry obj

let open_section id = Actions.open_section id

exception WrongClosingBlockName of Id.t * Loc.t option

let () = CErrors.register_handler (function
  | WrongClosingBlockName (id,_) ->
    Some Pp.(str "Last block to end has name " ++ Id.print id ++ str ".")
  | _ -> None)

let () = Quickfix.register (function
  | WrongClosingBlockName (id, Some loc) -> [Quickfix.make ~loc (Id.print id)]
  | _ -> [])

let find_opening_node ?loc id =
  let entry = match Actions.get_lib_stk () with
    | [] -> assert false
    | (CompilingLibrary _, _) :: _ ->
        CErrors.user_err Pp.(str "There is nothing to end.")
    | (entry, _) :: _ -> entry
  in
  let id' = prefix_id (node_prefix entry) in
  if not (Names.Id.equal id id') then
    Loc.raise ?loc (WrongClosingBlockName(id',loc));
  entry

let start_module = Actions.start_mod ~is_type:false
let start_modtype = Actions.start_mod ~is_type:true None

let end_mod ~is_type =
  let (after,mark,before) = split_lib_at_opening (Actions.get_lib_stk ()) in
  (* The errors here should not happen because we checked in the upper layers *)
  let prefix, fs = match mark with
    | OpenedModule (ty,_,prefix,fs) ->
      if ty == is_type then prefix, fs
      else error_still_opened (module_kind ty) prefix
    | OpenedSection (prefix, _) -> error_still_opened "section" prefix
    | CompilingLibrary _ -> CErrors.user_err (Pp.str "No opened modules.")
  in
  Actions.set_lib_stk before;
  Actions.recalc_path_prefix ();
  let after = classify_segment after in
  (prefix, fs, after)

let end_module () = end_mod ~is_type:false
let end_modtype () = end_mod ~is_type:true

(* Restore lib_stk and summaries as before the section opening, and
   add a ClosedSection object. *)
let close_section () =
  let (secdecls,mark,before) = split_lib_at_opening (Actions.get_lib_stk ()) in
  let fs = match mark with
    | OpenedSection (_,fs) -> fs
    | _ -> CErrors.user_err Pp.(str "No opened section.")
  in
  Actions.set_lib_stk before;
  Actions.pop_path_prefix ();
  let newdecls = List.filter_map discharge_item secdecls in
  Actions.close_section fs;
  newdecls

type frozen = Actions.frozen

let freeze () = Actions.freeze ()

let unfreeze st = Actions.unfreeze st

let init () = Actions.init ()

let drop_objects st = Actions.drop_objects st

let declare_info info = Actions.declare_info info

end

module Synterp : StagedLibS with type summary = Summary.Synterp.frozen = StagedLib(SynterpActions)
module Interp : StagedLibS with type summary = Summary.Interp.frozen = StagedLib(InterpActions)

type compilation_result = {
  info : Library_info.t;
  synterp_objects : classified_objects;
  interp_objects : classified_objects;
}

let end_compilation dir =
  end_compilation_checks dir;
  let (syntax_after,_,syntax_before) = split_lib_at_opening !synterp_state.lib_stk in
  let (after,_,before) = split_lib_at_opening !interp_state in
  assert (List.is_empty syntax_before);
  assert (List.is_empty before);
  synterp_state := { !synterp_state with comp_name = None };
  let syntax_after = classify_segment syntax_after in
  let after = classify_segment after in
  { info = !library_info; interp_objects = after; synterp_objects = syntax_after; }

(** Compatibility layer *)
let init () =
  Synterp.init ();
  Interp.init ();
  Summary.Synterp.init_summaries ();
  Summary.Interp.init_summaries ()
