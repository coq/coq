(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

let make_oname Nametab.{ obj_dir; obj_mp; section_depth } id =
  Names.(Libnames.make_path obj_dir id, KerName.make obj_mp (Label.of_id id))

type 'summary node =
  | CompilingLibrary of Nametab.object_prefix
  | OpenedModule of is_type * export * Nametab.object_prefix * 'summary
  | OpenedSection of Nametab.object_prefix * 'summary * (bool * Nametab.object_prefix * Libobject.t) list

let node_prefix = function
  | CompilingLibrary prefix
  | OpenedModule (_,_,prefix,_)
  | OpenedSection (prefix,_,_) -> prefix

let prefix_id prefix = snd (Libnames.split_dirpath prefix.Nametab.obj_dir)

type 'summary library_segment = ('summary node * Libobject.t list) list

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
      let open Libobject in
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
    | OpenedSection (prefix,_,_) ->
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
  section_depth = 0;
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

let contents () = !interp_state

let start_compilation s mp =
  if !synterp_state.comp_name != None then
    CErrors.user_err Pp.(str "compilation unit is already started");
  assert (List.is_empty !synterp_state.lib_stk);
  assert (List.is_empty !interp_state);
  if Global.sections_are_opened () then (* XXX not sure if we need this check *)
    CErrors.user_err Pp.(str "some sections are already opened");
  let prefix = Nametab.{ obj_dir = s; obj_mp = mp; section_depth = 0 } in
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

let sections () = Safe_typing.sections_of_safe_env @@ Global.safe_env ()

let sections_depth () =
  if !Flags.in_synterp_phase then
    !synterp_state.lib_stk |> List.count (function
        | (OpenedSection _, _) -> true
        | ((OpenedModule _ | CompilingLibrary _), _) -> false)
  else
    Section.depth (sections ())

let sections_are_opened () = sections_depth () > 0

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
    | CompilingLibrary prefix
    | OpenedModule (_, _, prefix, _)
    | OpenedSection (prefix, _, _) -> prefix
  in
  synterp_state := { !synterp_state with path_prefix }

let pop_modpath = function
  | MPdot (mp, _) -> mp
  | _ -> assert false

let pop_path_prefix () =
  let op = !synterp_state.path_prefix in
  synterp_state := {
    !synterp_state
    with path_prefix = Nametab.{
        obj_dir = Libnames.pop_dirpath op.obj_dir;
        obj_mp = pop_modpath op.obj_mp;
        section_depth = op.section_depth - 1;
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

let discharge_mind mind =
  if is_in_section (IndRef (mind,0)) then MutInd.pop mind else mind

let discharge_inductive ind =
  if is_in_section (IndRef ind) then Ind.pop ind else ind

let discharge_constant cst =
  if is_in_section (ConstRef cst) then Constant.pop cst else cst

let discharge_global_reference ref =
  if is_in_section ref then
    if Globnames.isVarRef ref then None
    else Some (Globnames.pop_global_reference ref)
  else Some ref

let discharge_global_reference_with_instance ref =
  if is_in_section ref then
    if Globnames.isVarRef ref then None
    else Some (Globnames.pop_global_reference ref, section_instance ref)
  else Some (ref, [||])

let cache_item (discharged,prefix,item) =
  Libobject.(match item with
  | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | KeepObject _
  | ExportObject _ -> ()
  | AtomicObject obj -> cache_object (discharged,prefix,obj))

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

let discharge_proj_repr p =
  let ind = Projection.Repr.inductive p in
  let sec = section_segment_of_reference (GlobRef.IndRef ind) in
  Cooking.discharge_proj_repr sec p

let set_top_leaf = function
  | [] -> []
  | (_, prefix, leaf) :: rest -> (false, prefix, leaf) :: rest

let rec add_leaf_entry leaf = function
  | [] ->
    (* top_printers does set_bool_option_value which adds a leaf *)
    if !Flags.in_debugger then [], [dummylib, [leaf]] else assert false
  | ((CompilingLibrary prefix | OpenedModule (_, _, prefix, _)) as node, leaves) :: rest ->
    [true, prefix, leaf], (node, leaf :: leaves) :: rest
  | (OpenedSection (prefix, fs, discharged_leaves), sec_leaves) :: rest ->
    (* adding leaf in opened sections as well as here *)
    let open Libobject in
    match leaf with
    | AtomicObject obj ->
      let obj_leaves, rest =
        match Libobject.discharge_object obj with
        | Some obj ->
          Global.in_lower_section (fun () ->
              let newleaf = Libobject.AtomicObject (Libobject.rebuild_object obj) in
              add_leaf_entry newleaf rest) ()
        | None ->
          [], rest in
      let node = OpenedSection (prefix, fs, set_top_leaf obj_leaves @ discharged_leaves) in
      let obj_leaves = (true, prefix, leaf) :: obj_leaves in
      obj_leaves, (node, List.map pi3 obj_leaves @ sec_leaves) :: rest
    | _ ->
      let obj_leaves, rest =
        Global.in_lower_section (fun () -> add_leaf_entry leaf rest) () in
      let node = OpenedSection (prefix, fs, set_top_leaf obj_leaves @ discharged_leaves) in
      obj_leaves, (node, List.map pi3 obj_leaves @ sec_leaves) :: rest

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
  val add_leaf_entry : Libobject.t -> (bool * Nametab.object_prefix * Libobject.t) list
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
    let leaves, lib_stk = add_leaf_entry leaf !synterp_state.lib_stk in
    synterp_state := { !synterp_state with lib_stk };
    leaves

  (* Returns the opening node of a given name *)
  let start_mod ~is_type export id mp fs =
    let dir = Libnames.add_dirpath_suffix !synterp_state.path_prefix.Nametab.obj_dir id in
    let prefix = Nametab.{ obj_dir = dir; obj_mp = mp; section_depth = 0 } in
    check_mod_fresh ~is_type prefix id;
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
    let obj_mp = MPdot (opp.Nametab.obj_mp, Label.of_id id) in
    let prefix = Nametab.{ obj_dir; obj_mp ; section_depth = opp.section_depth + 1 } in
    check_section_fresh obj_dir id;
    let fs = Summary.Synterp.freeze_summaries () in
    add_entry (OpenedSection (prefix, fs, []));
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
      | OpenedSection (op, _, _) ->
        OpenedSection(op,Summary.Synterp.empty_frozen, [] (* ?? *))
    in
    let lib_synterp_stk = List.map (fun (node,_) -> drop_node node, []) st.lib_stk in
    { st with lib_stk = lib_synterp_stk }

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
    let leaves, lib_stk = add_leaf_entry leaf !interp_state in
    interp_state := lib_stk;
    leaves

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
    Global.open_section id;
    let prefix = !synterp_state.path_prefix in
    let fs = Summary.Interp.freeze_summaries () in
    add_entry (OpenedSection (prefix, fs, []))

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
      | OpenedSection (op, _, _) ->
        OpenedSection(op,Summary.Interp.empty_frozen, [] (* ? *))
    in
    List.map (fun (node,_) -> drop_node node, []) interp_state

end

let add_leaf obj =
  let leaves = match Libobject.object_stage obj with
  | Summary.Stage.Synterp ->
    SynterpActions.add_leaf_entry (AtomicObject obj)
  | Summary.Stage.Interp ->
    InterpActions.add_leaf_entry (AtomicObject obj) in
  let leaves = set_top_leaf leaves in
  List.iter cache_item (List.rev leaves)

module type StagedLibS = sig

  type summary

  type classified_objects = {
    substobjs : Libobject.t list;
    keepobjs : Libobject.t list;
    anticipateobjs : Libobject.t list;
  }
  val classify_segment : Libobject.t list -> classified_objects

  val find_opening_node : Id.t -> summary node

  val add_entry : summary node -> unit
  val add_leaf_entry : Libobject.t -> unit

  (** {6 Sections } *)
  val open_section : Id.t -> unit
  val close_section : unit -> unit

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

end

(** The [StagedLib] abstraction factors out the code dealing with Lib structure
    that is common to all stages. *)
module StagedLib(Actions : LibActions) : StagedLibS with type summary = Actions.summary = struct

type summary = Actions.summary

type classified_objects = {
  substobjs : Libobject.t list;
  keepobjs : Libobject.t list;
  anticipateobjs : Libobject.t list;
}

let classify_segment seg =
  let substobjs, keepobjs, anticipateobjs = classify_segment seg in
  { substobjs; keepobjs; anticipateobjs; }

let add_entry node = Actions.add_entry node
let add_leaf_entry obj = ignore (Actions.add_leaf_entry obj)

let open_section id = Actions.open_section id

let find_opening_node id =
  let entry = match Actions.get_lib_stk () with
    | [] -> assert false
    | (CompilingLibrary _, _) :: _ ->
        CErrors.user_err Pp.(str "There is nothing to end.")
    | (entry, _) :: _ -> entry
  in
  let id' = prefix_id (node_prefix entry) in
  if not (Names.Id.equal id id') then
    CErrors.user_err Pp.(str "Last block to end has name "
      ++ Id.print id' ++ str ".");
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
    | OpenedSection (prefix, _, _) -> error_still_opened "section" prefix
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
  let fs,newdecls = match mark with
    | OpenedSection (_,fs,discharged_decls) -> fs, discharged_decls
    | _ -> CErrors.user_err Pp.(str "No opened section.")
  in
  Actions.set_lib_stk before;
  Actions.pop_path_prefix ();
  Actions.close_section fs;
  List.iter cache_item (List.rev newdecls)

type frozen = Actions.frozen

let freeze () = Actions.freeze ()

let unfreeze st = Actions.unfreeze st

let init () = Actions.init ()

let drop_objects st = Actions.drop_objects st

end

module Synterp : StagedLibS with type summary = Summary.Synterp.frozen = StagedLib(SynterpActions)
module Interp : StagedLibS with type summary = Summary.Interp.frozen = StagedLib(InterpActions)

let end_compilation dir =
  end_compilation_checks dir;
  let (syntax_after,_,syntax_before) = split_lib_at_opening !synterp_state.lib_stk in
  let (after,_,before) = split_lib_at_opening !interp_state in
  assert (List.is_empty syntax_before);
  assert (List.is_empty before);
  synterp_state := { !synterp_state with comp_name = None };
  let syntax_after = Synterp.classify_segment syntax_after in
  let after = Interp.classify_segment after in
  !synterp_state.path_prefix, after, syntax_after

(** Compatibility layer *)
let init () =
  Synterp.init ();
  Interp.init ();
  Summary.Synterp.init_summaries ();
  Summary.Interp.init_summaries ()

let open_section id =
  Synterp.open_section id;
  Interp.open_section id

let close_section () =
  Synterp.close_section ();
  Interp.close_section ()
