(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ

(* object_kind , id *)
exception AlreadyDeclared of (string option * Id.t)

let () = CErrors.register_handler (function
    | AlreadyDeclared (kind, id) ->
      Some
        Pp.(seq [ Pp.pr_opt_no_spc (fun s -> str s ++ spc ()) kind
                ; Id.print id; str " already exists."])
    | _ ->
      None)

type universe_source =
  | BoundUniv (* polymorphic universe, bound in a function (this will go away someday) *)
  | QualifiedUniv of DirPath.t (* global universe introduced by some global value *)
  | UnqualifiedUniv (* other global universe, todo merge with [QualifiedUniv []] *)

type universe_name_decl = universe_source * (Id.t * UGlobal.t) list

type sort_source =
  | BoundQuality
  | UnqualifiedQuality

type sort_name_decl = {
  sdecl_src : sort_source; (* global sort introduced by some global value *)
  sdecl_named : (Id.t * Sorts.Quality.t) list;
}

let check_exists_universe sp =
  if Nametab.exists_universe sp then
    raise (AlreadyDeclared (Some "Universe", Libnames.basename sp))
  else ()

let qualify_univ i dp src id =
  match src with
  | BoundUniv | UnqualifiedUniv ->
    i,  Libnames.add_path_suffix dp id
  | QualifiedUniv l ->
    let path = Libnames.append_path dp l in
    Nametab.map_visibility (fun n -> n + List.length (DirPath.repr l)) i, Libnames.add_path_suffix path id

let do_univ_name ~check i dp src (id,univ) =
  let i, sp = qualify_univ i dp src id in
  if check then check_exists_universe sp;
  Nametab.push_universe i sp univ

let cache_univ_names (prefix, (src, univs)) =
  let depth = Lib.sections_depth () in
  let dp = Libnames.path_pop_n_suffixes depth prefix.Libobject.obj_path in
  List.iter (do_univ_name ~check:true (Nametab.Until 1) dp src) univs

let load_univ_names i (prefix, (src, univs)) =
  List.iter (do_univ_name ~check:false (Nametab.Until i) prefix.Libobject.obj_path src) univs

let open_univ_names i (prefix, (src, univs)) =
  List.iter (do_univ_name ~check:false (Nametab.Exactly i) prefix.Libobject.obj_path src) univs

let discharge_univ_names = function
  | BoundUniv, _ -> None
  | (QualifiedUniv _ | UnqualifiedUniv), _ as x -> Some x

let input_univ_names : universe_name_decl -> Libobject.obj =
  let open Libobject in
  declare_named_object_gen
    { (default_object "Global universe name state") with
      cache_function = cache_univ_names;
      load_function = load_univ_names;
      open_function = filtered_open open_univ_names;
      discharge_function = discharge_univ_names;
      classify_function = (fun _ -> Escape) }

let input_univ_names (src, l) =
  if CList.is_empty l then ()
  else Lib.add_leaf (input_univ_names (src, l))

let invent_name prefix (named,cnt) u =
  let rec aux i =
    let na = Id.of_string ("u"^(string_of_int i)) in
    let sp = Libnames.add_path_suffix prefix na in
    if Id.Map.mem na named || Nametab.exists_universe sp then aux (i+1)
    else na, (Id.Map.add na u named, i+1)
  in
  aux cnt

let check_exists_sort sp =
  if Nametab.Quality.exists sp then
    raise (AlreadyDeclared (Some "Sort", Libnames.basename sp))
  else ()

let qualify_sort i dp id =
  i, Libnames.add_path_suffix dp id

let do_sort_name ~check i dp (id,quality) =
  let i, sp = qualify_sort i dp id in
  if check then check_exists_sort sp;
  Nametab.Quality.push i sp quality

let cache_sort_names (prefix, decl) =
  let depth = Lib.sections_depth () in
  let dp = Libnames.path_pop_n_suffixes depth prefix.Libobject.obj_path in
  List.iter (do_sort_name ~check:true (Nametab.Until 1) dp) decl.sdecl_named

let load_sort_names i (prefix, decl) =
  List.iter (do_sort_name ~check:false (Nametab.Until i) prefix.Libobject.obj_path) decl.sdecl_named

let open_sort_names i (prefix, decl) =
  List.iter (do_sort_name ~check:false (Nametab.Exactly i) prefix.Libobject.obj_path) decl.sdecl_named

let discharge_sort_names decl =
  match decl.sdecl_src with
  | BoundQuality -> None
  | UnqualifiedQuality -> Some decl

let input_sort_names : sort_name_decl -> Libobject.obj =
  let open Libobject in
  declare_named_object_gen
    { (default_object "Global sort name state") with
      cache_function = cache_sort_names;
      load_function = load_sort_names;
      open_function = filtered_open open_sort_names;
      discharge_function = discharge_sort_names;
      classify_function = (fun a -> Escape) }

let input_sort_names (src, l) =
  if CList.is_empty l then ()
  else Lib.add_leaf (input_sort_names { sdecl_src = src; sdecl_named = l })


let label_of = let open GlobRef in function
| ConstRef c -> Constant.label c
| IndRef (c,_) -> MutInd.label c
| VarRef id -> id
| ConstructRef _ ->
  CErrors.anomaly ~label:"declare_univ_binders"
    Pp.(str "declare_univ_binders on a constructor reference")

let declare_univ_binders gr UState.{ universes_entry_universes = univs; universes_entry_binders = pl } =
  let l = label_of gr in
  match univs with
  | UState.Polymorphic_entry _ -> ()
  | UState.Monomorphic_entry (levels, _) ->
    let qs, pl = pl in
    assert (Id.Map.is_empty qs);
    (* First the explicitly named universes *)
    let named, univs = Id.Map.fold (fun id univ (named,univs) ->
        let univs = match Level.name univ with
          | None -> assert false (* having Prop/Set/Var as binders is nonsense *)
          | Some univ -> (id,univ)::univs
        in
        let named = Level.Set.add univ named in
        named, univs)
        pl (Level.Set.empty,[])
    in
    (* then invent names for the rest *)
    let prefix = Libnames.add_path_suffix (Lib.cwd_except_section()) l in
    let _, univs = Level.Set.fold (fun univ (aux,univs) ->
        let id, aux = invent_name prefix aux univ in
        let univ = Option.get (Level.name univ) in
        aux, (id,univ) :: univs)
        (Level.Set.diff levels named) ((pl,0),univs)
    in
    input_univ_names (QualifiedUniv (DirPath.make [l]), univs)

let name_mono_section_univs univs =
  if Level.Set.is_empty univs then ()
  else
  let prefix = Lib.cwd () in
  let sections = let open Libnames in
    drop_dirpath_prefix (dirpath_of_path @@ Lib.cwd_except_section())
      (dirpath_of_path prefix)
  in
  let _, univs = Level.Set.fold (fun univ (aux,univs) ->
      let id, aux = invent_name prefix aux univ in
      let univ = Option.get (Level.name univ) in
      aux, (id,univ) :: univs)
      univs ((Id.Map.empty, 0), [])
  in
  input_univ_names (QualifiedUniv sections, univs)

let do_universe ~poly l =
  let in_section = Lib.sections_are_opened () in
  let () =
    if poly && not in_section then
      CErrors.user_err
        (Pp.str"Cannot declare polymorphic universes outside sections.")
  in
  let l = List.map (fun {CAst.v=id} -> (id, UnivGen.new_univ_global ())) l in
  let src = if poly then BoundUniv else UnqualifiedUniv in
  let () = input_univ_names (src, l) in
  match poly with
  | false ->
    let ctx = List.fold_left (fun ctx (_,qid) -> Level.Set.add (Level.make qid) ctx)
        Level.Set.empty l, Univ.UnivConstraints.empty
    in
    Global.push_context_set ctx
  | true ->
    let names = CArray.map_of_list (fun (na,_) -> Name na) l in
    let us = CArray.map_of_list (fun (_,l) -> Level.make l) l in
    let ctx =
      UVars.UContext.make {quals = [||]; univs = names}
        (UVars.LevelInstance.of_array ([||],us), PConstraints.empty)
    in
    Global.push_section_context ctx

let do_sort_mono l =
  let l = List.map (fun {CAst.v=id} ->
      let q = Global.new_global_sort () in
      q, (id, Sorts.Quality.QGlobal q))
      l
  in
  let src = UnqualifiedQuality in
  input_sort_names (src, List.map snd l)

let do_sort_poly l =
  let in_section = Lib.sections_are_opened () in
  let () =
    if not in_section then
      CErrors.user_err
        (Pp.str"Cannot declare polymorphic sorts outside sections.")
  in
  let new_sort =
    let n = Section.section_qvar_count @@
      Option.get @@ Safe_typing.sections_of_safe_env @@
      Global.safe_env ()
    in
    let n = ref n in
    fun _id ->
      let x = !n in
      let () = incr n in
      let q = Sorts.QVar.make_secvar x in
      Sorts.Quality.QVar q
  in
  let l = List.map (fun {CAst.v=id} -> (id, new_sort id)) l in
  let src = BoundQuality in
  let () = input_sort_names (src, l) in
  let names = CArray.map_of_list (fun (na,_) -> Name na) l in
  let qs = CArray.map_of_list snd l in
  let ctx =
    UVars.UContext.make {quals=names; univs=[||]}
      (UVars.LevelInstance.of_array (qs,[||]), PConstraints.empty)
  in
  Global.push_section_context ctx

let do_sort ~poly l =
  if poly then do_sort_poly l else do_sort_mono l

let redundant_elim_warning =
  CWarnings.create
    ~name:"redundant-elimination-constraint"
    (fun (q1, k, q2) ->
      Pp.(hov 1 (str "Redundant elimination constraint: "
        ++ UnivNames.pr_quality_with_global_universes q1 ++ spc()
        ++ Sorts.ElimConstraint.pr_kind k ++ spc()
        ++ UnivNames.pr_quality_with_global_universes q2)))

let do_constraint ~poly l =
  let evd = Evd.from_env (Global.env ()) in
  let constraints = List.fold_left (fun acc cst ->
      match cst with
      | Constrexpr.UnivCst (l,d,r as cst) ->
         let cst = Constrintern.interp_univ_constraint evd cst in
         PConstraints.add_univ cst acc
      | Constrexpr.ElimCst (l,d,r as cst) ->
         let cst = Constrintern.interp_elim_constraint evd cst in
         PConstraints.add_quality cst acc)
      PConstraints.empty l
  in
  let qcst, ucst = constraints in
  let graph = Global.elim_graph () in
  let qcst = Sorts.ElimConstraints.filter
    (fun q ->
      (* this does not check redundancy of multiple new constraints *)
      let b = QGraph.check_constraint graph q in
      let () = if b then redundant_elim_warning q else () in
      not b)
    qcst in
  match poly with
  | false ->
    let () = Global.merge_elim_constraints qcst in
    Global.push_context_set (Univ.Level.Set.empty, ucst)
  | true ->
    let uctx = UVars.UContext.make
        UVars.empty_bound_names
        (UVars.LevelInstance.empty, (qcst, ucst))
    in
    Global.push_section_context uctx

let constraint_sources = Summary.ref ~name:"univ constraint sources" []

let cache_constraint_source x =
  let open Summary.Ref in
  constraint_sources := x :: !constraint_sources

let constraint_sources () =
  let open Summary.Ref in
  !constraint_sources

let constraint_obj =
  Libobject.declare_object {
    (Libobject.default_object "univ constraint sources") with
    cache_function = cache_constraint_source;
    load_function = (fun _ c -> cache_constraint_source c);
    discharge_function = (fun x -> Some x);
    classify_function = (fun _ -> Escape);
  }

(* XXX this seems like it could be merged with declare_univ_binders
   main issue is the filtering or redundant constraints (needed for perf / smaller vo file sizes) *)
let add_constraint_source x ctx =
  let _, csts = ctx in
  if Univ.UnivConstraints.is_empty csts then ()
  else
    let v = x, csts in
    Lib.add_leaf (constraint_obj v)

(* TODO: MS generalize to elim constraints? *)
let check_constraint env sigma l =
  let constraints = List.fold_left (fun acc cst ->
      let cst = Constrintern.interp_univ_constraint sigma cst in
      PConstraints.add_univ cst acc)
      PConstraints.empty l
  in
  if Evd.check_poly_constraints sigma constraints then ()
  else CErrors.user_err (Pp.str"Constraints do not hold")
