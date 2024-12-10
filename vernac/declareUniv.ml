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

let _ = CErrors.register_handler (function
    | AlreadyDeclared (kind, id) ->
      Some
        Pp.(seq [ Pp.pr_opt_no_spc (fun s -> str s ++ spc ()) kind
                ; Id.print id; str " already exists."])
    | _ ->
      None)

type universe_source =
  | BoundUniv (* polymorphic universe, bound in a function (this will go away someday) *)
  | QualifiedUniv of Id.t list (* global universe introduced by some global value *)
  | UnqualifiedUniv (* other global universe, todo merge with [QualifiedUniv []] *)

type universe_name_decl = universe_source * (Id.t * UGlobal.t) list

let check_exists_universe sp =
  if Nametab.exists_universe sp then
    raise (AlreadyDeclared (Some "Universe", Libnames.basename sp))
  else ()

let qualify_univ i dp src id =
  match src with
  | BoundUniv | UnqualifiedUniv ->
    i,  Libnames.make_path dp id
  | QualifiedUniv l ->
    let dp = DirPath.repr dp in
    Nametab.map_visibility (fun n -> n + List.length l) i, Libnames.make_path (DirPath.make (List.append l dp)) id

let do_univ_name ~check i dp src (id,univ) =
  let i, sp = qualify_univ i dp src id in
  if check then check_exists_universe sp;
  Nametab.push_universe i sp univ

let cache_univ_names (prefix, (src, univs)) =
  let depth = Lib.sections_depth () in
  let dp = Libnames.pop_dirpath_n depth prefix.Nametab.obj_dir in
  List.iter (do_univ_name ~check:true (Nametab.Until 1) dp src) univs

let load_univ_names i (prefix, (src, univs)) =
  List.iter (do_univ_name ~check:false (Nametab.Until i) prefix.Nametab.obj_dir src) univs

let open_univ_names i (prefix, (src, univs)) =
  List.iter (do_univ_name ~check:false (Nametab.Exactly i) prefix.Nametab.obj_dir src) univs

let discharge_univ_names = function
  | BoundUniv, _ -> None
  | (QualifiedUniv _ | UnqualifiedUniv), _ as x -> Some x

let input_univ_names : universe_name_decl -> Libobject.obj =
  let open Libobject in
  declare_named_object_gen
    { (default_object "Global universe name state") with
      cache_function = cache_univ_names;
      load_function = load_univ_names;
      open_function = simple_open open_univ_names;
      discharge_function = discharge_univ_names;
      classify_function = (fun _ -> Escape) }

let input_univ_names (src, l) =
  if CList.is_empty l then ()
  else Lib.add_leaf (input_univ_names (src, l))

let invent_name prefix (named,cnt) u =
  let rec aux i =
    let na = Id.of_string ("u"^(string_of_int i)) in
    let sp = Libnames.make_path prefix na in
    if Id.Map.mem na named || Nametab.exists_universe sp then aux (i+1)
    else na, (Id.Map.add na u named, i+1)
  in
  aux cnt

let label_of = let open GlobRef in function
| ConstRef c -> Label.to_id @@ Constant.label c
| IndRef (c,_) -> Label.to_id @@ MutInd.label c
| VarRef id -> id
| ConstructRef _ ->
  CErrors.anomaly ~label:"declare_univ_binders"
    Pp.(str "declare_univ_binders on a constructor reference")

let declare_univ_binders gr (univs, pl) =
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
    let prefix = DirPath.make (l :: DirPath.repr (Lib.cwd_except_section())) in
    let _, univs = Level.Set.fold (fun univ (aux,univs) ->
        let id, aux = invent_name prefix aux univ in
        let univ = Option.get (Level.name univ) in
        aux, (id,univ) :: univs)
        (Level.Set.diff levels named) ((pl,0),univs)
    in
    input_univ_names (QualifiedUniv [l], univs)

let name_mono_section_univs univs =
  if Level.Set.is_empty univs then ()
  else
  let prefix = Lib.cwd () in
  let sections = DirPath.repr @@ Libnames.drop_dirpath_prefix (Lib.cwd_except_section()) prefix in
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
        Level.Set.empty l, Constraints.empty
    in
    Global.push_context_set ctx
  | true ->
    let names = CArray.map_of_list (fun (na,_) -> Name na) l in
    let us = CArray.map_of_list (fun (_,l) -> Level.make l) l in
    let ctx =
      UVars.UContext.make ([||],names) (UVars.Instance.of_array ([||],us), Constraints.empty)
    in
    Global.push_section_context ctx

let do_constraint ~poly l =
  let open Univ in
  let evd = Evd.from_env (Global.env ()) in
  let constraints = List.fold_left (fun acc cst ->
      let cst = Constrintern.interp_univ_constraint evd cst in
      Constraints.add cst acc)
      Constraints.empty l
  in
  match poly with
  | false ->
    let uctx = ContextSet.add_constraints constraints ContextSet.empty in
    Global.push_context_set uctx
  | true ->
    let uctx = UVars.UContext.make
        ([||],[||])
        (UVars.Instance.empty,constraints)
    in
    Global.push_section_context uctx

let constraint_sources = Summary.ref ~name:"univ constraint sources" []

let cache_constraint_source x = constraint_sources := x :: !constraint_sources

let constraint_sources () = !constraint_sources

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
  if Univ.Constraints.is_empty csts then ()
  else
    let v = x, csts in
    Lib.add_leaf (constraint_obj v)
