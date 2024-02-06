(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
  | QualifiedUniv of Id.t (* global universe introduced by some global value *)
  | UnqualifiedUniv (* other global universe *)

type universe_name_decl = {
  udecl_src : universe_source;
  udecl_named : (Id.t * UGlobal.t) list;
  udecl_anon : UGlobal.t list;
}

type [@warning "-37"] sort_source =
  | BoundQuality 
  | UnqualifiedQuality

type sort_name_decl = {
  sdecl_src : sort_source; (* global sort introduced by some global value *)
  sdecl_named : (Id.t * Sorts.QGlobal.t) list;
}

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
    Nametab.map_visibility succ i, Libnames.make_path (DirPath.make (l::dp)) id

let do_univ_name ~check i dp src (id,univ) =
  let i, sp = qualify_univ i dp src id in
  if check then check_exists_universe sp;
  Nametab.push_universe i sp univ

let get_names decl =
  let fold accu (id, _) = Id.Set.add id accu in
  let names = List.fold_left fold Id.Set.empty decl.udecl_named in
  (* create fresh names for anonymous universes *)
  let fold u ((names, cnt), accu) =
    let rec aux i =
      let na = Id.of_string ("u"^(string_of_int i)) in
      if Id.Set.mem na names then aux (i+1) else (na, i)
    in
    let (id, cnt) = aux cnt in
    ((Id.Set.add id names, cnt + 1), ((id, u) :: accu))
  in
  let _, univs = List.fold_right fold decl.udecl_anon ((names, 0), decl.udecl_named) in
  univs

let cache_univ_names (prefix, decl) =
  let depth = Lib.sections_depth () in
  let dp = Libnames.pop_dirpath_n depth prefix.Nametab.obj_dir in
  let names = get_names decl in
  List.iter (do_univ_name ~check:true (Nametab.Until 1) dp decl.udecl_src) names

let load_univ_names i (prefix, decl) =
  let names = get_names decl in
  List.iter (do_univ_name ~check:false (Nametab.Until i) prefix.Nametab.obj_dir decl.udecl_src) names

let open_univ_names i (prefix, decl) =
  let names = get_names decl in
  List.iter (do_univ_name ~check:false (Nametab.Exactly i) prefix.Nametab.obj_dir decl.udecl_src) names

let discharge_univ_names decl = match decl.udecl_src with
  | BoundUniv -> None
  | (QualifiedUniv _ | UnqualifiedUniv) -> Some decl

let input_univ_names : universe_name_decl -> Libobject.obj =
  let open Libobject in
  declare_named_object_gen
    { (default_object "Global universe name state") with
      cache_function = cache_univ_names;
      load_function = load_univ_names;
      open_function = simple_open open_univ_names;
      discharge_function = discharge_univ_names;
      subst_function = (fun (subst, a) -> (* Actually the name is generated once and for all. *) a);
      classify_function = (fun a -> Substitute) }

let input_univ_names (src, l, a) =
  if CList.is_empty l && CList.is_empty a then ()
  else Lib.add_leaf (input_univ_names { udecl_src = src; udecl_named = l; udecl_anon = a })

let check_exists_sort sp =
  if Nametab.exists_sort sp then
    raise (AlreadyDeclared (Some "Sort", Libnames.basename sp))
  else ()

let qualify_sort i dp _src id =
    i,  Libnames.make_path dp id

let do_sort_name ~check i dp src (id,quality) =
  let i, sp = qualify_sort i dp src id in
  if check then check_exists_sort sp;
  Nametab.push_sort i sp quality 

let cache_sort_names (prefix, decl) =
  let depth = Lib.sections_depth () in
  let dp = Libnames.pop_dirpath_n depth prefix.Nametab.obj_dir in
  List.iter (do_sort_name ~check:true (Nametab.Until 1) dp decl.sdecl_src) decl.sdecl_named

let load_sort_names i (prefix, decl) =
  List.iter (do_sort_name ~check:false (Nametab.Until i) prefix.Nametab.obj_dir decl.sdecl_src) decl.sdecl_named

let open_sort_names i (prefix, decl) =
  List.iter (do_sort_name ~check:false (Nametab.Exactly i) prefix.Nametab.obj_dir decl.sdecl_src) decl.sdecl_named

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
      open_function = simple_open open_sort_names;
      discharge_function = discharge_sort_names;
      subst_function = (fun (subst, a) -> (* Actually the name is generated once and for all. *) a);
      classify_function = (fun a -> Substitute) }

let input_sort_names (src, l) =
  if CList.is_empty l then ()
  else Lib.add_leaf (input_sort_names { sdecl_src = src; sdecl_named = l; (* sdecl_anon = a *) })


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
    (* then keep the anonymous ones *)
    let fold u accu = Option.get (Level.name u) :: accu in
    let anonymous = Level.Set.fold fold (Level.Set.diff levels named) [] in
    input_univ_names (QualifiedUniv l, univs, anonymous)

let do_universe ~poly l =
  let in_section = Lib.sections_are_opened () in
  let () =
    if poly && not in_section then
      CErrors.user_err
        (Pp.str"Cannot declare polymorphic universes outside sections.")
  in
  let l = List.map (fun {CAst.v=id} -> (id, UnivGen.new_univ_global ())) l in
  let src = if poly then BoundUniv else UnqualifiedUniv in
  let () = input_univ_names (src, l, []) in
  match poly with
  | false ->
    let ctx = List.fold_left (fun ctx (_,qid) -> Level.Set.add (Level.make qid) ctx)
        Level.Set.empty l, Constraints.empty
    in
    Global.push_context_set ~strict:true ctx
  | true ->
    let names = CArray.map_of_list (fun (na,_) -> Name na) l in
    let us = CArray.map_of_list (fun (_,l) -> Level.make l) l in
    let ctx =
      UVars.UContext.make ([||],names) (UVars.Instance.of_array ([||],us), Constraints.empty)
    in
    Global.push_section_context ctx

    (* TODO: move to its proper place *)
let do_sort l =
  let () =
    if Lib.is_modtype () 
    then CErrors.user_err (Pp.str "Cannot declare global sort qualities in a module type.") 
  in
  (* let in_section = Lib.sections_are_opened () in *)
  let l = List.map (fun {CAst.v=id} -> (id, UnivGen.new_sort_global id)) l in
  let src = UnqualifiedQuality in
     (* if in_section then BoundQuality else UnqualifiedQuality in *)
  let () = input_sort_names (src, l) in
  let qs = List.fold_left  (fun qs (_, qv) -> Sorts.QVar.(Set.add (make_global qv) qs))
    Sorts.QVar.Set.empty l
  in
  Global.push_quality_set qs

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
    Global.push_context_set ~strict:true uctx
  | true ->
    let uctx = UVars.UContext.make
        ([||],[||])
        (UVars.Instance.empty,constraints)
    in
    Global.push_section_context uctx
