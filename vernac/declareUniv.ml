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
open Declarations
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

type universe_name_decl = universe_source * (Id.t * Univ.Level.UGlobal.t) list

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

let cache_univ_names ((sp, _), (src, univs)) =
  let depth = Lib.sections_depth () in
  let dp = Libnames.pop_dirpath_n depth (Libnames.dirpath sp) in
  List.iter (do_univ_name ~check:true (Nametab.Until 1) dp src) univs

let load_univ_names i ((sp, _), (src, univs)) =
  List.iter (do_univ_name ~check:false (Nametab.Until i) (Libnames.dirpath sp) src) univs

let open_univ_names i ((sp, _), (src, univs)) =
  List.iter (do_univ_name ~check:false (Nametab.Exactly i) (Libnames.dirpath sp) src) univs

let discharge_univ_names = function
  | _, (BoundUniv, _) -> None
  | _, ((QualifiedUniv _ | UnqualifiedUniv), _ as x) -> Some x

let input_univ_names : universe_name_decl -> Libobject.obj =
  let open Libobject in
  declare_object
    { (default_object "Global universe name state") with
      cache_function = cache_univ_names;
      load_function = load_univ_names;
      open_function = simple_open open_univ_names;
      discharge_function = discharge_univ_names;
      subst_function = (fun (subst, a) -> (* Actually the name is generated once and for all. *) a);
      classify_function = (fun a -> Substitute a) }

let invent_name (named,cnt) u =
  let rec aux i =
    let na = Id.of_string ("u"^(string_of_int i)) in
    if Id.Map.mem na named then aux (i+1)
    else na, (Id.Map.add na u named, i+1)
  in
  aux cnt

let label_and_univs_of = let open GlobRef in function
    | ConstRef c ->
      let l = Label.to_id @@ Constant.label c in
      let univs = (Global.lookup_constant c).const_universes in
      l, univs
    | IndRef (c,_) ->
      let l = Label.to_id @@ MutInd.label c in
      let univs = (Global.lookup_mind c).mind_universes in
      l, univs
    | VarRef id ->
      CErrors.anomaly ~label:"declare_univ_binders"
        Pp.(str "declare_univ_binders on variable " ++ Id.print id ++ str".")
    | ConstructRef _ ->
      CErrors.anomaly ~label:"declare_univ_binders"
        Pp.(str "declare_univ_binders on a constructor reference")

let declare_univ_binders gr pl =
  let l, univs = label_and_univs_of gr in
  match univs with
  | Polymorphic _ -> ()
  | Monomorphic (levels,_) ->
    (* First the explicitly named universes *)
    let named, univs = Id.Map.fold (fun id univ (named,univs) ->
        let univs = match Univ.Level.name univ with
          | None -> assert false (* having Prop/Set/Var as binders is nonsense *)
          | Some univ -> (id,univ)::univs
        in
        let named = LSet.add univ named in
        named, univs)
        pl (LSet.empty,[])
    in
    (* then invent names for the rest *)
    let _, univs = LSet.fold (fun univ (aux,univs) ->
        let id, aux = invent_name aux univ in
        let univ = Option.get (Level.name univ) in
        aux, (id,univ) :: univs)
        (LSet.diff levels named) ((pl,0),univs)
    in
    if univs != [] then
      Lib.add_anonymous_leaf (input_univ_names (QualifiedUniv l, univs))

let do_universe ~poly l =
  let in_section = Global.sections_are_opened () in
  let () =
    if poly && not in_section then
      CErrors.user_err ~hdr:"Constraint"
        (Pp.str"Cannot declare polymorphic universes outside sections")
  in
  let l = List.map (fun {CAst.v=id} -> (id, UnivGen.new_univ_global ())) l in
  let ctx = List.fold_left (fun ctx (_,qid) -> Univ.LSet.add (Univ.Level.make qid) ctx)
      Univ.LSet.empty l, Univ.Constraint.empty
  in
  let src = if poly then BoundUniv else UnqualifiedUniv in
  let () = Lib.add_anonymous_leaf (input_univ_names (src, l)) in
  DeclareUctx.declare_universe_context ~poly ctx

let do_constraint ~poly l =
  let open Univ in
  let evd = Evd.from_env (Global.env ()) in
  let u_of_id x = Constrintern.interp_known_level evd x in
  let constraints = List.fold_left (fun acc (l, d, r) ->
      let lu = u_of_id l and ru = u_of_id r in
      Constraint.add (lu, d, ru) acc)
      Constraint.empty l
  in
  let uctx = ContextSet.add_constraints constraints ContextSet.empty in
  DeclareUctx.declare_universe_context ~poly uctx
