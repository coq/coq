(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File created by Vincent Siles, Oct 2007, extended into a generic
   support for generation of inductive schemes by Hugo Herbelin, Nov 2009 *)

(* This file provides support for registering inductive scheme builders,
   declaring schemes and generating schemes on demand *)

open Names
open Nameops
open Declarations
open Constr
open Util


(**********************************************************************)
(* Registering schemes in the environment *)

type side_effect_role =
| Schema of inductive * string

type schemes = {
  sch_eff : Evd.side_effects;
  sch_roles : side_effect_role Cmap_env.t;
  sch_reg : (Id.t * Constant.t * Loc.t option * UState.named_universes_entry) list;
}

type handle = schemes

let push_handle eff =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  let sigma = Evd.emit_side_effects eff.sch_eff sigma in
  Proofview.Unsafe.tclEVARS sigma

type mutual_scheme_object_function =
  Environ.env -> handle -> MutInd.t -> constr array Evd.in_ustate
type individual_scheme_object_function =
  Environ.env -> handle -> inductive -> constr Evd.in_ustate

type 'a scheme_kind = string

let pr_scheme_kind = Pp.str

(**********************************************************************)
(* The table of scheme building functions *)

type individual
type mutual

type scheme_dependency =
| SchemeMutualDep of MutInd.t * mutual scheme_kind
| SchemeIndividualDep of inductive * individual scheme_kind

type scheme_object_function =
  | MutualSchemeFunction of mutual_scheme_object_function * (Environ.env -> MutInd.t -> scheme_dependency list) option
  | IndividualSchemeFunction of individual_scheme_object_function * (Environ.env -> inductive -> scheme_dependency list) option

let scheme_object_table =
  (Hashtbl.create 17 : (string, string * scheme_object_function) Hashtbl.t)

let declare_scheme_object key ?(suff=key) f =
  let () =
    if not (Id.is_valid ("ind_" ^ suff)) then
      CErrors.user_err Pp.(str ("Illegal induction scheme suffix: " ^ suff))
  in
  if Hashtbl.mem scheme_object_table key then
    CErrors.user_err
      Pp.(str "Scheme object " ++ str key ++ str " already declared.")
  else begin
    Hashtbl.add scheme_object_table key (suff,f);
    key
  end

let declare_mutual_scheme_object key ?suff ?deps f =
  declare_scheme_object key ?suff (MutualSchemeFunction (f, deps))

let declare_individual_scheme_object key ?suff ?deps f =
  declare_scheme_object key ?suff (IndividualSchemeFunction (f, deps))

let is_declared_scheme_object key = Hashtbl.mem scheme_object_table key

let scheme_kind_name (key : _ scheme_kind) : string = key

(**********************************************************************)
(* Defining/retrieving schemes *)

let is_visible_name id =
  try ignore (Nametab.locate (Libnames.qualid_of_ident id)); true
  with Not_found ->
    (* FIXME: due to private constant declaration being imperative, we have to
       also check in the global env *)
    Global.exists_objlabel id

let compute_name internal id avoid =
  if internal then
    let visible id = is_visible_name id || Id.Set.mem id avoid in
    Namegen.next_ident_away_from (add_prefix "internal_" id) visible
  else id

let declare_definition_scheme = ref (fun ~univs ~name ~effs c ->
    CErrors.anomaly (Pp.str "scheme declaration not registered"))

let register_definition_scheme = ref (fun ~internal ~name ~const ~univs ?loc () ->
  CErrors.anomaly (Pp.str "scheme registering not registered"))

let lookup_scheme kind ind =
  try Some (DeclareScheme.lookup_scheme kind (GlobRef.IndRef ind)) with Not_found -> None

let empty_schemes eff = {
  sch_eff = eff;
  sch_reg = [];
  sch_roles = Cmap_env.empty;
}

let redeclare_schemes { sch_eff = eff; sch_roles = roles } =
  let fold c role accu = match role with
  | Schema (ind, kind) ->
    try
      let _ = DeclareScheme.lookup_scheme kind (GlobRef.IndRef ind) in
      accu
    with Not_found ->
      let old = try String.Map.find kind accu with Not_found -> [] in
      String.Map.add kind ((GlobRef.IndRef ind, GlobRef.ConstRef c) :: old) accu
  in
  let schemes = Cmap_env.fold fold roles String.Map.empty in
  let iter kind defs = List.iter (DeclareScheme.declare_scheme SuperGlobal kind) defs in
  String.Map.iter iter schemes

let local_lookup_scheme { sch_roles = roles } kind ind =
  match lookup_scheme kind ind with
| Some _ as ans -> ans
| None ->
  let exception Found of Constant.t in
  let iter c role = match role with
  | Schema (i, k) ->
    if String.equal k kind && Ind.UserOrd.equal i ind then raise (Found c)
  in
  (* Inefficient O(n), but the number of locally declared schemes is small and
     this is very rarely called *)
  try let _ = Cmap_env.iter iter roles in None with Found c -> Some (GlobRef.ConstRef c)

let local_check_scheme kind ind eff =
  Option.has_some (local_lookup_scheme eff kind ind)

let define ?loc internal role id c poly uctx sch =
  let avoid = Safe_typing.constants_of_private (Evd.seff_private sch.sch_eff) in
  let avoid = Id.Set.of_list @@ List.map (fun cst -> Constant.label cst) avoid in
  let id = compute_name internal id avoid in
  let uctx = UState.collapse_sort_variables ~only_above_prop:true uctx in
  let uctx = UState.normalize_variables uctx in
  let uctx = UState.minimize uctx in
  let c = UState.nf_universes uctx c in
  let uctx = UState.restrict uctx (Vars.universes_of_constr c) in
  let univs = UState.univ_entry ~poly uctx in
  let effs = sch.sch_eff in
  let cst, effs = !declare_definition_scheme ~univs ~name:id ~effs c in
  let reg = (id, cst, loc, univs) :: sch.sch_reg in
  let roles = Cmap_env.add cst role sch.sch_roles in
  cst, { sch_eff = effs; sch_reg = reg; sch_roles = roles  }

module Locmap : sig

    type t

    val default : Loc.t option -> t
    val make : ?default:Loc.t -> MutInd.t -> Loc.t option list -> t
    val lookup : locmap:t -> Names.inductive -> Loc.t option

end = struct

    type t = {
      default : Loc.t option;
      mind : MutInd.t option;
      ind_to_loc : Loc.t Int.Map.t;
    }

    let lookup ~locmap:{ ind_to_loc; default; mind } (m, i) =
      let () = match mind with
      | None -> ()
      | Some mind -> assert (MutInd.UserOrd.equal mind m)
      in
      Int.Map.find_opt i ind_to_loc |> fun loc ->
      Option.append loc default

    let default default = { default; ind_to_loc = Int.Map.empty; mind = None }

    let make ?default mind locs =
      let default, ind_to_loc =
        CList.fold_left_i (fun i (default,m) loc ->
          let m = match loc with
            | None -> m
            | Some loc -> Int.Map.add i loc m
          in
          let default = if Option.has_some default then default else loc in
          default, m)
          0 (default, Int.Map.empty) locs in
      { default; ind_to_loc; mind = Some mind }

  end

let get_env sch =
  Safe_typing.env_of_safe_env (Evd.get_senv_side_effects sch.sch_eff)

let globally_declare_schemes sch =
  Global.Internal.reset_safe_env (Evd.get_senv_side_effects sch.sch_eff)

(* Assumes that dependencies are already defined *)
let rec define_individual_scheme_base ?loc kind suff f ~internal idopt (mind,i as ind) eff =
  let env = get_env eff in
  let (c, ctx) = f env eff ind in
  let mib = Environ.lookup_mind mind env in
  let id = match idopt with
    | Some id -> id
    | None -> add_suffix mib.mind_packets.(i).mind_typename ("_"^suff) in
  let role = Schema (ind, kind) in
  let poly, cumulative = Declareops.inductive_is_polymorphic mib, Declareops.inductive_is_cumulative mib in
  let poly = PolyFlags.make ~univ_poly:poly ~cumulative ~collapse_sort_variables:true in
  let const, eff = define ?loc internal role id c poly ctx eff in
  const, eff

and define_individual_scheme ?loc kind ~internal names (mind,i as ind) eff =
  match Hashtbl.find scheme_object_table kind with
  | _,MutualSchemeFunction _ -> assert false
  | s,IndividualSchemeFunction (f, deps) ->
    let env = get_env eff in
    let deps = match deps with None -> [] | Some deps -> deps env ind in
    let eff = List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) eff deps in
    let _, eff = define_individual_scheme_base ?loc kind s f ~internal names ind eff in
    eff

(* Assumes that dependencies are already defined *)
and define_mutual_scheme_base ?(locmap=Locmap.default None) kind suff f ~internal names mind eff =
  let env = get_env eff in
  let (cl, ctx) = f env eff mind in
  let mib = Environ.lookup_mind mind env in
  let ids = Array.init (Array.length mib.mind_packets) (fun i ->
      try Int.List.assoc i names
      with Not_found -> add_suffix mib.mind_packets.(i).mind_typename ("_"^suff)) in
  let fold i effs id cl =
    let role = Schema ((mind, i), kind)in
    let loc = Locmap.lookup ~locmap (mind,i) in
    (* FIXME cumulativity not supported? *)
    let poly = PolyFlags.of_univ_poly (Declareops.inductive_is_polymorphic mib) in
    let cst, effs = define ?loc internal role id cl poly ctx effs in
    (effs, cst)
  in
  let (eff, consts) = Array.fold_left2_map_i fold eff ids cl in
  consts, eff

and define_mutual_scheme ?locmap kind ~internal names mind eff =
  match Hashtbl.find scheme_object_table kind with
  | _,IndividualSchemeFunction _ -> assert false
  | s,MutualSchemeFunction (f, deps) ->
    let env = get_env eff in
    let deps = match deps with None -> [] | Some deps -> deps env mind in
    let eff = List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) eff deps in
    let _, eff = define_mutual_scheme_base ?locmap kind s f ~internal names mind eff in
    eff

and declare_scheme_dependence eff sd =
match sd with
| SchemeIndividualDep (ind, kind) ->
  if local_check_scheme kind ind eff then eff
  else define_individual_scheme kind ~internal:true None ind eff
| SchemeMutualDep (mind, kind) ->
  if local_check_scheme kind (mind, 0) eff then eff
  else define_mutual_scheme kind ~internal:true [] mind eff

let register_schemes sch =
  let iter (id, kn, loc, univs) =
    !register_definition_scheme ~internal:false ~name:id ~const:kn ~univs ?loc ()
  in
  List.iter iter (List.rev sch.sch_reg)

let define_individual_scheme ?loc kind names ind =
  let sch = empty_schemes Evd.empty_side_effects in
  let eff = define_individual_scheme ?loc kind ~internal:false names ind sch in
  let () = globally_declare_schemes eff in
  let () = register_schemes eff in
  redeclare_schemes eff

let define_mutual_scheme ?locmap kind names mind =
  let sch = empty_schemes Evd.empty_side_effects in
  let eff = define_mutual_scheme ?locmap kind ~internal:false names mind sch in
  let () = globally_declare_schemes eff in
  let () = register_schemes eff in
  redeclare_schemes eff
