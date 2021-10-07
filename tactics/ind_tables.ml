(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open CErrors
open Util
open Pp

(**********************************************************************)
(* Registering schemes in the environment *)

type handle = Evd.side_effects

type mutual_scheme_object_function =
  Environ.env -> handle -> MutInd.t -> constr array Evd.in_evar_universe_context
type individual_scheme_object_function =
  Environ.env -> handle -> inductive -> constr Evd.in_evar_universe_context

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

let declare_scheme_object s aux f =
  let () =
    if not (Id.is_valid ("ind" ^ s)) then
      user_err Pp.(str ("Illegal induction scheme suffix: " ^ s))
  in
  let key = if String.is_empty aux then s else aux in
  try
    let _ = Hashtbl.find scheme_object_table key in
(*    let aux_msg = if aux="" then "" else " (with key "^aux^")" in*)
    user_err
      (str "Scheme object " ++ str key ++ str " already declared.")
  with Not_found ->
    Hashtbl.add scheme_object_table key (s,f);
    key

let declare_mutual_scheme_object s ?deps ?(aux="") f =
  declare_scheme_object s aux (MutualSchemeFunction (f, deps))

let declare_individual_scheme_object s ?deps ?(aux="") f =
  declare_scheme_object s aux (IndividualSchemeFunction (f, deps))

(**********************************************************************)
(* Defining/retrieving schemes *)

let is_visible_name id =
  try ignore (Nametab.locate (Libnames.qualid_of_ident id)); true
  with Not_found -> false

let compute_name internal id =
  if internal then
    Namegen.next_ident_away_from (add_prefix "internal_" id) is_visible_name
  else id

let declare_definition_scheme = ref (fun ~internal ~univs ~role ~name c ->
    CErrors.anomaly (Pp.str "scheme declaration not registered"))

let lookup_scheme kind ind =
  try Some (DeclareScheme.lookup_scheme kind ind) with Not_found -> None

let redeclare_schemes eff =
  let fold c role accu = match role with
  | Evd.Schema (ind, kind) ->
    try
      let _ = DeclareScheme.lookup_scheme kind ind in
      accu
    with Not_found ->
      let old = try String.Map.find kind accu with Not_found -> [] in
      String.Map.add kind ((ind, c) :: old) accu
  in
  let schemes = Cmap.fold fold eff.Evd.seff_roles String.Map.empty in
  let iter kind defs =
    let defs = Array.of_list defs in
    DeclareScheme.declare_scheme kind defs
  in
  String.Map.iter iter schemes

let local_lookup_scheme eff kind ind = match lookup_scheme kind ind with
| Some _ as ans -> ans
| None ->
  let exception Found of Constant.t in
  let iter c role = match role with
  | Evd.Schema (i, k) ->
    if String.equal k kind && Ind.CanOrd.equal i ind then raise (Found c)
  in
  (* Inefficient O(n), but the number of locally declared schemes is small and
     this is very rarely called *)
  try let _ = Cmap.iter iter eff.Evd.seff_roles in None with Found c -> Some c

let local_check_scheme kind ind eff =
  Option.has_some (local_lookup_scheme eff kind ind)

let define internal role id c poly univs =
  let id = compute_name internal id in
  let uctx = UState.minimize univs in
  let c = UState.nf_universes uctx c in
  let univs = UState.univ_entry ~poly uctx in
  !declare_definition_scheme ~internal ~univs ~role ~name:id c

(* Assumes that dependencies are already defined *)
let rec define_individual_scheme_base kind suff f ~internal idopt (mind,i as ind) eff =
  (* FIXME: do not rely on the imperative modification of the global environment *)
  let (c, ctx) = f (Global.env ()) eff ind in
  let mib = Global.lookup_mind mind in
  let id = match idopt with
    | Some id -> id
    | None -> add_suffix mib.mind_packets.(i).mind_typename suff in
  let role = Evd.Schema (ind, kind) in
  let const, neff = define internal role id c (Declareops.inductive_is_polymorphic mib) ctx in
  let eff = Evd.concat_side_effects neff eff in
  const, eff

and define_individual_scheme kind ~internal names (mind,i as ind) =
  match Hashtbl.find scheme_object_table kind with
  | _,MutualSchemeFunction _ -> assert false
  | s,IndividualSchemeFunction (f, deps) ->
    let deps = match deps with None -> [] | Some deps -> deps (Global.env ()) ind in
    let eff = List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) Evd.empty_side_effects deps in
    define_individual_scheme_base kind s f ~internal names ind eff

(* Assumes that dependencies are already defined *)
and define_mutual_scheme_base kind suff f ~internal names mind eff =
  (* FIXME: do not rely on the imperative modification of the global environment *)
  let (cl, ctx) = f (Global.env ()) eff mind in
  let mib = Global.lookup_mind mind in
  let ids = Array.init (Array.length mib.mind_packets) (fun i ->
      try Int.List.assoc i names
      with Not_found -> add_suffix mib.mind_packets.(i).mind_typename suff) in
  let fold i effs id cl =
    let role = Evd.Schema ((mind, i), kind)in
    let cst, neff = define internal role id cl (Declareops.inductive_is_polymorphic mib) ctx in
    (Evd.concat_side_effects neff effs, cst)
  in
  let (eff, consts) = Array.fold_left2_map_i fold eff ids cl in
  consts, eff

and define_mutual_scheme kind ~internal names mind =
  match Hashtbl.find scheme_object_table kind with
  | _,IndividualSchemeFunction _ -> assert false
  | s,MutualSchemeFunction (f, deps) ->
    let deps = match deps with None -> [] | Some deps -> deps (Global.env ()) mind in
    let eff = List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) Evd.empty_side_effects deps in
    define_mutual_scheme_base kind s f ~internal names mind eff

and declare_scheme_dependence eff = function
| SchemeIndividualDep (ind, kind) ->
  if local_check_scheme kind ind eff then eff
  else
    let _, eff' = define_individual_scheme kind ~internal:true None ind in
    Evd.concat_side_effects eff' eff
| SchemeMutualDep (mind, kind) ->
  if local_check_scheme kind (mind, 0) eff then eff
  else
    let _, eff' = define_mutual_scheme kind ~internal:true [] mind in
    Evd.concat_side_effects eff' eff

let find_scheme kind (mind,i as ind) =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  match local_lookup_scheme (Evd.eval_side_effects sigma) kind ind with
  | Some s ->
    Proofview.tclUNIT s
  | None ->
  match Hashtbl.find scheme_object_table kind with
  | s,IndividualSchemeFunction (f, deps) ->
    let deps = match deps with None -> [] | Some deps -> deps (Global.env ()) ind in
    let eff = List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) Evd.empty_side_effects deps in
    let c, eff = define_individual_scheme_base kind s f ~internal:true None ind eff in
    Proofview.tclEFFECTS eff <*> Proofview.tclUNIT c
  | s,MutualSchemeFunction (f, deps) ->
    let deps = match deps with None -> [] | Some deps -> deps (Global.env ()) mind in
    let eff = List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) Evd.empty_side_effects deps in
    let ca, eff = define_mutual_scheme_base kind s f ~internal:true [] mind eff in
    Proofview.tclEFFECTS eff <*> Proofview.tclUNIT ca.(i)

let define_individual_scheme kind names ind =
  let _ , eff = define_individual_scheme kind ~internal:false names ind in
  redeclare_schemes eff

let define_mutual_scheme kind names mind =
  let _, eff = define_mutual_scheme kind ~internal:false names mind in
  redeclare_schemes eff
