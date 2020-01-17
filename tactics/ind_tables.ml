(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

(** flag for internal message display *)
type internal_flag =
  | UserAutomaticRequest (* kernel action, a message is displayed *)
  | InternalTacticRequest  (* kernel action, no message is displayed *)
  | UserIndividualRequest   (* user action, a message is displayed *)

type mutual_scheme_object_function =
  internal_flag -> MutInd.t -> constr array Evd.in_evar_universe_context * Evd.side_effects
type individual_scheme_object_function =
  internal_flag -> inductive -> constr Evd.in_evar_universe_context * Evd.side_effects

type 'a scheme_kind = string

let pr_scheme_kind = Pp.str

(**********************************************************************)
(* The table of scheme building functions *)

type individual
type mutual

type scheme_object_function =
  | MutualSchemeFunction of mutual_scheme_object_function
  | IndividualSchemeFunction of individual_scheme_object_function

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
    user_err ~hdr:"IndTables.declare_scheme_object"
      (str "Scheme object " ++ str key ++ str " already declared.")
  with Not_found ->
    Hashtbl.add scheme_object_table key (s,f);
    key

let declare_mutual_scheme_object s ?(aux="") f =
  declare_scheme_object s aux (MutualSchemeFunction f)

let declare_individual_scheme_object s ?(aux="") f =
  declare_scheme_object s aux (IndividualSchemeFunction f)

(**********************************************************************)
(* Defining/retrieving schemes *)

let is_visible_name id =
  try ignore (Nametab.locate (Libnames.qualid_of_ident id)); true
  with Not_found -> false

let compute_name internal id =
  if internal then
    Namegen.next_ident_away_from (add_prefix "internal_" id) (Id.AvoidSet.of_pred is_visible_name)
  else id

let define internal role id c poly univs =
  let id = compute_name internal id in
  let ctx = UState.minimize univs in
  let c = UnivSubst.nf_evars_and_universes_opt_subst (fun _ -> None) (UState.subst ctx) c in
  let univs = UState.univ_entry ~poly ctx in
  let entry = Declare.pure_definition_entry ~univs c in
  let kn, eff = Declare.declare_private_constant ~role ~kind:Decls.(IsDefinition Scheme) ~name:id entry in
  let () = if internal then () else Declare.definition_message id in
  kn, eff

let define_individual_scheme_base kind suff f mode idopt (mind,i as ind) =
  let (c, ctx), eff = f mode ind in
  let mib = Global.lookup_mind mind in
  let id = match idopt with
    | Some id -> id
    | None -> add_suffix mib.mind_packets.(i).mind_typename suff in
  let role = Evd.Schema (ind, kind) in
  let internal = mode == InternalTacticRequest in
  let const, neff = define internal role id c (Declareops.inductive_is_polymorphic mib) ctx in
  DeclareScheme.declare_scheme kind [|ind,const|];
  const, Evd.concat_side_effects neff eff

let define_individual_scheme kind mode names (mind,i as ind) =
  match Hashtbl.find scheme_object_table kind with
  | _,MutualSchemeFunction f -> assert false
  | s,IndividualSchemeFunction f ->
      define_individual_scheme_base kind s f mode names ind

let define_mutual_scheme_base kind suff f mode names mind =
  let (cl, ctx), eff = f mode mind in
  let mib = Global.lookup_mind mind in
  let ids = Array.init (Array.length mib.mind_packets) (fun i ->
      try Int.List.assoc i names
      with Not_found -> add_suffix mib.mind_packets.(i).mind_typename suff) in
  let fold i effs id cl =
    let role = Evd.Schema ((mind, i), kind)in
    let internal = mode == InternalTacticRequest in
    let cst, neff = define internal role id cl (Declareops.inductive_is_polymorphic mib) ctx in
    (Evd.concat_side_effects neff effs, cst)
  in
  let (eff, consts) = Array.fold_left2_map_i fold eff ids cl in
  let schemes = Array.mapi (fun i cst -> ((mind,i),cst)) consts in
  DeclareScheme.declare_scheme kind schemes;
  consts, eff

let define_mutual_scheme kind mode names mind =
  match Hashtbl.find scheme_object_table kind with
  | _,IndividualSchemeFunction _ -> assert false
  | s,MutualSchemeFunction f ->
      define_mutual_scheme_base kind s f mode names mind

let find_scheme_on_env_too kind ind =
  let s = DeclareScheme.lookup_scheme kind ind in
  s, Evd.empty_side_effects

let find_scheme ?(mode=InternalTacticRequest) kind (mind,i as ind) =
  try find_scheme_on_env_too kind ind
  with Not_found ->
  match Hashtbl.find scheme_object_table kind with
  | s,IndividualSchemeFunction f ->
      define_individual_scheme_base kind s f mode None ind
  | s,MutualSchemeFunction f ->
      let ca, eff = define_mutual_scheme_base kind s f mode [] mind in
      ca.(i), eff

let define_individual_scheme kind mode names ind =
  ignore (define_individual_scheme kind mode names ind)

let define_mutual_scheme kind mode names mind =
  ignore (define_mutual_scheme kind mode names mind)

let check_scheme kind ind =
  try let _ = find_scheme_on_env_too kind ind in true
  with Not_found -> false

let lookup_scheme = DeclareScheme.lookup_scheme
