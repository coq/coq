(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
open Mod_subst
open Libobject
open Nameops
open Declarations
open Constr
open CErrors
open Util
open Declare
open Entries
open Decl_kinds
open Pp

(**********************************************************************)
(* Registering schemes in the environment *)

type mutual_scheme_object_function =
  internal_flag -> MutInd.t -> constr array Evd.in_evar_universe_context * Safe_typing.private_constants
type individual_scheme_object_function =
  internal_flag -> inductive -> constr Evd.in_evar_universe_context * Safe_typing.private_constants

type 'a scheme_kind = string

let scheme_map = Summary.ref Indmap.empty ~name:"Schemes"

let pr_scheme_kind = Pp.str

let cache_one_scheme kind (ind,const) =
  let map = try Indmap.find ind !scheme_map with Not_found -> String.Map.empty in
  scheme_map := Indmap.add ind (String.Map.add kind const map) !scheme_map

let cache_scheme (_,(kind,l)) =
  Array.iter (cache_one_scheme kind) l

let subst_one_scheme subst (ind,const) =
  (* Remark: const is a def: the result of substitution is a constant *)
  (subst_ind subst ind,subst_constant subst const)

let subst_scheme (subst,(kind,l)) =
  (kind,Array.Smart.map (subst_one_scheme subst) l)

let discharge_scheme (_,(kind,l)) =
  Some (kind,Array.map (fun (ind,const) ->
    (Lib.discharge_inductive ind,Lib.discharge_con const)) l)

let inScheme : string * (inductive * Constant.t) array -> obj =
  declare_object {(default_object "SCHEME") with
                    cache_function = cache_scheme;
                    load_function = (fun _ -> cache_scheme);
                    subst_function = subst_scheme;
		    classify_function = (fun obj -> Substitute obj);
		    discharge_function = discharge_scheme}

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

let declare_scheme kind indcl =
  Lib.add_anonymous_leaf (inScheme (kind,indcl))

let () = Declare.set_declare_scheme declare_scheme

let is_visible_name id =
  try ignore (Nametab.locate (Libnames.qualid_of_ident id)); true
  with Not_found -> false

let compute_name internal id =
  match internal with
  | UserAutomaticRequest | UserIndividualRequest -> id
  | InternalTacticRequest ->
      Namegen.next_ident_away_from (add_prefix "internal_" id) is_visible_name

let define internal id c p univs =
  let fd = declare_constant ~internal in
  let id = compute_name internal id in
  let ctx = UState.minimize univs in
  let c = UnivSubst.nf_evars_and_universes_opt_subst (fun _ -> None) (UState.subst ctx) c in
  let univs =
    if p then Polymorphic_const_entry (UState.context ctx)
    else Monomorphic_const_entry (UState.context_set ctx)
  in
  let entry = {
    const_entry_body =
      Future.from_val ((c,Univ.ContextSet.empty),
                       Safe_typing.empty_private_constants);
    const_entry_secctx = None;
    const_entry_type = None;
    const_entry_universes = univs;
    const_entry_opaque = false;
    const_entry_inline_code = false;
    const_entry_feedback = None;
  } in
  let kn = fd id (DefinitionEntry entry, Decl_kinds.IsDefinition Scheme) in
  let () = match internal with
    | InternalTacticRequest -> ()
    | _-> definition_message id
  in
  kn

let define_individual_scheme_base kind suff f mode idopt (mind,i as ind) =
  let (c, ctx), eff = f mode ind in
  let mib = Global.lookup_mind mind in
  let id = match idopt with
    | Some id -> id
    | None -> add_suffix mib.mind_packets.(i).mind_typename suff in
  let const = define mode id c (Declareops.inductive_is_polymorphic mib) ctx in
  declare_scheme kind [|ind,const|];
  const, Safe_typing.concat_private
     (Safe_typing.private_con_of_scheme ~kind (Global.safe_env()) [ind,const]) eff

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
  let consts = Array.map2 (fun id cl -> 
     define mode id cl (Declareops.inductive_is_polymorphic mib) ctx) ids cl in
  let schemes = Array.mapi (fun i cst -> ((mind,i),cst)) consts in
  declare_scheme kind schemes;
  consts,
  Safe_typing.concat_private
    (Safe_typing.private_con_of_scheme
      ~kind (Global.safe_env()) (Array.to_list schemes))
    eff 

let define_mutual_scheme kind mode names mind =
  match Hashtbl.find scheme_object_table kind with
  | _,IndividualSchemeFunction _ -> assert false
  | s,MutualSchemeFunction f ->
      define_mutual_scheme_base kind s f mode names mind

let find_scheme_on_env_too kind ind =
  let s = String.Map.find kind (Indmap.find ind !scheme_map) in
  s, Safe_typing.concat_private
      (Safe_typing.private_con_of_scheme
            ~kind (Global.safe_env()) [ind, s])
      Safe_typing.empty_private_constants

let find_scheme ?(mode=InternalTacticRequest) kind (mind,i as ind) =
  try find_scheme_on_env_too kind ind
  with Not_found ->
  match Hashtbl.find scheme_object_table kind with
  | s,IndividualSchemeFunction f ->
      define_individual_scheme_base kind s f mode None ind
  | s,MutualSchemeFunction f ->
      let ca, eff = define_mutual_scheme_base kind s f mode [] mind in
      ca.(i), eff

let check_scheme kind ind =
  try let _ = find_scheme_on_env_too kind ind in true
  with Not_found -> false
