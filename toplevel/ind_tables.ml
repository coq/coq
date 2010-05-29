(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
open Term
open Util
open Declare
open Entries
open Decl_kinds

(**********************************************************************)
(* Registering schemes in the environment *)

type mutual_scheme_object_function = mutual_inductive -> constr array
type individual_scheme_object_function = inductive -> constr

type 'a scheme_kind = string

let scheme_map = ref Indmap.empty

let cache_one_scheme kind (ind,const) =
  let map = try Indmap.find ind !scheme_map with Not_found -> Stringmap.empty in
  scheme_map := Indmap.add ind (Stringmap.add kind const map) !scheme_map

let cache_scheme (_,(kind,l)) =
  Array.iter (cache_one_scheme kind) l

let subst_one_scheme subst ((mind,i),const) =
  (* Remark: const is a def: the result of substitution is a constant *)
  ((subst_ind subst mind,i),fst (subst_con subst const))

let subst_scheme (subst,(kind,l)) =
  (kind,Array.map (subst_one_scheme subst) l)

let discharge_scheme (_,(kind,l)) =
  Some (kind,Array.map (fun (ind,const) ->
    (Lib.discharge_inductive ind,Lib.discharge_con const)) l)

let (inScheme,_) =
  declare_object {(default_object "SCHEME") with
                    cache_function = cache_scheme;
                    load_function = (fun _ -> cache_scheme);
                    subst_function = subst_scheme;
		    classify_function = (fun obj -> Substitute obj);
		    discharge_function = discharge_scheme}

(**********************************************************************)
(* Saving/restoring the table of scheme *)

let freeze_schemes () = !scheme_map
let unfreeze_schemes sch = scheme_map := sch
let init_schemes () = scheme_map := Indmap.empty

let _ =
  Summary.declare_summary "Schemes"
    { Summary.freeze_function = freeze_schemes;
      Summary.unfreeze_function = unfreeze_schemes;
      Summary.init_function = init_schemes }

(**********************************************************************)
(* The table of scheme building functions *)

type individual
type mutual

type scheme_object_function =
  | MutualSchemeFunction of (mutual_inductive -> constr array)
  | IndividualSchemeFunction of (inductive -> constr)

let scheme_object_table =
  (Hashtbl.create 17 : (string, string * scheme_object_function) Hashtbl.t)

let declare_scheme_object s aux f =
  (try check_ident ("ind"^s) with _ ->
    error ("Illegal induction scheme suffix: "^s));
  let key = if aux = "" then s else aux in
  try
    let _ = Hashtbl.find scheme_object_table key in
(*    let aux_msg = if aux="" then "" else " (with key "^aux^")" in*)
    error ("Scheme object "^key^" already declared.")
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

let define internal id c =
  let fd = if internal then declare_internal_constant else declare_constant in
  let kn = fd id
    (DefinitionEntry
      { const_entry_body = c;
        const_entry_type = None;
        const_entry_opaque = false;
	const_entry_boxed = Flags.boxed_definitions() },
      Decl_kinds.IsDefinition Scheme) in
  if not internal then definition_message id;
  kn

let define_individual_scheme_base kind suff f internal idopt (mind,i as ind) =
  let c = f ind in
  let mib = Global.lookup_mind mind in
  let id = match idopt with
    | Some id -> id
    | None -> add_suffix mib.mind_packets.(i).mind_typename suff in
  let const = define internal id c in
  declare_scheme kind [|ind,const|];
  const

let define_individual_scheme kind internal names (mind,i as ind) =
  match Hashtbl.find scheme_object_table kind with
  | _,MutualSchemeFunction f -> assert false
  | s,IndividualSchemeFunction f ->
      define_individual_scheme_base kind s f internal names ind

let define_mutual_scheme_base kind suff f internal names mind =
  let cl = f mind in
  let mib = Global.lookup_mind mind in
  let ids = Array.init (Array.length mib.mind_packets) (fun i ->
      try List.assoc i names
      with Not_found -> add_suffix mib.mind_packets.(i).mind_typename suff) in
  let consts = array_map2 (define internal) ids cl in
  declare_scheme kind (Array.mapi (fun i cst -> ((mind,i),cst)) consts);
  consts

let define_mutual_scheme kind internal names mind =
  match Hashtbl.find scheme_object_table kind with
  | _,IndividualSchemeFunction _ -> assert false
  | s,MutualSchemeFunction f ->
      define_mutual_scheme_base kind s f internal names mind

let find_scheme kind (mind,i as ind) =
  try Stringmap.find kind (Indmap.find ind !scheme_map)
  with Not_found ->
  match Hashtbl.find scheme_object_table kind with
  | s,IndividualSchemeFunction f ->
      define_individual_scheme_base kind s f true None ind
  | s,MutualSchemeFunction f ->
      (define_mutual_scheme_base kind s f true [] mind).(i)

let check_scheme kind ind =
  try let _ = Stringmap.find kind (Indmap.find ind !scheme_map) in true
  with Not_found -> false

