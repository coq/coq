(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Constr
open Evd
open Util
open Typeclasses_errors

(*i*)

(* Core typeclasses hints *)
type 'a hint_info_gen =
    { hint_priority : int option;
      hint_pattern : 'a option }

type hint_info = (Id.Set.t * Pattern.constr_pattern) hint_info_gen

let { Goptions.get = get_typeclasses_unique_solutions } =
  Goptions.declare_bool_option_and_ref
    ~key:["Typeclasses";"Unique";"Solutions"]
    ~value:false
    ()

type class_method = {
  meth_name : Name.t;
  meth_const : Constant.t option;
}

(* This module defines type-classes *)
type typeclass = {
  (* Universe quantification *)
  cl_univs : UVars.AbstractContext.t;

  (* The class implementation *)
  cl_impl : GlobRef.t;

  cl_context : Constr.rel_context;

  cl_trivial : bool;

  cl_props : Constr.rel_context;

  cl_projs : class_method list;

  cl_strict : bool;

  cl_unique : bool;
}

type typeclasses = typeclass GlobRef.Map.t
(* Invariant: for any pair (gr, tc) in the map, gr and tc.cl_impl are equal *)

type instance = {
  is_class: GlobRef.t;
  is_info: hint_info;
  is_impl: GlobRef.t;
}

type instances = (instance GlobRef.Map.t) GlobRef.Map.t

let instance_impl is = is.is_impl

let hint_priority is = is.is_info.hint_priority

(*
 * states management
 *)

let classes : typeclasses ref = Summary.ref GlobRef.Map.empty ~name:"classes"
let instances : instances ref = Summary.ref GlobRef.Map.empty ~name:"instances"

let class_info c = GlobRef.Map.find_opt c !classes

let class_info_exn env sigma r =
  match class_info r with
  | Some v -> v
  | None ->
    let sigma, c = Evd.fresh_global env sigma r in
    not_a_class env sigma c

let global_class_of_constr env sigma c =
  try let gr, u = EConstr.destRef sigma c in
    GlobRef.Map.find gr !classes, u
  with DestKO | Not_found -> not_a_class env sigma c

let decompose_class_app env sigma c =
  let hd, args = EConstr.decompose_app_list sigma c in
  match EConstr.kind sigma hd with
  | Proj (p, _, c) ->
    let expp = Retyping.expand_projection env sigma p c args in
    EConstr.decompose_app_list sigma expp
  | _ -> hd, args

let dest_class_app env sigma c =
  let cl, args = decompose_class_app env sigma c in
    global_class_of_constr env sigma cl, (List.map EConstr.Unsafe.to_constr args)

let dest_class_arity env sigma c =
  let open EConstr in
  let rels, c = decompose_prod_decls sigma c in
    rels, dest_class_app (push_rel_context rels env) sigma c

let class_of_constr env sigma c =
  try Some (dest_class_arity env sigma c)
  with e when CErrors.noncritical e -> None

let is_class_constr sigma c =
  try let gr, u = EConstr.destRef sigma c in
    GlobRef.Map.mem gr !classes
  with DestKO | Not_found -> false

let rec is_class_type evd c =
  let c, _ = EConstr.decompose_app evd c in
    match EConstr.kind evd c with
    | Prod (_, _, t) -> is_class_type evd t
    | Cast (t, _, _) -> is_class_type evd t
    | Proj (p, _, c) -> GlobRef.(Map.mem (ConstRef (Projection.constant p))) !classes
    | _ -> is_class_constr evd c

let is_class_evar evd evi =
  is_class_type evd (Evd.evar_concl evi)

let rec is_maybe_class_type evd c =
  let c, _ = EConstr.decompose_app evd c in
    match EConstr.kind evd c with
    | Prod (_, _, t) -> is_maybe_class_type evd t
    | Cast (t, _, _) -> is_maybe_class_type evd t
    | Evar _ -> true
    | Proj (p, _, c) -> GlobRef.(Map.mem (ConstRef (Projection.constant p))) !classes
    | _ -> is_class_constr evd c

let () = Hook.set Evd.is_maybe_typeclass_hook (fun evd c -> is_maybe_class_type evd c)

let load_class cl =
  classes := GlobRef.Map.add cl.cl_impl cl !classes

(** Build the subinstances hints. *)

(*
 * interface functions
 *)

let load_instance inst =
  let insts =
    try GlobRef.Map.find inst.is_class !instances
    with Not_found -> GlobRef.Map.empty in
  let insts = GlobRef.Map.add inst.is_impl inst insts in
  instances := GlobRef.Map.add inst.is_class insts !instances

let remove_instance inst =
  let insts =
    try GlobRef.Map.find inst.is_class !instances
    with Not_found -> assert false in
  let insts = GlobRef.Map.remove inst.is_impl insts in
  instances := GlobRef.Map.add inst.is_class insts !instances

let typeclasses () = GlobRef.Map.fold (fun _ l c -> l :: c) !classes []

let cmap_elements c = GlobRef.Map.fold (fun k v acc -> v :: acc) c []

let instances_of c =
  try cmap_elements (GlobRef.Map.find c.cl_impl !instances) with Not_found -> []

let all_instances () =
  GlobRef.Map.fold (fun k v acc ->
    GlobRef.Map.fold (fun k v acc -> v :: acc) v acc)
    !instances []

let instances r =
  Option.map instances_of (class_info r)

let instances_exn env sigma r =
  match instances r with
  | Some v -> v
  | None ->
    let sigma, c = Evd.fresh_global env sigma r in
    not_a_class env sigma c

let is_class gr =
  GlobRef.Map.mem gr !classes

open Evar_kinds
type evar_filter = Evar.t -> Evar_kinds.t Lazy.t -> bool

let make_unresolvables filter evd =
  let tcs = Evd.get_typeclass_evars evd in
  Evd.set_typeclass_evars evd (Evar.Set.filter (fun x -> not (filter x)) tcs)

let all_evars _ _ = true
let all_goals _ source =
  match Lazy.force source with
  | VarInstance _ | GoalEvar -> true
  | _ -> false

let no_goals ev evi = not (all_goals ev evi)
let no_goals_or_obligations _ source =
  match Lazy.force source with
  | VarInstance _ | GoalEvar | QuestionMark _ -> false
  | _ -> true

let has_typeclasses filter evd =
  let tcs = get_typeclass_evars evd in
  let check ev = filter ev (lazy (snd (Evd.evar_source (Evd.find_undefined evd ev)))) in
  Evar.Set.exists check tcs

let get_filtered_typeclass_evars filter evd =
  let tcs = get_typeclass_evars evd in
  let check ev = filter ev (lazy (snd (Evd.evar_source (Evd.find_undefined evd ev)))) in
  Evar.Set.filter check tcs

let solve_all_instances_hook = ref (fun env evd filter unique fail -> assert false)

let solve_all_instances env evd filter unique fail =
  !solve_all_instances_hook env evd filter unique fail

let set_solve_all_instances f = solve_all_instances_hook := f

let resolve_typeclasses ?(filter=no_goals) ?(unique=get_typeclasses_unique_solutions ())
    ?(fail=true) env evd =
  if not (has_typeclasses filter evd) then evd
  else solve_all_instances env evd filter unique fail

(** In case of unsatisfiable constraints, build a nice error message *)

let error_unresolvable env evd comp =
  let exception MultipleFound in
  let fold ev accu =
    match Evd.find_undefined evd ev with
    | exception Not_found -> None
    | evi ->
      let ev_class = class_of_constr env evd (Evd.evar_concl evi) in
      if Option.is_empty ev_class then accu
      else (* focus on one instance if only one was searched for *)
      if Option.has_some accu then raise MultipleFound
      else (Some ev)
  in
  let ev = try Evar.Set.fold fold comp None with MultipleFound -> None in
  Pretype_errors.unsatisfiable_constraints env evd ev comp

(** Deprecated *)

let solve_one_instance = ref (fun env evm t -> assert false)

let resolve_one_typeclass ?unique:_ env evm t =
  !solve_one_instance env evm t

let set_solve_one_instance f = solve_one_instance := f
