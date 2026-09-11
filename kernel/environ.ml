(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Author: Jean-Christophe Filliâtre as part of the rebuilding of Coq
   around a purely functional abstract type-checker, Aug 1999 *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Flag for predicativity of Set by Hugo Herbelin in Oct 2003 *)
(* Support for virtual machine by Benjamin Grégoire in Oct 2004 *)
(* Support for retroknowledge by Arnaud Spiwack in May 2007 *)
(* Support for assumption dependencies by Arnaud Spiwack in May 2007 *)

(* Miscellaneous maintenance by Bruno Barras, Hugo Herbelin, Jean-Marc
   Notin, Matthieu Sozeau *)

(* This file defines the type of environments on which the
   type-checker works, together with simple related functions *)

open CErrors
open Util
open Names
open Constr
open Vars
open Declarations
open Mod_declarations
open Context.Rel.Declaration

module NamedDecl = Context.Named.Declaration

(* The type of environments. *)

(* The key attached to each constant is used by the VM to retrieve previous *)
(* evaluations of the constant. It is essentially an index in the symbols table *)
(* used by the VM. *)
type key = int CEphemeron.key option ref

(** Linking information for the native compiler. *)

type link_info =
  | Linked of string
  | NotLinked

type constant_key = constant_body * (link_info ref * key) * KerName.t

module DepCache :
sig
  type t
  val empty : t
  val get : Constant.t -> t -> (Cset_env.t, Cset_env.t -> unit) union
  val fresh : t -> t
end =
struct

type t = Cset_env.t Cmap_env.t ref option

let empty = None

let get kn cache = match cache with
| None -> Inr ignore
| Some cache ->
  match Cmap_env.find_opt kn !cache with
  | None -> Inr (fun s -> cache := Cmap_env.add kn s !cache)
  | Some s -> Inl s

let fresh = function
| None -> Some (ref Cmap_env.empty)
| Some cache -> Some (ref !cache)

end

type mind_key = mutual_inductive_body * link_info ref * KerName.t

type named_context_val = {
  env_named_ctx : Constr.named_context;
  env_named_map : Constr.named_declaration Id.Map.t;
  env_named_idx : Constr.named_declaration Range.t;
  env_named_secvars : Id.Set.t;
}

type rel_context_val = {
  env_rel_ctx : Constr.rel_context;
  env_rel_map : Constr.rel_declaration Range.t;
}

type env = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mind_key Mindmap_env.t;
  env_modules : module_body ModPath.Map.t;
  env_modtypes : module_type_body ModPath.Map.t;
  env_named_context : named_context_val; (* section variables *)
  env_rel_context   : rel_context_val;
  env_universes : UGraph.t;
  env_qualities : QGraph.t;
  symb_pats : machine_rewrite_rule list Cmap_env.t;
  env_typing_flags  : typing_flags;
  vm_library : Vmlibrary.t;
  retroknowledge : Retroknowledge.retroknowledge;
  rewrite_rules_allowed : bool;

  (* caches *)
  env_nb_rel        : int;
  irr_constants : Sorts.relevance Cmap_env.t;
  irr_inds : Sorts.relevance Indmap_env.t;
  constant_hyps : Id.Set.t Cmap_env.t;
  inductive_hyps : Id.Set.t Mindmap_env.t;
  constant_deps : DepCache.t CEphemeron.key;
}

type rewrule_not_allowed = Symb | Rule
exception RewriteRulesNotAllowed of rewrule_not_allowed

let empty_named_context_val = {
  env_named_ctx = [];
  env_named_map = Id.Map.empty;
  env_named_idx = Range.empty;
  env_named_secvars = Id.Set.empty;
}

let empty_rel_context_val = {
  env_rel_ctx = [];
  env_rel_map = Range.empty;
}

let empty_env = {
  env_constants = Cmap_env.empty;
  env_inductives = Mindmap_env.empty;
  env_modules = ModPath.Map.empty;
  env_modtypes = ModPath.Map.empty;
  constant_hyps = Cmap_env.empty;
  inductive_hyps = Mindmap_env.empty;
  env_named_context = empty_named_context_val;
  env_rel_context = empty_rel_context_val;
  env_nb_rel = 0;
  env_universes = UGraph.initial_universes;
  env_qualities = QGraph.initial_graph;
  irr_constants = Cmap_env.empty;
  irr_inds = Indmap_env.empty;
  symb_pats = Cmap_env.empty;
  env_typing_flags = Declareops.safe_flags Conv_oracle.empty;
  vm_library = Vmlibrary.empty;
  retroknowledge = Retroknowledge.empty;
  rewrite_rules_allowed = false;
  constant_deps = CEphemeron.create DepCache.empty;
}


(* Rel context *)

let push_rel_context_val d ctx = {
  env_rel_ctx = Context.Rel.add d ctx.env_rel_ctx;
  env_rel_map = Range.cons d ctx.env_rel_map;
}

let match_rel_context_val ctx = match ctx.env_rel_ctx with
| [] -> None
| decl :: rem ->
  let ctx = { env_rel_ctx = rem; env_rel_map = Range.tl ctx.env_rel_map } in
  Some (decl, ctx)

let push_rel d env =
    { env with
      env_rel_context = push_rel_context_val d env.env_rel_context;
      env_nb_rel = env.env_nb_rel + 1 }

let lookup_rel n env =
  try Range.get env.env_rel_context.env_rel_map (n - 1)
  with Invalid_argument _ -> raise Not_found

let lookup_rel_ctxt n ctx =
  try Range.get ctx.env_rel_map (n - 1)
  with Invalid_argument _ -> raise Not_found

let rel_skipn n ctx = {
  env_rel_ctx = Util.List.skipn n ctx.env_rel_ctx;
  env_rel_map = Range.skipn n ctx.env_rel_map;
}

let env_of_rel n env =
  { env with
    env_rel_context = rel_skipn n env.env_rel_context;
    env_nb_rel = env.env_nb_rel - n
  }

let set_rel_context_val v env =
  { env with
    env_rel_context = v;
    env_nb_rel = Range.length v.env_rel_map; }

(* Named context *)
type var_status = SecVar | ProofVar

let var_status_eq a b = match a, b with
  | SecVar, SecVar -> true
  | ProofVar, ProofVar -> true
  | (SecVar | ProofVar), _ -> false

let push_named_context_val status d ctxt =
  let id = NamedDecl.get_id d in
  (* we would like the stronger assert but it breaks in bug_4095 *)
  (* assert (not (Id.Map.mem id ctxt.env_named_map)); *)
  assert (not (Id.Set.mem id ctxt.env_named_secvars));
  let secvars = match status with
    | ProofVar -> ctxt.env_named_secvars
    | SecVar -> Id.Set.add id ctxt.env_named_secvars
  in
  {
    env_named_ctx = Context.Named.add d ctxt.env_named_ctx;
    env_named_map = Id.Map.add id d ctxt.env_named_map;
    env_named_idx = Range.cons d ctxt.env_named_idx;
    env_named_secvars = secvars;
  }

let var_status_ctxt ?(check=true) id ctxt =
  if Id.Set.mem id ctxt.env_named_secvars then SecVar
  else
    let () = assert (not check || Id.Map.mem id ctxt.env_named_map) in
    ProofVar

let var_status ?check id env = var_status_ctxt ?check id env.env_named_context

let section_variables_ctxt ctxt = ctxt.env_named_secvars

let section_variables env = section_variables_ctxt env.env_named_context

let match_named_context_val c = match c.env_named_ctx with
| [] -> None
| decl :: ctx ->
  let id = NamedDecl.get_id decl in
  let map = Id.Map.remove id c.env_named_map in
  let secvars = Id.Set.remove id c.env_named_secvars in
  let status = if secvars == c.env_named_secvars then ProofVar else SecVar in
  let cval = {
    env_named_ctx = ctx;
    env_named_map = map;
    env_named_idx = Range.tl c.env_named_idx;
    env_named_secvars = secvars;
  }
  in
  Some (status, decl, cval)

let map_named_val f ctxt =
  let open Context.Named.Declaration in
  let fold (map,secvars) d =
    let id = get_id d in
    let status = var_status_ctxt ~check:false id ctxt in
    let status', d' = f status d in
    let () = assert (Id.equal id (get_id d')) in
    let map =
      if d == d' then map
      else Id.Map.set id d' map
    in
    let secvars =
      if status == status' then secvars else
        match status' with
        | SecVar -> Id.Set.add id secvars
        | ProofVar -> Id.Set.remove id secvars
    in
    ((map,secvars), d')
  in
  let (map,secvars), ctx = List.Smart.fold_left_map fold (ctxt.env_named_map,ctxt.env_named_secvars) ctxt.env_named_ctx in
  if map == ctxt.env_named_map && secvars == ctxt.env_named_secvars then ctxt
  else
    let idx = List.fold_right Range.cons ctx Range.empty in
    { env_named_ctx = ctx; env_named_map = map; env_named_idx = idx; env_named_secvars = secvars }

let push_named status d env =
  {env with env_named_context = push_named_context_val status d env.env_named_context}

let mem_named_ctxt id ctxt =
  Id.Map.mem id ctxt.env_named_map

let mem_named id env = mem_named_ctxt id  env.env_named_context

let lookup_named id env =
  Id.Map.find id env.env_named_context.env_named_map

let lookup_named_ctxt id ctxt =
  Id.Map.find id ctxt.env_named_map

let lookup_named_ctxt_pos n ctxt =
  try Range.get ctxt.env_named_idx n with Invalid_argument _ -> raise Not_found

let nb_named ctx = Range.length ctx.env_named_idx

let record_global_hyps add kn hyps acc =
  if CList.is_empty hyps then acc
  else add kn (Context.Named.to_vars hyps) acc

let fold_constants f env acc =
  Cmap_env.fold (fun c (body,_,_) acc -> f c body acc) env.env_constants acc

let fold_inductives f env acc =
  Mindmap_env.fold (fun c (body,_,_) acc -> f c body acc) env.env_inductives acc

(* Global constants *)

let lookup_constant_opt kn env =
  match Cmap_env.find_opt kn env.env_constants with
  | None -> None
  | Some (cb, _, _) -> Some cb

let missing_constant kn =
  anomaly Pp.(str "Constant " ++ Constant.print kn ++ str" does not appear in the environment.")

let lookup_constant_key kn env = match Cmap_env.find_opt kn env.env_constants with
| None -> missing_constant kn
| Some (_, key, _) -> key

let lookup_constant kn env = match Cmap_env.find_opt kn env.env_constants with
| None -> missing_constant kn
| Some (cb, _, _) -> cb

let lookup_constant_canonical kn env = match Cmap_env.find_opt kn env.env_constants with
| None -> missing_constant kn
| Some (_, _, can) -> can

let mem_constant kn env = Cmap_env.mem kn env.env_constants

let add_rewrite_rules l env =
  if not env.rewrite_rules_allowed then raise (RewriteRulesNotAllowed Rule);
  let add c r = function
    | None -> anomaly Pp.(str "Trying to add a rule to non-symbol " ++ Constant.print c ++ str".")
    | Some rs -> Some (r::rs)
  in
  { env with
    symb_pats = List.fold_left (fun symb_pats (c, r) -> Cmap_env.update c (add c r) symb_pats) env.symb_pats l
  }

let lookup_rewrite_rules cst env =
  Cmap_env.find cst env.symb_pats

(* Mutual Inductives *)

let missing_ind kn =
  anomaly Pp.(str "Inductive " ++ MutInd.print kn ++ str" does not appear in the environment.")

let lookup_mind kn env = match Mindmap_env.find_opt kn env.env_inductives with
| None -> missing_ind kn
| Some (mib, _, _) -> mib

let lookup_mind_key kn env = match Mindmap_env.find_opt kn env.env_inductives with
| None -> missing_ind kn
| Some (_, key, _) -> key

let lookup_mind_canonical kn env = match Mindmap_env.find_opt kn env.env_inductives with
| None -> missing_ind kn
| Some (_, _, can) -> can

let ind_relevance kn env = match Indmap_env.find_opt kn env.irr_inds with
| None -> Sorts.Relevant
| Some r -> r

(** {6 Changes of representation of Case nodes} *)

(** Provided:
    - a universe instance [u]
    - a term substitution [subst]
    - name replacements [nas]
    [instantiate_context u subst nas ctx] applies both [u] and [subst] to [ctx]
    while replacing names using [nas] (order reversed)
*)

let get_template_instance mib u = match mib.mind_template with
| None -> u
| Some templ ->
  let () = assert (UVars.Instance.is_empty u) in
  templ.template_defaults

let instantiate_context u subst nas ctx =
  let open Context.Rel.Declaration in
  let get_binder i na =
    Context.
    { binder_name = nas.(i).binder_name;
      binder_relevance = UVars.subst_instance_relevance u na.binder_relevance }
  in
  let rec instantiate i ctx = match ctx with
  | [] -> assert (Int.equal i (-1)); []
  | LocalAssum (na, ty) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let na = get_binder i na in
    LocalAssum (na, ty) :: ctx
  | LocalDef (na, ty, bdy) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let bdy = substnl subst i (subst_instance_constr u bdy) in
    let na = get_binder i na in
    LocalDef (na, ty, bdy) :: ctx
  in
  instantiate (Array.length nas - 1) ctx

let expand_arity (mib, mip) (ind, u) params nas =
  let open Context.Rel.Declaration in
  let u = get_template_instance mib u in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let params = Vars.subst_of_rel_context_instance paramdecl params in
  let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
  let self =
    let u =
      if Option.has_some mib.mind_template then UVars.Instance.empty
      else UVars.Instance.abstract_instance (UVars.Instance.length u)
    in
    let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
    mkApp (mkIndU (ind, u), args)
  in
  let na = Context.make_annot Anonymous mip.mind_relevance in
  let realdecls = LocalAssum (na, self) :: realdecls in
  instantiate_context u params nas realdecls

let expand_branch_contexts (mib, mip) u params br =
  let u = get_template_instance mib u in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in
  let build_one_branch i (nas, _) (ctx, _) =
    let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
    let ctx = instantiate_context u paramsubst nas ctx in
    ctx
  in
  Array.map2_i build_one_branch br mip.mind_nf_lc


let mem_mind kn env = Mindmap_env.mem kn env.env_inductives

let mind_context env mind =
  let mib = lookup_mind mind env in
  Declareops.inductive_polymorphic_context mib

let oracle env = env.env_typing_flags.conv_oracle
let set_oracle env o =
  let env_typing_flags = { env.env_typing_flags with conv_oracle = o } in
  { env with env_typing_flags }

let typing_flags env = env.env_typing_flags

let is_impredicative_set env = env.env_typing_flags.impredicative_set

let is_impredicative_sort env = function
  | Sorts.SProp | Sorts.Prop -> true
  | Sorts.Set -> is_impredicative_set env
  | Sorts.Type _ | Sorts.VSort _ | Sorts.GSort _-> false

let type_in_type env = not (typing_flags env).check_universes
let ignore_elim_constraints env = not (typing_flags env).check_eliminations
let deactivated_guard env = not (typing_flags env).check_guarded

let indices_matter env = env.env_typing_flags.indices_matter

let universes env = env.env_universes

let set_universes g env =
  {env with env_universes=g}

let qualities env = env.env_qualities

let set_qualities g env =
  {env with env_qualities=g}

let named_context env = env.env_named_context.env_named_ctx
let named_context_val env = env.env_named_context
let rel_context env = env.env_rel_context.env_rel_ctx
let rel_context_val env = env.env_rel_context

let empty_context env =
  match env.env_rel_context.env_rel_ctx, env.env_named_context.env_named_ctx with
  | [], [] -> true
  | _ -> false

(* Rel context *)
let evaluable_rel n env =
  is_local_def (lookup_rel n env)

let nb_rel env = env.env_nb_rel

let push_rel_context ctxt x = Context.Rel.fold_outside push_rel ctxt ~init:x

let push_rec_types (lna,typarray,_) env =
  let ctxt = Array.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

let fold_rel_context f env ~init =
  let rec fold_right env =
    match match_rel_context_val env.env_rel_context with
    | None -> init
    | Some (rd, rc) ->
        let env =
          { env with
            env_rel_context = rc;
            env_nb_rel = env.env_nb_rel - 1 } in
        f env rd (fold_right env)
  in fold_right env

(* Named context *)

let named_context_of_val c = c.env_named_ctx

let named_context_of_val_with_status c =
  List.map (fun d -> var_status_ctxt ~check:false (NamedDecl.get_id d) c, d) c.env_named_ctx

let ids_of_named_context_val c = Id.Map.domain c.env_named_map

let empty_named_context = Context.Named.empty

let push_named_context = List.fold_right (fun (status,d) env -> push_named status d env)

let val_of_named_context ctxt =
  List.fold_right (fun (status,d) ctxt -> push_named_context_val status d ctxt)
    ctxt empty_named_context_val


let eq_named_context_val c1 c2 =
   c1 == c2 || Context.Named.equal Sorts.relevance_equal Constr.equal (named_context_of_val c1) (named_context_of_val c2)

(* A local const is evaluable if it is defined  *)

let named_type id env =
  let open Context.Named.Declaration in
  get_type (lookup_named id env)

let named_body id env =
  let open Context.Named.Declaration in
  get_value (lookup_named id env)

let evaluable_named id env =
  match named_body id env with
  | Some _      -> true
  | _          -> false

let reset_with_named_context ctxt env =
  { env with
    env_named_context = ctxt;
    env_rel_context = empty_rel_context_val;
    env_nb_rel = 0 }

let reset_context = reset_with_named_context empty_named_context_val

let pop_rel_context n env =
  let rec skip n ctx =
    if Int.equal n 0 then ctx
    else match match_rel_context_val ctx with
    | None -> invalid_arg "List.skipn"
    | Some (_, ctx) -> skip (pred n) ctx
  in
  let ctxt = env.env_rel_context in
  { env with
    env_rel_context = skip n ctxt;
    env_nb_rel = env.env_nb_rel - n }

let fold_named_context_val f sign ~init =
  let rec fold_right sign =
    match match_named_context_val sign with
    | None -> init
    | Some (status, d, rem) ->
      f rem status d (fold_right rem)
  in fold_right sign

let fold_named_context f env ~init =
  fold_named_context_val (fun sign status d acc ->
      f (reset_with_named_context sign env) status d acc)
    (named_context_val env) ~init

let fold_named_context_reverse f ~init env =
  Context.Named.fold_inside f ~init:init (named_context env)


(* Universe constraints *)

let map_universes f env = set_universes (f env.env_universes) env

let map_qualities f env = set_qualities (f env.env_qualities) env

let check_univ_constraints univ_csts env =
  UGraph.check_constraints univ_csts env.env_universes

let check_constraints (elim_csts,univ_csts) env =
  check_univ_constraints univ_csts env &&
    QGraph.check_constraints elim_csts env.env_qualities

let add_universes ~strict ctx g =
  let _, us = UVars.Instance.to_array (UVars.UContext.instance ctx) in
  let g = Array.fold_left
      (fun g v -> UGraph.add_universe ~strict v g)
      g us
  in
  UGraph.merge_constraints (UVars.UContext.univ_constraints ctx) g

let set_qualities g env = {env with env_qualities = g}

let add_qualities ctx g =
  let qs, _ = UVars.Instance.to_array (UVars.UContext.instance ctx) in
  let g = Array.fold_right QGraph.add_quality qs g in
  QGraph.merge_constraints (UVars.UContext.elim_constraints ctx) g

let push_context ?(strict=false) ctx env =
  let env = map_qualities (add_qualities ctx) env in
  map_universes (add_universes ~strict ctx) env

(* TODO: a bit wasteful, we typically call this before pushing the sort context *)
let check_ucontext ctx env =
  let qgraph = add_qualities ctx (qualities env) in
  if not (Sorts.ElimConstraints.is_empty @@ UVars.UContext.elim_constraints ctx) then
    QGraph.check_rigid_paths qgraph

let add_universes_set ~strict (lvl, cstr) g =
  let g = Univ.Level.Set.fold
            (* Be lenient, module typing reintroduces universes and constraints due to includes *)
            (fun v g -> try UGraph.add_universe ~strict v g with UGraph.AlreadyDeclared -> g)
            lvl g
  in
  UGraph.merge_constraints cstr g

let push_context_set ?(strict=false) ctx env =
  map_universes (add_universes_set ~strict ctx) env

let push_qualities qs env =
  let () = assert Sorts.Quality.Set.(is_empty @@ inter qs (QGraph.domain env.env_qualities)) in
  let g = Sorts.Quality.Set.fold QGraph.add_quality qs env.env_qualities in
  set_qualities g env

let merge_elim_constraints ~rigid qcsts env =
  let merge g =
    let g = QGraph.merge_constraints qcsts g in
    if rigid then
      let fold (q1, _, q2) accu = QGraph.add_rigid_path q1 q2 accu in
      Sorts.ElimConstraints.fold fold qcsts g
    else g
  in
  map_qualities merge env

(** [restrict_subgraph l c] produces [c'] such that [c + (Set <= l)] imply [c'],
    [c'] does not mention any of the levels in [l],
    and any constraint between levels not in [l] which is implied by [c + (Set <= l)]
    is also implied by [c'].

    We then rely on the fact that for any constraint set [d] which does not mention levels in [l],
    any constraint between levels not in [l] which is implied by [d + c + (Set <= l)]
    is also implied by [d + c'].
    Therefore if [d] implies [c'] then [c] adds no new constraints between non-[l] levels.

    (Given a path in [d + c + (Set <= l)], we can separate it in
    segments in [d] and segments in [c + (Set <= l)] where the
    endpoints of each segment are not in [l]. Then the non-[d]
    segments can be replaced by paths in [c'].)
*)
let restrict_subgraph levels univ_csts =
  let g = UGraph.initial_universes in
  let mentioned_univs =
    Univ.UnivConstraints.fold (fun (u,_,v) acc ->
        Univ.Level.Set.(add u (add v acc)))
      univ_csts
      (* do not forget Set: if we have preexisting univ u and new univ v with v < u,
         this implies Set < u.
         (in other words we have implicit Set <= v constraints for every new v) *)
      (Univ.Level.Set.singleton Univ.Level.set)
  in
  let g = Univ.Level.Set.fold (fun v g ->
      if Univ.Level.is_set v then g else UGraph.add_universe ~strict:false v g)
      mentioned_univs g
  in
  (* having to merge_constraints twice (here and in add_subgraph) is
     not great but better than having to crawl the full env's graph to
     check the subgraph property *)
  let g = UGraph.merge_constraints univ_csts g in
  let kept = Univ.Level.Set.diff mentioned_univs levels in
  UGraph.constraints_for ~kept g

let push_subgraph (levels, univ_csts) env =
  let add_subgraph g =
    let newg = Univ.Level.Set.fold (fun v g -> UGraph.add_universe ~strict:false v g) levels g in
    let newg = UGraph.merge_constraints univ_csts newg in
    let () =
      if not (Univ.UnivConstraints.is_empty univ_csts) then
        let restricted = restrict_subgraph levels univ_csts in
        (if not (UGraph.check_constraints restricted g) then
           CErrors.anomaly Pp.(str "Local constraints imply new transitive constraints."))
    in
    newg
  in
  map_universes add_subgraph env

let push_subgraph us env = NewProfile.profile "push_subgraph" (fun () -> push_subgraph us env) ()

(* It's convenient to use [{flags with foo = bar}] so we're smart wrt to it. *)
let same_flags {
     check_guarded;
     check_positive;
     check_universes;
     check_eliminations;
     conv_oracle;
     indices_matter;
     share_reduction;
     unfold_dep_heuristic;
     enable_VM;
     enable_native_compiler;
     impredicative_set;
     sprop_allowed;
     allow_uip;
  } alt =
  check_guarded == alt.check_guarded &&
  check_positive == alt.check_positive &&
  check_universes == alt.check_universes &&
  check_eliminations == alt.check_eliminations &&
  conv_oracle == alt.conv_oracle &&
  indices_matter == alt.indices_matter &&
  share_reduction == alt.share_reduction &&
  unfold_dep_heuristic == alt.unfold_dep_heuristic &&
  enable_VM == alt.enable_VM &&
  enable_native_compiler == alt.enable_native_compiler &&
  impredicative_set == alt.impredicative_set &&
  sprop_allowed == alt.sprop_allowed &&
  allow_uip == alt.allow_uip
[@warning "+9"]

let check_flags c =
  assert (Coq_config.bytecode_compiler || not c.enable_VM);
  assert (match Coq_config.native_compiler with
      | NativeOff -> not c.enable_native_compiler
      | NativeOn _ -> true)

let set_type_in_type b = map_universes (UGraph.set_type_in_type b)

let set_typing_flags c env =
  if same_flags env.env_typing_flags c then env
  else
    let () = check_flags c in
    let env = { env with env_typing_flags = c } in
    let env = set_type_in_type (not c.check_universes) env in
    let env = { env with env_qualities = QGraph.set_ignore_constraints (not c.check_eliminations) env.env_qualities } in
    env

let update_typing_flags ?typing_flags env =
  Option.cata (fun flags -> set_typing_flags flags env) env typing_flags

let set_impredicative_set b env =
  set_typing_flags {env.env_typing_flags with impredicative_set=b} env

let set_type_in_type b env =
  set_typing_flags {env.env_typing_flags with check_universes=not b} env

let set_allow_sprop b env =
  set_typing_flags {env.env_typing_flags with sprop_allowed=b} env

let sprop_allowed env = env.env_typing_flags.sprop_allowed

let allow_rewrite_rules env =
  (* We need to be safe with reduction machines *)
  let flags = typing_flags env in
  let env = set_typing_flags
    { flags with
      enable_VM = false;
      enable_native_compiler = false }
    env
  in
  { env with rewrite_rules_allowed = true }

let rewrite_rules_allowed env = env.rewrite_rules_allowed

(* Global constants *)

let no_link_info = NotLinked

let add_constant_key kn cb linkinfo env =
  let new_constants =
    Cmap_env.add kn (cb,(ref linkinfo, ref None), Constant.canonical kn) env.env_constants in
  let irr_constants = if cb.const_relevance != Sorts.Relevant
    then Cmap_env.add kn cb.const_relevance env.irr_constants
    else env.irr_constants
  in
  let constant_hyps = record_global_hyps Cmap_env.add kn cb.const_hyps env.constant_hyps in
  let symb_pats =
    match cb.const_body with
    | Symbol _ ->
      if not env.rewrite_rules_allowed then raise (RewriteRulesNotAllowed Symb);
      Cmap_env.add kn [] env.symb_pats
    | _ -> env.symb_pats
  in
  let constant_deps =
    (* when replacing a previous constant, invalidate the cache *)
    if Cmap_env.mem kn env.env_constants then DepCache.empty
    else match CEphemeron.get env.constant_deps with
    | cache -> cache
    | exception CEphemeron.InvalidKey -> DepCache.empty
  in
  let constant_deps = CEphemeron.create @@ DepCache.fresh constant_deps in
  { env with constant_hyps; irr_constants; symb_pats; env_constants = new_constants; constant_deps }

let add_constant kn cb env =
  add_constant_key kn cb no_link_info env

(* constant_type gives the type of a constant *)
let constant_type env (kn,u) =
  let cb = lookup_constant kn env in
  let uctx = Declareops.constant_polymorphic_context cb in
  let csts = UVars.AbstractContext.instantiate u uctx in
  (subst_instance_constr u cb.const_type, csts)

type const_evaluation_result =
  | NoBody
  | Opaque
  | IsPrimitive of UVars.Instance.t * CPrimitives.t
  | HasRules of UVars.Instance.t * bool * machine_rewrite_rule list

exception NotEvaluableConst of const_evaluation_result

let constant_value_and_type env (kn, u) =
  let cb = lookup_constant kn env in
  let uctx = Declareops.constant_polymorphic_context cb in
  let cst = UVars.AbstractContext.instantiate u uctx in
  let b' = match cb.const_body with
    | Def l_body -> Some (subst_instance_constr u l_body)
    | OpaqueDef _ -> None
    | Undef _ | Primitive _ | Symbol _ -> None
  in
  b', subst_instance_constr u cb.const_type, cst

(* These functions should be called under the invariant that [env]
   already contains the constraints corresponding to the constant
   application. *)

(* constant_type gives the type of a constant *)
let constant_type_in env (kn,u) =
  let cb = lookup_constant kn env in
  subst_instance_constr u cb.const_type

let constant_value_in env (kn,u) =
  let cb = lookup_constant kn env in
  match cb.const_body with
    | Def l_body ->
      subst_instance_constr u l_body
    | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
    | Undef _ -> raise (NotEvaluableConst NoBody)
    | Primitive p -> raise (NotEvaluableConst (IsPrimitive (u,p)))
    | Symbol b ->
        match Cmap_env.find_opt kn env.symb_pats with
        | Some r -> raise (NotEvaluableConst (HasRules (u, b, r)))
        | None -> assert false

let constant_opt_value_in env cst =
  try Some (constant_value_in env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant kn env =
  let cb = lookup_constant kn env in
    match cb.const_body with
    | Def _ -> true
    | OpaqueDef _ -> false
    | Undef _ | Primitive _ | Symbol _ -> false

let constant_relevance kn env = match Cmap_env.find_opt kn env.irr_constants with
| None -> Sorts.Relevant
| Some r -> r

let is_primitive env c =
  let cb = lookup_constant c env in
  match cb.Declarations.const_body with
  | Declarations.Primitive _ -> true
  | _ -> false

let is_symbol env c =
  let cb = lookup_constant c env in
  match cb.Declarations.const_body with
  | Declarations.Symbol _ -> true
  | _ -> false

let get_primitive env c =
  let cb = lookup_constant c env in
  match cb.Declarations.const_body with
  | Declarations.Primitive p -> Some p
  | _ -> None

let is_int63_type env c =
  match env.retroknowledge.Retroknowledge.retro_int63 with
  | None -> false
  | Some c' -> Constant.CanOrd.equal c c'

let is_float64_type env c =
  match env.retroknowledge.Retroknowledge.retro_float64 with
  | None -> false
  | Some c' -> Constant.CanOrd.equal c c'

let is_string_type env c =
  match env.retroknowledge.Retroknowledge.retro_string with
  | None -> false
  | Some c' -> Constant.CanOrd.equal c c'

let is_array_type env c =
  match env.retroknowledge.Retroknowledge.retro_array with
  | None -> false
  | Some c' -> Constant.CanOrd.equal c c'

let is_primitive_type env c =
  (* dummy match to force an update if we add a primitive type *)
  let _ =
    function
    | CPrimitives.(PTE(PT_int63))
    | CPrimitives.(PTE(PT_float64))
    | CPrimitives.(PTE(PT_string))
    | CPrimitives.(PTE(PT_array)) -> ()
  in
  is_int63_type env c || is_float64_type env c || is_array_type env c ||
  is_string_type env c

let polymorphic_constant cst env =
  Declareops.constant_is_polymorphic (lookup_constant cst env)

let polymorphic_pconstant (cst,u) env =
  if UVars.Instance.is_empty u then false
  else polymorphic_constant cst env

let type_in_type_constant cst env =
  not (lookup_constant cst env).const_typing_flags.check_universes

let lookup_projection p env =
  let mind,i = Projection.inductive p in
  let mib = lookup_mind mind env in
  (if not (Int.equal mib.mind_nparams (Projection.npars p))
   then anomaly ~label:"lookup_projection" Pp.(str "Bad number of parameters on projection."));
  match mib.mind_packets.(i).mind_record with
  | NotRecord | FakeRecord -> anomaly ~label:"lookup_projection" Pp.(str "not a projection")
  | PrimRecord { relevances; tys; _ } ->
    let arg = Projection.arg p in
    relevances.(arg), tys.(arg)

let projection_repr_label env p =
  let mind, i = Projection.Repr.inductive p in
  let mib = lookup_mind mind env in
  match mib.mind_packets.(i).mind_record with
  | NotRecord | FakeRecord -> anomaly ~label:"lookup_projection" Pp.(str "not a projection")
  | PrimRecord { projections; _ } -> projections.(Projection.Repr.arg p)

let projection_repr_constant env p =
  let mind, _ = Projection.Repr.inductive p in
  let knu = MutInd.user mind in
  let knc = MutInd.canonical mind in
  let label = projection_repr_label env p in
  let cst = Constant.make knu knc in
  Constant.change_label cst label

let get_projection env ind ~proj_arg =
  let mib = lookup_mind (fst ind) env in
  Declareops.inductive_make_projection ind mib ~proj_arg

let get_projections env ind =
  let mib = lookup_mind (fst ind) env in
  Declareops.inductive_make_projections ind mib

(* Mutual Inductives *)
let polymorphic_ind (mind,_i) env =
  Declareops.inductive_is_polymorphic (lookup_mind mind env)

let polymorphic_pind (ind,u) env =
  if UVars.Instance.is_empty u then false
  else polymorphic_ind ind env

let type_in_type_ind (mind,_i) env =
  not (lookup_mind mind env).mind_typing_flags.check_universes

let template_polymorphic_ind (mind,_) env =
  match (lookup_mind mind env).mind_template with
  | Some _ -> true
  | None -> false

let template_polymorphic_pind (ind,u) env =
  if not (UVars.Instance.is_empty u) then false
  else template_polymorphic_ind ind env

let add_mind_key kn mind link env =
  let mind_key = (mind, ref link, MutInd.canonical kn) in
  let new_inds = Mindmap_env.add kn mind_key env.env_inductives in
  let irr_inds = Array.fold_left_i (fun i irr_inds mip ->
      if mip.mind_relevance != Sorts.Relevant
      then Indmap_env.add (kn, i) mip.mind_relevance irr_inds
      else irr_inds) env.irr_inds mind.mind_packets
  in
  let inductive_hyps = record_global_hyps Mindmap_env.add kn mind.mind_hyps env.inductive_hyps in
  { env with inductive_hyps; irr_inds; env_inductives = new_inds }

let add_mind kn mib env =
  let li = no_link_info in add_mind_key kn mib li env

(* Lookup of section variables *)

let lookup_constant_variables c env =
  Option.default Id.Set.empty (Cmap_env.find_opt c env.constant_hyps)

let lookup_inductive_variables (kn,_i) env =
  Option.default Id.Set.empty (Mindmap_env.find_opt kn env.inductive_hyps)

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Universes *)
let constant_context env c =
  let cb = lookup_constant c env in
  Declareops.constant_polymorphic_context cb

let universes_of_global env r =
  let open GlobRef in
    match r with
    | VarRef _ -> UVars.AbstractContext.empty
    | ConstRef c -> constant_context env c
    | IndRef (mind,_) | ConstructRef ((mind,_),_) ->
      let mib = lookup_mind mind env in
      Declareops.inductive_polymorphic_context mib

(* Returns the list of global variables in a term *)

let vars_of_global env gr =
  let open GlobRef in
  match gr with
  | VarRef id -> Id.Set.singleton id
  | ConstRef kn -> lookup_constant_variables kn env
  | IndRef ind -> lookup_inductive_variables ind env
  | ConstructRef cstr -> lookup_constructor_variables cstr env

let global_vars_set env constr =
  let rec filtrec acc c =
    match destRef c with
    | gr, _ ->
      Id.Set.union (vars_of_global env gr) acc
    | exception DestKO -> Constr.fold filtrec acc c
  in
  filtrec Id.Set.empty constr


(* [keep_hyps env ids] keeps the part of the section context of [env] which
   contains the variables of the set [ids], and recursively the variables
   contained in the types of the needed variables. *)

let really_needed env needed =
  let open! Context.Named.Declaration in
  Context.Named.fold_inside
    (fun need decl ->
      if Id.Set.mem (get_id decl) need then
        let globc =
          match decl with
            | LocalAssum _ -> Id.Set.empty
            | LocalDef (_,c,_) -> global_vars_set env c in
        Id.Set.union
          (global_vars_set env (get_type decl))
          (Id.Set.union globc need)
      else need)
    ~init:needed
    (named_context env)

let keep_hyps env needed =
  let open Context.Named.Declaration in
  let really_needed = really_needed env needed in
  Context.Named.fold_outside
    (fun d nsign ->
      if Id.Set.mem (get_id d) really_needed then Context.Named.add d nsign
      else nsign)
    (named_context env)
    ~init:empty_named_context

(* Modules *)

let add_modtype mp mtb env =
  let new_modtypes = ModPath.Map.add mp mtb env.env_modtypes in
  { env with env_modtypes = new_modtypes }

let shallow_add_module mp mb env =
  let () = assert (not @@ ModPath.Map.mem mp env.env_modules) in
  let new_mods = ModPath.Map.add mp mb env.env_modules in
  { env with env_modules = new_mods }

let lookup_module mp env =
    ModPath.Map.find mp env.env_modules


let lookup_modtype mp env =
  ModPath.Map.find mp env.env_modtypes

(*s Judgments. *)

type ('constr, 'types) punsafe_judgment = {
  uj_val : 'constr;
  uj_type : 'types }

let on_judgment f j = { uj_val = f j.uj_val; uj_type = f j.uj_type }
let on_judgment_value f j = { j with uj_val = f j.uj_val }
let on_judgment_type f j = { j with uj_type = f j.uj_type }

type unsafe_judgment = (constr, types) punsafe_judgment

let make_judge v tj =
  { uj_val = v;
    uj_type = tj }

let j_val j = j.uj_val
let j_type j = j.uj_type

type ('types, 'sorts) punsafe_type_judgment = {
  utj_val : 'types;
  utj_type : 'sorts }

type unsafe_type_judgment = (types, Sorts.t) punsafe_type_judgment

exception Hyp_not_found

let apply_to_hyp ctxt id f =
  let open Context.Named.Declaration in
  let rec aux rtail ctxt =
    match match_named_context_val ctxt with
    | Some (status, d, ctxt) ->
      if Id.equal (get_id d) id then
        let status, d' = f ctxt.env_named_ctx status d rtail in
        push_named_context_val status d' ctxt
      else
        let ctxt' = aux (d::rtail) ctxt in
        push_named_context_val status d ctxt'
    | None -> raise Hyp_not_found
  in aux [] ctxt

(* To be used in Logic.clear_hyps *)
let remove_hyps ids check_context ctxt =
  let rec remove_hyps ids ctxt =
    if Id.Set.is_empty ids then ctxt, false
    else match match_named_context_val ctxt with
    | None -> empty_named_context_val, false
    | Some (status, d, rctxt) ->
      let id0 = Context.Named.Declaration.get_id d in
      let removed = Id.Set.mem id0 ids in
      let ids = if removed then Id.Set.remove id0 ids else ids in
      let (ans, seen) = remove_hyps ids rctxt in
      if removed then (ans, true)
      else if not seen then ctxt, false
      else
        let rctxt' = ans in
        let status', d' = check_context status d in
        if status == status' && d == d' && rctxt == rctxt' then
          ctxt, true
        else push_named_context_val status' d' rctxt', true
  in
  fst (remove_hyps ids ctxt)

(* A general request *)

let is_polymorphic env r =
  let open Names.GlobRef in
  match r with
  | VarRef _id -> false
  | ConstRef c -> polymorphic_constant c env
  | IndRef ind -> polymorphic_ind ind env
  | ConstructRef cstr -> polymorphic_ind (inductive_of_constructor cstr) env

let is_template_polymorphic env r =
  let open Names.GlobRef in
  match r with
  | VarRef _id -> false
  | ConstRef _c -> false
  | IndRef ind -> template_polymorphic_ind ind env
  | ConstructRef cstr -> template_polymorphic_ind (inductive_of_constructor cstr) env

let is_type_in_type env r =
  let open Names.GlobRef in
  match r with
  | VarRef _id -> false
  | ConstRef c -> type_in_type_constant c env
  | IndRef ind -> type_in_type_ind ind env
  | ConstructRef cstr -> type_in_type_ind (inductive_of_constructor cstr) env

let ind_ignores_elim_constraints env (mind, _) =
  not (lookup_mind mind env).mind_typing_flags.check_eliminations

let vm_library env = env.vm_library

let set_vm_library lib env =
  { env with vm_library = lib }

let link_vm_library lib env =
  let vm_library = Vmlibrary.link lib env.vm_library in
  { env with vm_library }

let lookup_vm_code idx env =
  Vmlibrary.resolve idx env.vm_library

let set_retroknowledge env r = { env with retroknowledge = r }
let retroknowledge env = env.retroknowledge

module type QS =
sig
  type t
  val canonize : env -> t -> t
end

module type QMapS =
sig
  type key
  type (+'a) t
  val empty: 'a t
  val is_empty: 'a t -> bool
  val mem: env -> key -> 'a t -> bool
  val add: env -> key -> 'a -> 'a t -> 'a t
  val remove: env -> key -> 'a t -> 'a t
  val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val merge: (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
  val find: env -> key -> 'a t -> 'a
  val find_opt : env -> key -> 'a t -> 'a option
end

module QMap (M : CSig.UMapS) (Q : QS with type t = M.key) : QMapS with type key = M.key =
struct
  type key = M.key
  type 'a t = 'a M.t
  let empty = M.empty
  let is_empty = M.is_empty
  let mem env key m = M.mem (Q.canonize env key) m
  let add env key v m = M.add (Q.canonize env key) v m
  let remove env key m = M.remove (Q.canonize env key) m
  let fold = M.fold
  let merge = M.merge
  let find env key m = M.find (Q.canonize env key) m
  let find_opt env key m = M.find_opt (Q.canonize env key) m
end

module type QNameS =
sig
  type t
  val equal : env -> t -> t -> bool
  val compare : env -> t -> t -> int
  val hash : env -> t -> int
  val canonize : env -> t -> t
end

module type QCanonS = sig
  type t
  val canonize : env -> t -> t
  val fast_eq : t -> t -> bool

  module UserOrd : sig
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
  end

  (* Requirement: [UserOrd.equal (canonize e x) (canonize e y) = true] implies [fast_eq x y = true] *)

end

module QCanon (X : QCanonS) = struct
  module Self = struct
    type t = X.t
    include X.UserOrd
    let canonize = X.canonize
  end
  include Self
  let equal env c1 c2 = X.fast_eq c1 c2 && X.UserOrd.equal (X.canonize env c1) (X.canonize env c2)
  let compare env c1 c2 = X.UserOrd.compare (X.canonize env c1) (X.canonize env c2)
  let hash env c = X.UserOrd.hash (X.canonize env c)
  module UserMap = HMap.Make(Self)
  module Map = QMap(UserMap)(Self)
end

let lookup_can_constant cst env = match Cmap_env.find_opt cst env.env_constants with
| None -> Constant.user cst (* fallback for robustness *)
| Some (_, _, kn) -> kn

let lookup_can_mind mind env = match Mindmap_env.find_opt mind env.env_inductives with
| None -> MutInd.user mind (* fallback for robustness *)
| Some (_, _, kn) -> kn

module CanConstant =
struct
  include Constant
  let canonize env cst =
    Constant.make1 (lookup_can_constant cst env)
  let fast_eq c1 c2 =
    Id.equal (Constant.label c1) (Constant.label c2)
end

module CanMutInd =
struct
  include MutInd
  let canonize env mind =
    MutInd.make1 (lookup_can_mind mind env)
  let fast_eq m1 m2 =
    Id.equal (MutInd.label m1) (MutInd.label m2)
end

module CanInd =
struct
  include Ind
  let canonize env (mind, i) =
    (CanMutInd.canonize env mind, i)
  let fast_eq (m1, i1) (m2, i2) =
    CanMutInd.fast_eq m1 m2 && Int.equal i1 i2
end

module CanConstruct =
struct
  include Construct
  let canonize env (ind, i) =
    (CanInd.canonize env ind, i)
  let fast_eq (ind1, i1) (ind2, i2) =
    CanInd.fast_eq ind1 ind2 && Int.equal i1 i2
end

module CanProjectionRepr =
struct
  include Projection.Repr
  let canonize env p =
    make (CanInd.canonize env (inductive p)) ~proj_npars:(npars p) ~proj_arg:(arg p) (label p)
  let fast_eq p1 p2 =
    CanInd.fast_eq (inductive p1) (inductive p2)
end

module CanProjection =
struct
  include Projection
  let canonize env p =
    Projection.make (CanProjectionRepr.canonize env (Projection.repr p)) (Projection.unfolded p)
  let fast_eq p1 p2 =
    CanProjectionRepr.fast_eq (Projection.repr p1) (Projection.repr p2) && Projection.unfolded p1 == (Projection.unfolded p2 : bool)
end

module CanGlobRef =
struct
  include GlobRef
  let canonize env gr = match gr with
  | VarRef _ -> gr
  | ConstRef cst -> ConstRef (CanConstant.canonize env cst)
  | IndRef ind -> IndRef (CanInd.canonize env ind)
  | ConstructRef cstr -> ConstructRef (CanConstruct.canonize env cstr)
  let fast_eq gr1 gr2 = match gr1, gr2 with
  | VarRef _, VarRef _ -> true
  | ConstRef c1, ConstRef c2 -> CanConstant.fast_eq c1 c2
  | IndRef i1, IndRef i2 -> CanInd.fast_eq i1 i2
  | ConstructRef c1, ConstructRef c2 -> CanConstruct.fast_eq c1 c2
  | (VarRef _ | ConstRef _ | IndRef _ | ConstructRef _), _ -> false
end

module QConstant = QCanon(CanConstant)

module QMutInd = QCanon(CanMutInd)

module QInd = QCanon(CanInd)

module QConstruct = QCanon(CanConstruct)

module QProjection =
struct
  include QCanon(CanProjection)
  module Repr = QCanon(CanProjectionRepr)
end

module QGlobRef = QCanon(CanGlobRef)

let rec constant_dependencies_with_cache env cache kn =
  match DepCache.get kn cache with
  | Inl deps -> deps
  | Inr set ->
    match Cmap_env.find_opt kn env.env_constants with
    | None -> Cset_env.empty
    | Some (body, _, _) ->
      let deps = match body.const_body with
      | Def c ->
        let rec compute_dependencies accu c = match kind c with
        | Const (kn, _) ->
          Cset_env.fold Cset_env.add (constant_dependencies_with_cache env cache kn) (Cset_env.add kn accu)
        | _ -> Constr.fold compute_dependencies accu c
        in
        compute_dependencies Cset_env.empty c
      | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> Cset_env.empty
      in
      let () = set deps in
      deps

let constant_dependencies env kn =
  let cache =
    try CEphemeron.get env.constant_deps
    with CEphemeron.InvalidKey -> DepCache.empty
  in
  constant_dependencies_with_cache env cache kn

let constant_depends_on env cst1 cst2 =
  Cset_env.mem cst2 (constant_dependencies env cst1)

module Internal = struct
  let push_template_context uctx env =
    let () = check_ucontext uctx env in
    let env = push_context ~strict:false uctx env in
    let (qvars, _), _ = UVars.UContext.to_context_set uctx in
    let env = map_universes (UGraph.Internal.add_template_qvars qvars) env in
    env

  let is_above_prop env = UGraph.Internal.is_above_prop (universes env)

  module View =
  struct
    type t = {
      env_constants : constant_body Cmap_env.t;
      env_inductives : mutual_inductive_body Mindmap_env.t;
      env_modules : module_body ModPath.Map.t;
      env_modtypes : module_type_body ModPath.Map.t;
      env_named_context : named_context;
      env_rel_context   : rel_context;
      env_universes : UGraph.t;
      env_qualities : Sorts.Quality.Set.t;
      env_symb_pats : machine_rewrite_rule list Cmap_env.t;
      env_typing_flags  : typing_flags;
    }

    let view (env : env) = {
      env_constants = Cmap_env.map (fun (cb, _, _) -> cb) env.env_constants;
      env_inductives = Mindmap_env.map (fun (mib, _, _) -> mib) env.env_inductives;
      env_modtypes = env.env_modtypes;
      env_modules = env.env_modules;
      env_named_context = env.env_named_context.env_named_ctx;
      env_rel_context = env.env_rel_context.env_rel_ctx;
      env_universes = env.env_universes;
      env_qualities = QGraph.domain env.env_qualities;
      env_symb_pats = env.symb_pats;
      env_typing_flags = env.env_typing_flags;
    } [@@ocaml.warning "-42"]
    (* It does not matter that this is linear in the size of the environment
       since we only use for serialization purposes, which is already linear. *)

  end

  let shallow_overwrite_module mp mb env =
    let new_mods = ModPath.Map.add mp mb env.env_modules in
    { env with env_modules = new_mods }

  let rec overwrite_structure : type a. _ -> _ -> a Mod_subst.delta_resolver -> _ -> _ =
    fun mp sign resolver env ->
    let add_field env (l,elem) = match elem with
      | SFBconst cb ->
        let c = Mod_subst.constant_of_delta_kn resolver (KerName.make mp l) in
        add_constant c cb env
      | SFBmind mib ->
        let mind = Mod_subst.mind_of_delta_kn resolver (KerName.make mp l) in
        add_mind mind mib env
      | SFBmodule mb -> overwrite_module (MPdot (mp, l)) mb env
      | SFBmodtype mtb -> add_modtype (MPdot (mp, l)) mtb env
      | SFBrules r -> add_rewrite_rules r.rewrules_rules env
    in
    List.fold_left add_field env sign

  and overwrite_module mp mb env =
    let env = shallow_overwrite_module mp mb env in
    match mod_type mb with
    | NoFunctor struc ->
      let delta = Option.get (Mod_declarations.mod_global_delta mb) in
      overwrite_structure mp struc delta env
    | MoreFunctor _ -> env

  let overwrite_module_parameter mbid mtb env =
    overwrite_module (MPbound mbid) (module_body_of_type mtb) env

end
