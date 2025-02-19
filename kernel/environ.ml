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

type constant_key = constant_body * (link_info ref * key)

type mind_key = mutual_inductive_body * link_info ref

type named_context_val = {
  env_named_ctx : Constr.named_context;
  env_named_map : Constr.named_declaration Id.Map.t;
  env_named_idx : Constr.named_declaration Range.t;
}

type rel_context_val = {
  env_rel_ctx : Constr.rel_context;
  env_rel_map : Constr.rel_declaration Range.t;
}

type env = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mind_key Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t;
  env_named_context : named_context_val; (* section variables *)
  env_rel_context   : rel_context_val;
  env_universes : UGraph.t;
  env_qualities : Sorts.QVar.Set.t;
  symb_pats : rewrite_rule list Cmap_env.t;
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
}

type rewrule_not_allowed = Symb | Rule
exception RewriteRulesNotAllowed of rewrule_not_allowed

let empty_named_context_val = {
  env_named_ctx = [];
  env_named_map = Id.Map.empty;
  env_named_idx = Range.empty;
}

let empty_rel_context_val = {
  env_rel_ctx = [];
  env_rel_map = Range.empty;
}

let empty_env = {
  env_constants = Cmap_env.empty;
  env_inductives = Mindmap_env.empty;
  env_modules = MPmap.empty;
  env_modtypes = MPmap.empty;
  constant_hyps = Cmap_env.empty;
  inductive_hyps = Mindmap_env.empty;
  env_named_context = empty_named_context_val;
  env_rel_context = empty_rel_context_val;
  env_nb_rel = 0;
  env_universes = UGraph.initial_universes;
  env_qualities = Sorts.QVar.Set.empty;
  irr_constants = Cmap_env.empty;
  irr_inds = Indmap_env.empty;
  symb_pats = Cmap_env.empty;
  env_typing_flags = Declareops.safe_flags Conv_oracle.empty;
  vm_library = Vmlibrary.empty;
  retroknowledge = Retroknowledge.empty;
  rewrite_rules_allowed = false;
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

let push_named_context_val d ctxt =
(*   assert (not (Id.Map.mem (NamedDecl.get_id d) ctxt.env_named_map)); *)
  {
    env_named_ctx = Context.Named.add d ctxt.env_named_ctx;
    env_named_map = Id.Map.add (NamedDecl.get_id d) d ctxt.env_named_map;
    env_named_idx = Range.cons d ctxt.env_named_idx;
  }

let match_named_context_val c = match c.env_named_ctx with
| [] -> None
| decl :: ctx ->
  let map = Id.Map.remove (NamedDecl.get_id decl) c.env_named_map in
  let cval = { env_named_ctx = ctx; env_named_map = map; env_named_idx = Range.tl c.env_named_idx } in
  Some (decl, cval)

let map_named_val f ctxt =
  let open Context.Named.Declaration in
  let fold accu d =
    let d' = f d in
    let accu =
      if d == d' then accu
      else Id.Map.set (get_id d) d' accu
    in
    (accu, d')
  in
  let map, ctx = List.Smart.fold_left_map fold ctxt.env_named_map ctxt.env_named_ctx in
  if map == ctxt.env_named_map then ctxt
  else
    let idx = List.fold_right Range.cons ctx Range.empty in
    { env_named_ctx = ctx; env_named_map = map; env_named_idx = idx }

let push_named d env =
  {env with env_named_context = push_named_context_val d env.env_named_context}

let lookup_named id env =
  Id.Map.find id env.env_named_context.env_named_map

let lookup_named_ctxt id ctxt =
  Id.Map.find id ctxt.env_named_map

let record_global_hyps add kn hyps acc =
  if CList.is_empty hyps then acc
  else add kn (Context.Named.to_vars hyps) acc

let fold_constants f env acc =
  Cmap_env.fold (fun c (body,_) acc -> f c body acc) env.env_constants acc

let fold_inductives f env acc =
  Mindmap_env.fold (fun c (body,_) acc -> f c body acc) env.env_inductives acc

(* Global constants *)

let lookup_constant_key kn env =
  match Cmap_env.find_opt kn env.env_constants with
  | Some v -> v
  | None ->
    anomaly Pp.(str "Constant " ++ Constant.print kn ++ str" does not appear in the environment.")

let lookup_constant kn env =
  fst (lookup_constant_key kn env)

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
let lookup_mind_key kn env =
  match Mindmap_env.find_opt kn env.env_inductives with
  | Some v -> v
  | None ->
    anomaly Pp.(str "Inductive " ++ MutInd.print kn ++ str" does not appear in the environment.")

let lookup_mind kn env =
  fst (lookup_mind_key kn env)

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
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let params = Vars.subst_of_rel_context_instance paramdecl params in
  let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
  let self =
    let u = UVars.Instance.abstract_instance (UVars.Instance.length u) in
    let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
    mkApp (mkIndU (ind, u), args)
  in
  let na = Context.make_annot Anonymous mip.mind_relevance in
  let realdecls = LocalAssum (na, self) :: realdecls in
  instantiate_context u params nas realdecls

let expand_branch_contexts (mib, mip) u params br =
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
  | Sorts.Type _ | Sorts.QSort _ -> false

let is_impredicative_family env = function
  | Sorts.InSProp | Sorts.InProp -> true
  | Sorts.InSet -> is_impredicative_set env
  | Sorts.InType | Sorts.InQSort -> false

let type_in_type env = not (typing_flags env).check_universes
let deactivated_guard env = not (typing_flags env).check_guarded

let indices_matter env = env.env_typing_flags.indices_matter

let universes env = env.env_universes

let set_universes g env =
  {env with env_universes=g}

let qualities env = env.env_qualities

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

let ids_of_named_context_val c = Id.Map.domain c.env_named_map

let empty_named_context = Context.Named.empty

let push_named_context = List.fold_right push_named

let val_of_named_context ctxt =
  List.fold_right push_named_context_val ctxt empty_named_context_val


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

let fold_named_context f env ~init =
  let rec fold_right env =
    match match_named_context_val env.env_named_context with
    | None -> init
    | Some (d, rem) ->
        let env =
          reset_with_named_context rem env in
        f env d (fold_right env)
  in fold_right env

let fold_named_context_reverse f ~init env =
  Context.Named.fold_inside f ~init:init (named_context env)


(* Universe constraints *)

let map_universes f env = set_universes (f env.env_universes) env

let add_constraints c env =
  if Univ.Constraints.is_empty c then env
  else map_universes (UGraph.merge_constraints c) env

let check_constraints c env =
  UGraph.check_constraints c env.env_universes

let add_universes ~strict ctx g =
  let _qs, us = UVars.Instance.to_array (UVars.UContext.instance ctx) in
  let g = Array.fold_left
      (fun g v -> UGraph.add_universe ~strict v g)
      g us
  in
  UGraph.merge_constraints (UVars.UContext.constraints ctx) g

let add_qualities qs known =
  let open Sorts.Quality in
  Array.fold_left (fun known q ->
      match q with
      | QVar q ->
        let known' = Sorts.QVar.Set.add q known in
        let () = if known == known' then CErrors.anomaly Pp.(str"multiply bound sort quality") in
        known'
      | QConstant _ -> CErrors.anomaly Pp.(str "constant quality in ucontext"))
    known
    qs

let push_context ?(strict=false) ctx env =
  let qs, _us = UVars.Instance.to_array (UVars.UContext.instance ctx) in
  let env = { env with env_qualities = add_qualities qs env.env_qualities } in
  map_universes (add_universes ~strict ctx) env

let add_universes_set ~strict ctx g =
  let g = Univ.Level.Set.fold
            (* Be lenient, module typing reintroduces universes and constraints due to includes *)
            (fun v g -> try UGraph.add_universe ~strict v g with UGraph.AlreadyDeclared -> g)
            (Univ.ContextSet.levels ctx) g
  in UGraph.merge_constraints (Univ.ContextSet.constraints ctx) g

let push_context_set ?(strict=false) ctx env =
  map_universes (add_universes_set ~strict ctx) env

let push_qualities ctx env =
  { env with env_qualities = Sorts.QVar.Set.union env.env_qualities ctx }

let push_subgraph (levels,csts) env =
  let add_subgraph g =
    let newg = Univ.Level.Set.fold (fun v g -> UGraph.add_universe ~strict:false v g) levels g in
    let newg = UGraph.merge_constraints csts newg in
    (if not (Univ.Constraints.is_empty csts) then
       let restricted = UGraph.constraints_for ~kept:(UGraph.domain g) newg in
       (if not (UGraph.check_constraints restricted g) then
          CErrors.anomaly Pp.(str "Local constraints imply new transitive constraints.")));
    newg
  in
  map_universes add_subgraph env

(* It's convenient to use [{flags with foo = bar}] so we're smart wrt to it. *)
let same_flags {
     check_guarded;
     check_positive;
     check_universes;
     conv_oracle;
     indices_matter;
     share_reduction;
     enable_VM;
     enable_native_compiler;
     impredicative_set;
     sprop_allowed;
     allow_uip;
  } alt =
  check_guarded == alt.check_guarded &&
  check_positive == alt.check_positive &&
  check_universes == alt.check_universes &&
  conv_oracle == alt.conv_oracle &&
  indices_matter == alt.indices_matter &&
  share_reduction == alt.share_reduction &&
  enable_VM == alt.enable_VM &&
  enable_native_compiler == alt.enable_native_compiler &&
  impredicative_set == alt.impredicative_set &&
  sprop_allowed == alt.sprop_allowed &&
  allow_uip == alt.allow_uip
[@warning "+9"]

let set_type_in_type b = map_universes (UGraph.set_type_in_type b)

let set_typing_flags c env =
  if same_flags env.env_typing_flags c then env
  else
    let env = { env with env_typing_flags = c } in
    let env = set_type_in_type (not c.check_universes) env in
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
    Cmap_env.add kn (cb,(ref linkinfo, ref None)) env.env_constants in
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
  { env with constant_hyps; irr_constants; symb_pats; env_constants = new_constants }

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
  | HasRules of UVars.Instance.t * bool * rewrite_rule list

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
  match mib.mind_record with
  | NotRecord | FakeRecord -> anomaly ~label:"lookup_projection" Pp.(str "not a projection")
  | PrimRecord infos ->
    let _,_,rs,typs = infos.(i) in
    let arg = Projection.arg p in
    rs.(arg), typs.(arg)

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

let add_mind_key kn (mind, _ as mind_key) env =
  let new_inds = Mindmap_env.add kn mind_key env.env_inductives in
  let irr_inds = Array.fold_left_i (fun i irr_inds mip ->
      if mip.mind_relevance != Sorts.Relevant
      then Indmap_env.add (kn, i) mip.mind_relevance irr_inds
      else irr_inds) env.irr_inds mind.mind_packets
  in
  let inductive_hyps = record_global_hyps Mindmap_env.add kn mind.mind_hyps env.inductive_hyps in
  { env with inductive_hyps; irr_inds; env_inductives = new_inds }

let add_mind kn mib env =
  let li = ref no_link_info in add_mind_key kn (mib, li) env

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
  let new_modtypes = MPmap.add mp mtb env.env_modtypes in
  { env with env_modtypes = new_modtypes }

let shallow_add_module mp mb env =
  let new_mods = MPmap.add mp mb env.env_modules in
  { env with env_modules = new_mods }

let lookup_module mp env =
    MPmap.find mp env.env_modules


let lookup_modtype mp env =
  MPmap.find mp env.env_modtypes

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
    | Some (d, ctxt) ->
        if Id.equal (get_id d) id then
          push_named_context_val (f ctxt.env_named_ctx d rtail) ctxt
        else
          let ctxt' = aux (d::rtail) ctxt in
          push_named_context_val d ctxt'
    | None -> raise Hyp_not_found
  in aux [] ctxt

(* To be used in Logic.clear_hyps *)
let remove_hyps ids check_context ctxt =
  let rec remove_hyps ids ctxt =
    if Id.Set.is_empty ids then ctxt, false
    else match match_named_context_val ctxt with
    | None -> empty_named_context_val, false
    | Some (d, rctxt) ->
      let id0 = Context.Named.Declaration.get_id d in
      let removed = Id.Set.mem id0 ids in
      let ids = if removed then Id.Set.remove id0 ids else ids in
      let (ans, seen) = remove_hyps ids rctxt in
      if removed then (ans, true)
      else if not seen then ctxt, false
      else
        let rctxt' = ans in
        let d' = check_context d in
        if d == d' && rctxt == rctxt' then
          ctxt, true
        else push_named_context_val d' rctxt', true
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

module type QNameS =
sig
  type t
  val equal : env -> t -> t -> bool
  val compare : env -> t -> t -> int
  val hash : env -> t -> int
  val canonize : env -> t -> t
end

module QConstant =
struct
  type t = Constant.t
  let equal _env c1 c2 = Constant.CanOrd.equal c1 c2
  let compare _env c1 c2 = Constant.CanOrd.compare c1 c2
  let hash _env c = Constant.CanOrd.hash c
  let canonize _env c = Constant.canonize c
end

module QMutInd =
struct
  type t = MutInd.t
  let equal _env c1 c2 = MutInd.CanOrd.equal c1 c2
  let compare _env c1 c2 = MutInd.CanOrd.compare c1 c2
  let hash _env c = MutInd.CanOrd.hash c
  let canonize _env c = MutInd.canonize c
end

module QInd =
struct
  type t = Ind.t
  let equal _env c1 c2 = Ind.CanOrd.equal c1 c2
  let compare _env c1 c2 = Ind.CanOrd.compare c1 c2
  let hash _env c = Ind.CanOrd.hash c
  let canonize _env c = Ind.canonize c
end

module QConstruct =
struct
  type t = Construct.t
  let equal _env c1 c2 = Construct.CanOrd.equal c1 c2
  let compare _env c1 c2 = Construct.CanOrd.compare c1 c2
  let hash _env c = Construct.CanOrd.hash c
  let canonize _env c = Construct.canonize c
end

module QProjection =
struct
  type t = Projection.t
  let equal _env c1 c2 = Projection.CanOrd.equal c1 c2
  let compare _env c1 c2 = Projection.CanOrd.compare c1 c2
  let hash _env c = Projection.CanOrd.hash c
  let canonize _env c = Projection.canonize c
  module Repr =
  struct
    type t = Projection.Repr.t
    let equal _env c1 c2 = Projection.Repr.CanOrd.equal c1 c2
    let compare _env c1 c2 = Projection.Repr.CanOrd.compare c1 c2
    let hash _env c = Projection.Repr.CanOrd.hash c
    let canonize _env c = Projection.Repr.canonize c
  end
end

module QGlobRef =
struct
  type t = GlobRef.t
  let equal _env c1 c2 = GlobRef.CanOrd.equal c1 c2
  let compare _env c1 c2 = GlobRef.CanOrd.compare c1 c2
  let hash _env c = GlobRef.CanOrd.hash c
  let canonize _env c = GlobRef.canonize c
end

module Internal = struct
  let push_template_context uctx env =
    let env = push_context ~strict:false uctx env in
    let qvars, _ = UVars.UContext.to_context_set uctx in
    let env = map_universes (UGraph.Internal.add_template_qvars qvars) env in
    env

  let is_above_prop env q = UGraph.Internal.is_above_prop env.env_universes q

  module View =
  struct
    type t = {
      env_constants : constant_key Cmap_env.t;
      env_inductives : mind_key Mindmap_env.t;
      env_modules : module_body MPmap.t;
      env_modtypes : module_type_body MPmap.t;
      env_named_context : named_context_val;
      env_rel_context   : rel_context_val;
      env_universes : UGraph.t;
      env_qualities : Sorts.QVar.Set.t;
      env_symb_pats : rewrite_rule list Cmap_env.t;
      env_typing_flags  : typing_flags;
    }

    let view (env : env) = {
      env_constants = env.env_constants;
      env_inductives = env.env_inductives;
      env_modtypes = env.env_modtypes;
      env_modules = env.env_modules;
      env_named_context = env.env_named_context;
      env_rel_context = env.env_rel_context;
      env_universes = env.env_universes;
      env_qualities = env.env_qualities;
      env_symb_pats = env.symb_pats;
      env_typing_flags = env.env_typing_flags;
    } [@@ocaml.warning "-42"]

  end

end
