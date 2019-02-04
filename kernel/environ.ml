(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
  | LinkedInteractive of string
  | NotLinked

type constant_key = constant_body * (link_info ref * key)

type mind_key = mutual_inductive_body * link_info ref

type globals = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mind_key Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t;
}

type stratification = {
  env_universes : UGraph.t;
  env_engagement : engagement
}

type val_kind =
    | VKvalue of (Vmvalues.values * Id.Set.t) CEphemeron.key
    | VKnone

type lazy_val = val_kind ref

let force_lazy_val vk = match !vk with
| VKnone -> None
| VKvalue v -> try Some (CEphemeron.get v) with CEphemeron.InvalidKey -> None

let dummy_lazy_val () = ref VKnone
let build_lazy_val vk key = vk := VKvalue (CEphemeron.create key)

type named_context_val = {
  env_named_ctx : Constr.named_context;
  env_named_map : (Constr.named_declaration * lazy_val) Id.Map.t;
}

type rel_context_val = {
  env_rel_ctx : Constr.rel_context;
  env_rel_map : (Constr.rel_declaration * lazy_val) Range.t;
}

type env = {
  env_globals       : globals;
  env_named_context : named_context_val; (* section variables *)
  env_rel_context   : rel_context_val;
  env_nb_rel        : int;
  env_stratification : stratification;
  env_typing_flags  : typing_flags;
  retroknowledge : Retroknowledge.retroknowledge;
  indirect_pterms : Opaqueproof.opaquetab;
}

let empty_named_context_val = {
  env_named_ctx = [];
  env_named_map = Id.Map.empty;
}

let empty_rel_context_val = {
  env_rel_ctx = [];
  env_rel_map = Range.empty;
}

let empty_env = {
  env_globals = {
    env_constants = Cmap_env.empty;
    env_inductives = Mindmap_env.empty;
    env_modules = MPmap.empty;
    env_modtypes = MPmap.empty};
  env_named_context = empty_named_context_val;
  env_rel_context = empty_rel_context_val;
  env_nb_rel = 0;
  env_stratification = {
    env_universes = UGraph.initial_universes;
    env_engagement = PredicativeSet };
  env_typing_flags = Declareops.safe_flags Conv_oracle.empty;
  retroknowledge = Retroknowledge.empty;
  indirect_pterms = Opaqueproof.empty_opaquetab }


(* Rel context *)

let push_rel_context_val d ctx = {
  env_rel_ctx = Context.Rel.add d ctx.env_rel_ctx;
  env_rel_map = Range.cons (d, ref VKnone) ctx.env_rel_map;
}

let match_rel_context_val ctx = match ctx.env_rel_ctx with
| [] -> None
| decl :: rem ->
  let (_, lval) = Range.hd ctx.env_rel_map in
  let ctx = { env_rel_ctx = rem; env_rel_map = Range.tl ctx.env_rel_map } in
  Some (decl, lval, ctx)

let push_rel d env =
    { env with
      env_rel_context = push_rel_context_val d env.env_rel_context;
      env_nb_rel = env.env_nb_rel + 1 }

let lookup_rel n env =
  try fst (Range.get env.env_rel_context.env_rel_map (n - 1))
  with Invalid_argument _ -> raise Not_found

let lookup_rel_val n env =
  try snd (Range.get env.env_rel_context.env_rel_map (n - 1))
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

(* Named context *)

let push_named_context_val_val d rval ctxt =
(*   assert (not (Id.Map.mem (NamedDecl.get_id d) ctxt.env_named_map)); *)
  {
    env_named_ctx = Context.Named.add d ctxt.env_named_ctx;
    env_named_map = Id.Map.add (NamedDecl.get_id d) (d, rval) ctxt.env_named_map;
  }

let push_named_context_val d ctxt =
  push_named_context_val_val d (ref VKnone) ctxt

let match_named_context_val c = match c.env_named_ctx with
| [] -> None
| decl :: ctx ->
  let (_, v) = Id.Map.find (NamedDecl.get_id decl) c.env_named_map in
  let map = Id.Map.remove (NamedDecl.get_id decl) c.env_named_map in
  let cval = { env_named_ctx = ctx; env_named_map = map } in
  Some (decl, v, cval)

let map_named_val f ctxt =
  let open Context.Named.Declaration in
  let fold accu d =
    let d' = map_constr f d in
    let accu =
      if d == d' then accu
      else Id.Map.modify (get_id d) (fun _ (_, v) -> (d', v)) accu
    in
    (accu, d')
  in
  let map, ctx = List.fold_left_map fold ctxt.env_named_map ctxt.env_named_ctx in
  if map == ctxt.env_named_map then ctxt
  else { env_named_ctx = ctx; env_named_map = map }

let push_named d env =
  {env with env_named_context = push_named_context_val d env.env_named_context}

let lookup_named id env =
  fst (Id.Map.find id env.env_named_context.env_named_map)

let lookup_named_val id env =
  snd(Id.Map.find id env.env_named_context.env_named_map)

let lookup_named_ctxt id ctxt =
  fst (Id.Map.find id ctxt.env_named_map)

let fold_constants f env acc =
  Cmap_env.fold (fun c (body,_) acc -> f c body acc) env.env_globals.env_constants acc

(* Global constants *)

let lookup_constant_key kn env =
  Cmap_env.find kn env.env_globals.env_constants

let lookup_constant kn env =
  fst (Cmap_env.find kn env.env_globals.env_constants)

(* Mutual Inductives *)
let lookup_mind kn env =
  fst (Mindmap_env.find kn env.env_globals.env_inductives)

let lookup_mind_key kn env =
  Mindmap_env.find kn env.env_globals.env_inductives

let oracle env = env.env_typing_flags.conv_oracle
let set_oracle env o =
  let env_typing_flags = { env.env_typing_flags with conv_oracle = o } in
  { env with env_typing_flags }

let engagement env = env.env_stratification.env_engagement
let typing_flags env = env.env_typing_flags

let is_impredicative_set env = 
  match engagement env with
  | ImpredicativeSet -> true
  | _ -> false

let is_impredicative_sort env = function
  | Sorts.Prop -> true
  | Sorts.Set -> is_impredicative_set env
  | Sorts.Type _ -> false

let is_impredicative_univ env u = is_impredicative_sort env (Sorts.sort_of_univ u)

let type_in_type env = not (typing_flags env).check_universes
let deactivated_guard env = not (typing_flags env).check_guarded

let indices_matter env = env.env_typing_flags.indices_matter

let universes env = env.env_stratification.env_universes
let named_context env = env.env_named_context.env_named_ctx
let named_context_val env = env.env_named_context
let rel_context env = env.env_rel_context.env_rel_ctx
let opaque_tables env = env.indirect_pterms
let set_opaque_tables env indirect_pterms = { env with indirect_pterms }

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
    | Some (rd, _, rc) ->
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
   c1 == c2 || Context.Named.equal Constr.equal (named_context_of_val c1) (named_context_of_val c2)

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
    | Some (_, _, ctx) -> skip (pred n) ctx
  in
  let ctxt = env.env_rel_context in
  { env with
    env_rel_context = skip n ctxt;
    env_nb_rel = env.env_nb_rel - n }

let fold_named_context f env ~init =
  let rec fold_right env =
    match match_named_context_val env.env_named_context with
    | None -> init
    | Some (d, _v, rem) ->
	let env =
	  reset_with_named_context rem env in
	f env d (fold_right env)
  in fold_right env

let fold_named_context_reverse f ~init env =
  Context.Named.fold_inside f ~init:init (named_context env)


(* Universe constraints *)

let map_universes f env =
  let s = env.env_stratification in
    { env with env_stratification =
	 { s with env_universes = f s.env_universes } }

let add_constraints c env =
  if Univ.Constraint.is_empty c then env
  else map_universes (UGraph.merge_constraints c) env

let check_constraints c env =
  UGraph.check_constraints c env.env_stratification.env_universes

let push_constraints_to_env (_,univs) env =
  add_constraints univs env

let add_universes strict ctx g =
  let g = Array.fold_left
            (fun g v -> UGraph.add_universe v strict g)
	    g (Univ.Instance.to_array (Univ.UContext.instance ctx))
  in
    UGraph.merge_constraints (Univ.UContext.constraints ctx) g
			   
let push_context ?(strict=false) ctx env =
  map_universes (add_universes strict ctx) env

let add_universes_set strict ctx g =
  let g = Univ.LSet.fold
            (* Be lenient, module typing reintroduces universes and constraints due to includes *)
	    (fun v g -> try UGraph.add_universe v strict g with UGraph.AlreadyDeclared -> g)
	    (Univ.ContextSet.levels ctx) g
  in UGraph.merge_constraints (Univ.ContextSet.constraints ctx) g

let push_context_set ?(strict=false) ctx env =
  map_universes (add_universes_set strict ctx) env

let push_subgraph (levels,csts) env =
  let add_subgraph g =
    let newg = Univ.LSet.fold (fun v g -> UGraph.add_universe v false g) levels g in
    let newg = UGraph.merge_constraints csts newg in
    (if not (Univ.Constraint.is_empty csts) then
       let restricted = UGraph.constraints_for ~kept:(UGraph.domain g) newg in
       (if not (UGraph.check_constraints restricted g) then
          CErrors.anomaly Pp.(str "Local constraints imply new transitive constraints.")));
    newg
  in
  map_universes add_subgraph env

let set_engagement c env = (* Unsafe *)
  { env with env_stratification =
    { env.env_stratification with env_engagement = c } }

(* It's convenient to use [{flags with foo = bar}] so we're smart wrt to it. *)
let same_flags {
     check_guarded;
     check_universes;
     conv_oracle;
     indices_matter;
     share_reduction;
     enable_VM;
     enable_native_compiler;
  } alt =
  check_guarded == alt.check_guarded &&
  check_universes == alt.check_universes &&
  conv_oracle == alt.conv_oracle &&
  indices_matter == alt.indices_matter &&
  share_reduction == alt.share_reduction &&
  enable_VM == alt.enable_VM &&
  enable_native_compiler == alt.enable_native_compiler
[@warning "+9"]

let set_typing_flags c env = (* Unsafe *)
  if same_flags env.env_typing_flags c then env
  else { env with env_typing_flags = c }

(* Global constants *)

let no_link_info = NotLinked

let add_constant_key kn cb linkinfo env =
  let new_constants =
    Cmap_env.add kn (cb,(ref linkinfo, ref None)) env.env_globals.env_constants in
  let new_globals =
    { env.env_globals with
	env_constants = new_constants } in
  { env with env_globals = new_globals }

let add_constant kn cb env =
  add_constant_key kn cb no_link_info env

(* constant_type gives the type of a constant *)
let constant_type env (kn,u) =
  let cb = lookup_constant kn env in
  let uctx = Declareops.constant_polymorphic_context cb in
  let csts = Univ.AUContext.instantiate u uctx in
  (subst_instance_constr u cb.const_type, csts)

type const_evaluation_result =
  | NoBody
  | Opaque
  | IsPrimitive of CPrimitives.t

exception NotEvaluableConst of const_evaluation_result

let constant_value_and_type env (kn, u) =
  let cb = lookup_constant kn env in
  let uctx = Declareops.constant_polymorphic_context cb in
  let cst = Univ.AUContext.instantiate u uctx in
  let b' = match cb.const_body with
    | Def l_body -> Some (subst_instance_constr u (Mod_subst.force_constr l_body))
    | OpaqueDef _ -> None
    | Undef _ | Primitive _ -> None
  in
  b', subst_instance_constr u cb.const_type, cst

let body_of_constant_body env cb =
  let otab = opaque_tables env in
  match cb.const_body with
  | Undef _ | Primitive _ ->
     None
  | Def c ->
     Some (Mod_subst.force_constr c, Declareops.constant_polymorphic_context cb)
  | OpaqueDef o ->
     Some (Opaqueproof.force_proof otab o, Declareops.constant_polymorphic_context cb)

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
      let b = Mod_subst.force_constr l_body in
	subst_instance_constr u b
    | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
    | Undef _ -> raise (NotEvaluableConst NoBody)
    | Primitive p -> raise (NotEvaluableConst (IsPrimitive p))

let constant_opt_value_in env cst =
  try Some (constant_value_in env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant kn env =
  let cb = lookup_constant kn env in
    match cb.const_body with
    | Def _ -> true
    | OpaqueDef _ -> false
    | Undef _ | Primitive _ -> false

let is_primitive env c =
  let cb = lookup_constant c env in
  match cb.Declarations.const_body with
  | Declarations.Primitive _ -> true
  | _ -> false

let polymorphic_constant cst env =
  Declareops.constant_is_polymorphic (lookup_constant cst env)

let polymorphic_pconstant (cst,u) env =
  if Univ.Instance.is_empty u then false
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
    let _,_,typs = infos.(i) in
    typs.(Projection.arg p)

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
  if Univ.Instance.is_empty u then false
  else polymorphic_ind ind env

let type_in_type_ind (mind,_i) env =
  not (lookup_mind mind env).mind_typing_flags.check_universes

let template_polymorphic_ind (mind,i) env =
  match (lookup_mind mind env).mind_packets.(i).mind_arity with 
  | TemplateArity _ -> true
  | RegularArity _ -> false

let template_polymorphic_pind (ind,u) env =
  if not (Univ.Instance.is_empty u) then false
  else template_polymorphic_ind ind env
  
let add_mind_key kn (_mind, _ as mind_key) env =
  let new_inds = Mindmap_env.add kn mind_key env.env_globals.env_inductives in
  let new_globals =
    { env.env_globals with
        env_inductives = new_inds; } in
  { env with env_globals = new_globals }

let add_mind kn mib env =
  let li = ref no_link_info in add_mind_key kn (mib, li) env

(* Lookup of section variables *)

let lookup_constant_variables c env =
  let cmap = lookup_constant c env in
  Context.Named.to_vars cmap.const_hyps

let lookup_inductive_variables (kn,_i) env =
  let mis = lookup_mind kn env in
  Context.Named.to_vars mis.mind_hyps

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Universes *)
let constant_context env c =
  let cb = lookup_constant c env in
  Declareops.constant_polymorphic_context cb

let universes_of_global env r =
  let open GlobRef in
    match r with
    | VarRef _ -> Univ.AUContext.empty
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

let add_modtype mtb env =
  let mp = mtb.mod_mp in
  let new_modtypes = MPmap.add mp mtb env.env_globals.env_modtypes in
  let new_globals = { env.env_globals with env_modtypes = new_modtypes } in
  { env with env_globals = new_globals }

let shallow_add_module mb env =
  let mp = mb.mod_mp in
  let new_mods = MPmap.add mp mb env.env_globals.env_modules in
  let new_globals = { env.env_globals with env_modules = new_mods } in
  { env with env_globals = new_globals }

let lookup_module mp env =
    MPmap.find mp env.env_globals.env_modules


let lookup_modtype mp env = 
  MPmap.find mp env.env_globals.env_modtypes

(*s Judgments. *)

type ('constr, 'types) punsafe_judgment = {
  uj_val : 'constr;
  uj_type : 'types }

type unsafe_judgment = (constr, types) punsafe_judgment

let make_judge v tj =
  { uj_val = v;
    uj_type = tj }

let j_val j = j.uj_val
let j_type j = j.uj_type

type 'types punsafe_type_judgment = {
  utj_val : 'types;
  utj_type : Sorts.t }

type unsafe_type_judgment = types punsafe_type_judgment

exception Hyp_not_found

let apply_to_hyp ctxt id f =
  let open Context.Named.Declaration in
  let rec aux rtail ctxt =
    match match_named_context_val ctxt with
    | Some (d, v, ctxt) ->
	if Id.equal (get_id d) id then
          push_named_context_val_val (f ctxt.env_named_ctx d rtail) v ctxt
	else
	  let ctxt' = aux (d::rtail) ctxt in
	  push_named_context_val_val d v ctxt'
    | None -> raise Hyp_not_found
  in aux [] ctxt

(* To be used in Logic.clear_hyps *)
let remove_hyps ids check_context check_value ctxt =
  let rec remove_hyps ctxt = match match_named_context_val ctxt with
  | None -> empty_named_context_val, false
  | Some (d, v, rctxt) ->
     let open Context.Named.Declaration in
    let (ans, seen) = remove_hyps rctxt in
    if Id.Set.mem (get_id d) ids then (ans, true)
    else if not seen then ctxt, false
    else
      let rctxt' = ans in
      let d' = check_context d in
      let v' = check_value v in
      if d == d' && v == v' && rctxt == rctxt' then
        ctxt, true
      else push_named_context_val_val d' v' rctxt', true
  in
  fst (remove_hyps ctxt)

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

let set_retroknowledge env r = { env with retroknowledge = r }
