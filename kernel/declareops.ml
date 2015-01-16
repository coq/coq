(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Mod_subst
open Util

(** Operations concernings types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

(** {6 Arities } *)

let subst_decl_arity f g sub ar = 
  match ar with
  | RegularArity x -> 
    let x' = f sub x in 
      if x' == x then ar
      else RegularArity x'
  | TemplateArity x -> 
    let x' = g sub x in 
      if x' == x then ar
      else TemplateArity x'

let map_decl_arity f g = function
  | RegularArity a -> RegularArity (f a)
  | TemplateArity a -> TemplateArity (g a)

let hcons_template_arity ar =
  { template_param_levels = ar.template_param_levels;
      (* List.smartmap (Option.smartmap Univ.hcons_univ_level) ar.template_param_levels; *)
    template_level = Univ.hcons_univ ar.template_level }

(** {6 Constants } *)

let instantiate cb c =
  if cb.const_polymorphic then 
    Vars.subst_instance_constr (Univ.UContext.instance cb.const_universes) c
  else c

let body_of_constant otab cb = match cb.const_body with
  | Undef _ -> None
  | Def c -> Some (instantiate cb (force_constr c))
  | OpaqueDef o -> Some (instantiate cb (Opaqueproof.force_proof otab o))

let type_of_constant cb =
  match cb.const_type with
  | RegularArity t as x -> 
    let t' = instantiate cb t in
      if t' == t then x else RegularArity t'
  | TemplateArity _ as x -> x

let constraints_of_constant otab cb = Univ.Constraint.union 
  (Univ.UContext.constraints cb.const_universes)
  (match cb.const_body with
  | Undef _ -> Univ.empty_constraint
  | Def c -> Univ.empty_constraint
  | OpaqueDef o ->
      Univ.ContextSet.constraints (Opaqueproof.force_constraints otab o))

let universes_of_constant otab cb = 
  match cb.const_body with
  | Undef _ | Def _ -> cb.const_universes
  | OpaqueDef o -> 
      let body_uctxs = Opaqueproof.force_constraints otab o in
      assert(not cb.const_polymorphic || Univ.ContextSet.is_empty body_uctxs);
      let uctxs = Univ.ContextSet.of_context cb.const_universes in
      Univ.ContextSet.to_context (Univ.ContextSet.union body_uctxs uctxs) 

let universes_of_polymorphic_constant otab cb = 
  if cb.const_polymorphic then 
    let univs = universes_of_constant otab cb in
      Univ.instantiate_univ_context univs
  else Univ.UContext.empty

let constant_has_body cb = match cb.const_body with
  | Undef _ -> false
  | Def _ | OpaqueDef _ -> true

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Undef _ | Def _ -> false

(** {7 Constant substitutions } *)

let subst_rel_declaration sub (id,copt,t as x) =
  let copt' = Option.smartmap (subst_mps sub) copt in
  let t' = subst_mps sub t in
  if copt == copt' && t == t' then x else (id,copt',t')

let subst_rel_context sub = List.smartmap (subst_rel_declaration sub)

let subst_template_cst_arity sub (ctx,s as arity) =
  let ctx' = subst_rel_context sub ctx in
    if ctx==ctx' then arity else (ctx',s)
      
let subst_const_type sub arity =
  if is_empty_subst sub then arity
  else subst_mps sub arity

(** No need here to check for physical equality after substitution,
    at least for Def due to the delayed substitution [subst_constr_subst]. *)
let subst_const_def sub def = match def with
  | Undef _ -> def
  | Def c -> Def (subst_constr sub c)
  | OpaqueDef o -> OpaqueDef (Opaqueproof.subst_opaque sub o)

let subst_const_proj sub pb =
  { pb with proj_ind = subst_mind sub pb.proj_ind;
    proj_type = subst_mps sub pb.proj_type;
    proj_body = subst_const_type sub pb.proj_body }

let subst_const_body sub cb =
  assert (List.is_empty cb.const_hyps); (* we're outside sections *)
  if is_empty_subst sub then cb
  else
    let body' = subst_const_def sub cb.const_body in
    let type' = subst_decl_arity subst_const_type subst_template_cst_arity sub cb.const_type in
    let proj' = Option.smartmap (subst_const_proj sub) cb.const_proj in
    if body' == cb.const_body && type' == cb.const_type
      && proj' == cb.const_proj then cb
    else
      { const_hyps = [];
        const_body = body';
        const_type = type';
        const_proj = proj';
        const_body_code =
          Cemitcodes.subst_to_patch_subst sub cb.const_body_code;
        const_polymorphic = cb.const_polymorphic;
        const_universes = cb.const_universes;
        const_inline_code = cb.const_inline_code }

(** {7 Hash-consing of constants } *)

(** This hash-consing is currently quite partial : we only
    share internal fields (e.g. constr), and not the records
    themselves. But would it really bring substantial gains ? *)

let hcons_rel_decl ((n,oc,t) as d) =
  let n' = Names.Name.hcons n
  and oc' = Option.smartmap Term.hcons_constr oc
  and t' = Term.hcons_types t
  in if n' == n && oc' == oc && t' == t then d else (n',oc',t')

let hcons_rel_context l = List.smartmap hcons_rel_decl l

let hcons_regular_const_arity t = Term.hcons_constr t

let hcons_template_const_arity (ctx, ar) = 
  (hcons_rel_context ctx, hcons_template_arity ar)

let hcons_const_type = 
  map_decl_arity hcons_regular_const_arity hcons_template_const_arity

let hcons_const_def = function
  | Undef inl -> Undef inl
  | Def l_constr ->
    let constr = force_constr l_constr in
    Def (from_val (Term.hcons_constr constr))
  | OpaqueDef _ as x -> x (* hashconsed when turned indirect *)

let hcons_const_body cb =
  { cb with
    const_body = hcons_const_def cb.const_body;
    const_type = hcons_const_type cb.const_type;
    const_universes = Univ.hcons_universe_context cb.const_universes }

(** {6 Inductive types } *)

let eq_recarg r1 r2 = match r1, r2 with
| Norec, Norec -> true
| Mrec i1, Mrec i2 -> Names.eq_ind i1 i2
| Imbr i1, Imbr i2 -> Names.eq_ind i1 i2
| _ -> false

let subst_recarg sub r = match r with
  | Norec -> r
  | Mrec (kn,i) ->
    let kn' = subst_mind sub kn in
    if kn==kn' then r else Mrec (kn',i)
  | Imbr (kn,i) ->
    let kn' = subst_mind sub kn in
    if kn==kn' then r else Imbr (kn',i)

let mk_norec = Rtree.mk_node Norec [||]

let mk_paths r recargs =
  Rtree.mk_node r
    (Array.map (fun l -> Rtree.mk_node Norec (Array.of_list l)) recargs)

let dest_recarg p = fst (Rtree.dest_node p)

(* dest_subterms returns the sizes of each argument of each constructor of
   an inductive object of size [p]. This should never be done for Norec,
   because the number of sons does not correspond to the number of
   constructors.
 *)
let dest_subterms p =
  let (ra,cstrs) = Rtree.dest_node p in
  assert (match ra with Norec -> false | _ -> true);
  Array.map (fun t -> Array.to_list (snd (Rtree.dest_node t))) cstrs

let recarg_length p j =
  let (_,cstrs) = Rtree.dest_node p in
  Array.length (snd (Rtree.dest_node cstrs.(j-1)))

let subst_wf_paths sub p = Rtree.smartmap (subst_recarg sub) p

(** {7 Substitution of inductive declarations } *)

let subst_regular_ind_arity sub s =
  let uar' = subst_mps sub s.mind_user_arity in
    if uar' == s.mind_user_arity then s 
    else { mind_user_arity = uar'; mind_sort = s.mind_sort }

let subst_template_ind_arity sub s = s

(* FIXME records *)
let subst_ind_arity =
  subst_decl_arity subst_regular_ind_arity subst_template_ind_arity

let subst_mind_packet sub mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_consnrealargs = mbp.mind_consnrealargs;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.smartmap (subst_mps sub) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context sub mbp.mind_arity_ctxt;
    mind_arity = subst_ind_arity sub mbp.mind_arity;
    mind_user_lc = Array.smartmap (subst_mps sub) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealdecls = mbp.mind_nrealdecls;
    mind_kelim = mbp.mind_kelim;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*);
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }

let subst_mind_record sub (id, ps, pb as r) =
  let ps' = Array.smartmap (subst_constant sub) ps in
  let pb' = Array.smartmap (subst_const_proj sub) pb in
    if ps' == ps && pb' == pb then r
    else (id, ps', pb')

let subst_mind_body sub mib =
  { mind_record = Option.smartmap (Option.smartmap (subst_mind_record sub)) mib.mind_record ;
    mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
    mind_hyps = (match mib.mind_hyps with [] -> [] | _ -> assert false);
    mind_nparams = mib.mind_nparams;
    mind_nparams_rec = mib.mind_nparams_rec;
    mind_params_ctxt =
      Context.map_rel_context (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = Array.smartmap (subst_mind_packet sub) mib.mind_packets ;
    mind_polymorphic = mib.mind_polymorphic;
    mind_universes = mib.mind_universes;
    mind_private = mib.mind_private }

let inductive_instance mib =
  if mib.mind_polymorphic then
    Univ.UContext.instance mib.mind_universes
  else Univ.Instance.empty

let inductive_context mib =
  if mib.mind_polymorphic then 
    Univ.instantiate_univ_context mib.mind_universes 
  else Univ.UContext.empty

(** {6 Hash-consing of inductive declarations } *)

let hcons_regular_ind_arity a =
  { mind_user_arity = Term.hcons_constr a.mind_user_arity;
    mind_sort = Term.hcons_sorts a.mind_sort }

(** Just as for constants, this hash-consing is quite partial *)

let hcons_ind_arity =
  map_decl_arity hcons_regular_ind_arity hcons_template_arity

(** Substitution of inductive declarations *)

let hcons_mind_packet oib =
  let user = Array.smartmap Term.hcons_types oib.mind_user_lc in
  let nf = Array.smartmap Term.hcons_types oib.mind_nf_lc in
  (* Special optim : merge [mind_user_lc] and [mind_nf_lc] if possible *)
  let nf = if Array.equal (==) user nf then user else nf in
  { oib with
    mind_typename = Names.Id.hcons oib.mind_typename;
    mind_arity_ctxt = hcons_rel_context oib.mind_arity_ctxt;
    mind_arity = hcons_ind_arity oib.mind_arity;
    mind_consnames = Array.smartmap Names.Id.hcons oib.mind_consnames;
    mind_user_lc = user;
    mind_nf_lc = nf }

let hcons_mind mib =
  { mib with
    mind_packets = Array.smartmap hcons_mind_packet mib.mind_packets;
    mind_params_ctxt = hcons_rel_context mib.mind_params_ctxt;
    mind_universes = Univ.hcons_universe_context mib.mind_universes }

(** {6 Stm machinery } *)

let string_of_side_effect = function
  | SEsubproof (c,_,_) -> Names.string_of_con c
  | SEscheme (cl,_) ->
      String.concat ", " (List.map (fun (_,c,_,_) -> Names.string_of_con c) cl)
type side_effects = side_effect list
let no_seff = ([] : side_effects)
let iter_side_effects f l = List.iter f (List.rev l)
let fold_side_effects f a l = List.fold_left f a l
let uniquize_side_effects l = List.rev (CList.uniquize (List.rev l))
let union_side_effects l1 l2 = l1 @ l2
let flatten_side_effects l = List.flatten l
let side_effects_of_list l = l
let cons_side_effects x l = x :: l
let side_effects_is_empty = List.is_empty
