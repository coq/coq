(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Mod_subst
open Util

module RelDecl = Context.Rel.Declaration

(** Operations concernings types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

let safe_flags = {
  check_guarded = true;
  check_universes = true;
}

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
  match cb.const_universes with
  | Monomorphic_const _ -> c
  | Polymorphic_const ctx -> 
     Vars.subst_instance_constr (Univ.AUContext.instance ctx) c

let constant_is_polymorphic cb =
  match cb.const_universes with
  | Monomorphic_const _ -> false
  | Polymorphic_const _ -> true

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

let constraints_of_constant otab cb =
  match cb.const_universes with
  | Polymorphic_const ctx -> 
    Univ.UContext.constraints (Univ.instantiate_univ_context ctx)
  | Monomorphic_const ctx -> 
    Univ.Constraint.union 
      (Univ.UContext.constraints ctx)
      (match cb.const_body with
       | Undef _ -> Univ.empty_constraint
       | Def c -> Univ.empty_constraint
       | OpaqueDef o ->
         Univ.ContextSet.constraints (Opaqueproof.force_constraints otab o))

let universes_of_constant otab cb = 
  match cb.const_body with
  | Undef _ | Def _ ->
    begin
      match cb.const_universes with
      | Monomorphic_const ctx -> ctx
      | Polymorphic_const ctx -> Univ.instantiate_univ_context ctx
    end
  | OpaqueDef o -> 
    let body_uctxs = Opaqueproof.force_constraints otab o in
    match cb.const_universes with
    | Monomorphic_const ctx ->
      let uctxs = Univ.ContextSet.of_context ctx in
      Univ.ContextSet.to_context (Univ.ContextSet.union body_uctxs uctxs)
    | Polymorphic_const ctx ->
      assert(Univ.ContextSet.is_empty body_uctxs);
      Univ.instantiate_univ_context ctx

let universes_of_polymorphic_constant otab cb = 
  match cb.const_universes with
  | Monomorphic_const _ -> Univ.UContext.empty
  | Polymorphic_const ctx -> Univ.instantiate_univ_context ctx

let constant_has_body cb = match cb.const_body with
  | Undef _ -> false
  | Def _ | OpaqueDef _ -> true

let constant_polymorphic_instance cb =
  match cb.const_universes with
  | Monomorphic_const _ -> Univ.Instance.empty
  | Polymorphic_const ctx -> Univ.AUContext.instance ctx

let constant_polymorphic_context cb =
  match cb.const_universes with
  | Monomorphic_const _ -> Univ.UContext.empty
  | Polymorphic_const ctx -> Univ.instantiate_univ_context ctx

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Undef _ | Def _ -> false

(** {7 Constant substitutions } *)

let subst_rel_declaration sub =
  RelDecl.map_constr (subst_mps sub)

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
          Option.map (Cemitcodes.subst_to_patch_subst sub) cb.const_body_code;
        const_universes = cb.const_universes;
        const_inline_code = cb.const_inline_code;
        const_typing_flags = cb.const_typing_flags }

(** {7 Hash-consing of constants } *)

(** This hash-consing is currently quite partial : we only
    share internal fields (e.g. constr), and not the records
    themselves. But would it really bring substantial gains ? *)

let hcons_rel_decl =
  RelDecl.map_name Names.Name.hcons %> RelDecl.map_value Term.hcons_constr %> RelDecl.map_type Term.hcons_types

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

let hcons_const_universes cbu =
  match cbu with
  | Monomorphic_const ctx -> 
    Monomorphic_const (Univ.hcons_universe_context ctx)
  | Polymorphic_const ctx -> 
    Polymorphic_const (Univ.hcons_abstract_universe_context ctx)

let hcons_const_body cb =
  { cb with
    const_body = hcons_const_def cb.const_body;
    const_type = hcons_const_type cb.const_type;
    const_universes = hcons_const_universes cb.const_universes }

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
      Context.Rel.map (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = Array.smartmap (subst_mind_packet sub) mib.mind_packets ;
    mind_universes = mib.mind_universes;
    mind_private = mib.mind_private;
    mind_typing_flags = mib.mind_typing_flags;
  }

let inductive_polymorphic_instance mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> Univ.Instance.empty
  | Polymorphic_ind ctx -> Univ.AUContext.instance ctx
  | Cumulative_ind cumi -> 
    Univ.AUContext.instance (Univ.ACumulativityInfo.univ_context cumi)

let inductive_polymorphic_context mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> Univ.UContext.empty
  | Polymorphic_ind ctx -> Univ.instantiate_univ_context ctx
  | Cumulative_ind cumi -> 
    Univ.instantiate_univ_context (Univ.ACumulativityInfo.univ_context cumi)

let inductive_is_polymorphic mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> false
  | Polymorphic_ind ctx -> true
  | Cumulative_ind cumi -> true

let inductive_is_cumulative mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> false
  | Polymorphic_ind ctx -> false
  | Cumulative_ind cumi -> true

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

let hcons_mind_universes miu =
  match miu with
  | Monomorphic_ind ctx -> Monomorphic_ind (Univ.hcons_universe_context ctx)
  | Polymorphic_ind ctx -> Polymorphic_ind (Univ.hcons_abstract_universe_context ctx)
  | Cumulative_ind cui -> Cumulative_ind (Univ.hcons_abstract_cumulativity_info cui)

let hcons_mind mib =
  { mib with
    mind_packets = Array.smartmap hcons_mind_packet mib.mind_packets;
    mind_params_ctxt = hcons_rel_context mib.mind_params_ctxt;
    mind_universes = hcons_mind_universes mib.mind_universes }

(** {6 Stm machinery } *)

let string_of_side_effect { Entries.eff } = match eff with
  | Entries.SEsubproof (c,_,_) -> "P(" ^ Names.string_of_con c ^ ")"
  | Entries.SEscheme (cl,_) ->
      "S(" ^ String.concat ", " (List.map (fun (_,c,_,_) -> Names.string_of_con c) cl) ^ ")"

(** Hashconsing of modules *)

let hcons_functorize hty he hself f = match f with
| NoFunctor e ->
  let e' = he e in
  if e == e' then f else NoFunctor e'
| MoreFunctor (mid, ty, nf) ->
  (** FIXME *)
  let mid' = mid in
  let ty' = hty ty in
  let nf' = hself nf in
  if mid == mid' && ty == ty' && nf == nf' then f
  else MoreFunctor (mid, ty', nf')

let hcons_module_alg_expr me = me

let rec hcons_structure_field_body sb = match sb with
| SFBconst cb ->
  let cb' = hcons_const_body cb in
  if cb == cb' then sb else SFBconst cb'
| SFBmind mib ->
  let mib' = hcons_mind mib in
  if mib == mib' then sb else SFBmind mib'
| SFBmodule mb ->
  let mb' = hcons_module_body mb in
  if mb == mb' then sb else SFBmodule mb'
| SFBmodtype mb ->
  let mb' = hcons_module_body mb in
  if mb == mb' then sb else SFBmodtype mb'

and hcons_structure_body sb =
  (** FIXME *)
  let map (l, sfb as fb) =
    let l' = Names.Label.hcons l in
    let sfb' = hcons_structure_field_body sfb in
    if l == l' && sfb == sfb' then fb else (l', sfb')
  in
  List.smartmap map sb

and hcons_module_signature ms =
  hcons_functorize hcons_module_body hcons_structure_body hcons_module_signature ms

and hcons_module_expression me =
  hcons_functorize hcons_module_body hcons_module_alg_expr hcons_module_expression me

and hcons_module_implementation mip = match mip with
| Abstract -> Abstract
| Algebraic me ->
  let me' = hcons_module_expression me in
  if me == me' then mip else Algebraic me'
| Struct ms ->
  let ms' = hcons_module_signature ms in
  if ms == ms' then mip else Struct ms
| FullStruct -> FullStruct

and hcons_module_body mb =
  let mp' = mb.mod_mp in
  let expr' = hcons_module_implementation mb.mod_expr in
  let type' = hcons_module_signature mb.mod_type in
  let type_alg' = mb.mod_type_alg in
  let constraints' = Univ.hcons_universe_context_set mb.mod_constraints in
  let delta' = mb.mod_delta in
  let retroknowledge' = mb.mod_retroknowledge in

  if
    mb.mod_mp == mp' &&
    mb.mod_expr == expr' &&
    mb.mod_type == type' &&
    mb.mod_type_alg == type_alg' &&
    mb.mod_constraints == constraints' &&
    mb.mod_delta == delta' &&
    mb.mod_retroknowledge == retroknowledge'
  then mb
  else {
    mod_mp = mp';
    mod_expr = expr';
    mod_type = type';
    mod_type_alg = type_alg';
    mod_constraints = constraints';
    mod_delta = delta';
    mod_retroknowledge = retroknowledge';
  }
