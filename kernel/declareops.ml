(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Mod_subst
open Util

module RelDecl = Context.Rel.Declaration

(** Operations concernings types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

let safe_flags oracle = {
  check_guarded = true;
  check_universes = true;
  conv_oracle = oracle;
  share_reduction = true;
  enable_VM = true;
  enable_native_compiler = true;
  indices_matter = true;
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
      (* List.Smart.map (Option.Smart.map Univ.hcons_univ_level) ar.template_param_levels; *)
    template_level = Univ.hcons_univ ar.template_level }

(** {6 Constants } *)

let constant_is_polymorphic cb =
  match cb.const_universes with
  | Monomorphic_const _ -> false
  | Polymorphic_const _ -> true


let constant_has_body cb = match cb.const_body with
  | Undef _ | Primitive _ -> false
  | Def _ | OpaqueDef _ -> true

let constant_polymorphic_context cb =
  match cb.const_universes with
  | Monomorphic_const _ -> Univ.AUContext.empty
  | Polymorphic_const ctx -> ctx

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Undef _ | Def _ | Primitive _ -> false

(** {7 Constant substitutions } *)

let subst_rel_declaration sub =
  RelDecl.map_constr (subst_mps sub)

let subst_rel_context sub = List.Smart.map (subst_rel_declaration sub)

let subst_const_type sub arity =
  if is_empty_subst sub then arity
  else subst_mps sub arity

(** No need here to check for physical equality after substitution,
    at least for Def due to the delayed substitution [subst_constr_subst]. *)
let subst_const_def sub def = match def with
  | Undef _ | Primitive _ -> def
  | Def c -> Def (subst_constr sub c)
  | OpaqueDef o -> OpaqueDef (Opaqueproof.subst_opaque sub o)

let subst_const_body sub cb =
  assert (List.is_empty cb.const_hyps); (* we're outside sections *)
  if is_empty_subst sub then cb
  else
    let body' = subst_const_def sub cb.const_body in
    let type' = subst_const_type sub cb.const_type in
    if body' == cb.const_body && type' == cb.const_type
    then cb
    else
      { const_hyps = [];
        const_body = body';
        const_type = type';
        const_body_code =
          Option.map (Cemitcodes.subst_to_patch_subst sub) cb.const_body_code;
        const_universes = cb.const_universes;
        const_private_poly_univs = cb.const_private_poly_univs;
        const_inline_code = cb.const_inline_code;
        const_typing_flags = cb.const_typing_flags }

(** {7 Hash-consing of constants } *)

(** This hash-consing is currently quite partial : we only
    share internal fields (e.g. constr), and not the records
    themselves. But would it really bring substantial gains ? *)

let hcons_rel_decl =
  RelDecl.map_name Names.Name.hcons %> RelDecl.map_value Constr.hcons %> RelDecl.map_type Constr.hcons

let hcons_rel_context l = List.Smart.map hcons_rel_decl l

let hcons_const_def = function
  | Undef inl -> Undef inl
  | Primitive p -> Primitive p
  | Def l_constr ->
    let constr = force_constr l_constr in
    Def (from_val (Constr.hcons constr))
  | OpaqueDef _ as x -> x (* hashconsed when turned indirect *)

let hcons_const_universes cbu =
  match cbu with
  | Monomorphic_const ctx -> 
    Monomorphic_const (Univ.hcons_universe_context_set ctx)
  | Polymorphic_const ctx ->
    Polymorphic_const (Univ.hcons_abstract_universe_context ctx)

let hcons_const_private_univs = function
  | None -> None
  | Some univs -> Some (Univ.hcons_universe_context_set univs)

let hcons_const_body cb =
  { cb with
    const_body = hcons_const_def cb.const_body;
    const_type = Constr.hcons cb.const_type;
    const_universes = hcons_const_universes cb.const_universes;
    const_private_poly_univs = hcons_const_private_univs cb.const_private_poly_univs;
  }

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

let subst_wf_paths sub p = Rtree.Smart.map (subst_recarg sub) p

(** {7 Substitution of inductive declarations } *)

let subst_regular_ind_arity sub s =
  let uar' = subst_mps sub s.mind_user_arity in
    if uar' == s.mind_user_arity then s 
    else { mind_user_arity = uar'; mind_sort = s.mind_sort }

let subst_template_ind_arity _sub s = s

(* FIXME records *)
let subst_ind_arity =
  subst_decl_arity subst_regular_ind_arity subst_template_ind_arity

let subst_mind_packet sub mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_consnrealargs = mbp.mind_consnrealargs;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.Smart.map (subst_mps sub) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context sub mbp.mind_arity_ctxt;
    mind_arity = subst_ind_arity sub mbp.mind_arity;
    mind_user_lc = Array.Smart.map (subst_mps sub) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealdecls = mbp.mind_nrealdecls;
    mind_kelim = mbp.mind_kelim;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*);
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }

let subst_mind_record sub r = match r with
| NotRecord -> NotRecord
| FakeRecord -> FakeRecord
| PrimRecord infos ->
  let map (id, ps, pb as info) =
    let pb' = Array.Smart.map (subst_mps sub) pb in
    if pb' == pb then info
    else (id, ps, pb')
  in
  let infos' = Array.Smart.map map infos in
  if infos' == infos then r else PrimRecord infos'

let subst_mind_body sub mib =
  { mind_record = subst_mind_record sub mib.mind_record ;
    mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
    mind_hyps = (match mib.mind_hyps with [] -> [] | _ -> assert false);
    mind_nparams = mib.mind_nparams;
    mind_nparams_rec = mib.mind_nparams_rec;
    mind_params_ctxt =
      Context.Rel.map (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = Array.Smart.map (subst_mind_packet sub) mib.mind_packets ;
    mind_universes = mib.mind_universes;
    mind_private = mib.mind_private;
    mind_typing_flags = mib.mind_typing_flags;
  }

let inductive_polymorphic_context mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> Univ.AUContext.empty
  | Polymorphic_ind ctx -> ctx
  | Cumulative_ind cumi -> Univ.ACumulativityInfo.univ_context cumi

let inductive_is_polymorphic mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> false
  | Polymorphic_ind _ctx -> true
  | Cumulative_ind _cumi -> true

let inductive_is_cumulative mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> false
  | Polymorphic_ind _ctx -> false
  | Cumulative_ind _cumi -> true

let inductive_make_projection ind mib ~proj_arg =
  match mib.mind_record with
  | NotRecord | FakeRecord -> None
  | PrimRecord infos ->
    Some (Names.Projection.Repr.make ind
            ~proj_npars:mib.mind_nparams
            ~proj_arg
            (pi2 infos.(snd ind)).(proj_arg))

let inductive_make_projections ind mib =
  match mib.mind_record with
  | NotRecord | FakeRecord -> None
  | PrimRecord infos ->
    let projs = Array.mapi (fun proj_arg lab ->
        Names.Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg lab)
        (pi2 infos.(snd ind))
    in
    Some projs

(** {6 Hash-consing of inductive declarations } *)

let hcons_regular_ind_arity a =
  { mind_user_arity = Constr.hcons a.mind_user_arity;
    mind_sort = Sorts.hcons a.mind_sort }

(** Just as for constants, this hash-consing is quite partial *)

let hcons_ind_arity =
  map_decl_arity hcons_regular_ind_arity hcons_template_arity

(** Substitution of inductive declarations *)

let hcons_mind_packet oib =
  let user = Array.Smart.map Constr.hcons oib.mind_user_lc in
  let nf = Array.Smart.map Constr.hcons oib.mind_nf_lc in
  (* Special optim : merge [mind_user_lc] and [mind_nf_lc] if possible *)
  let nf = if Array.equal (==) user nf then user else nf in
  { oib with
    mind_typename = Names.Id.hcons oib.mind_typename;
    mind_arity_ctxt = hcons_rel_context oib.mind_arity_ctxt;
    mind_arity = hcons_ind_arity oib.mind_arity;
    mind_consnames = Array.Smart.map Names.Id.hcons oib.mind_consnames;
    mind_user_lc = user;
    mind_nf_lc = nf }

let hcons_mind_universes miu =
  match miu with
  | Monomorphic_ind ctx -> Monomorphic_ind (Univ.hcons_universe_context_set ctx)
  | Polymorphic_ind ctx -> Polymorphic_ind (Univ.hcons_abstract_universe_context ctx)
  | Cumulative_ind cui -> Cumulative_ind (Univ.hcons_abstract_cumulativity_info cui)

let hcons_mind mib =
  { mib with
    mind_packets = Array.Smart.map hcons_mind_packet mib.mind_packets;
    mind_params_ctxt = hcons_rel_context mib.mind_params_ctxt;
    mind_universes = hcons_mind_universes mib.mind_universes }

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
  let mb' = hcons_module_type mb in
  if mb == mb' then sb else SFBmodtype mb'

and hcons_structure_body sb =
  (** FIXME *)
  let map (l, sfb as fb) =
    let l' = Names.Label.hcons l in
    let sfb' = hcons_structure_field_body sfb in
    if l == l' && sfb == sfb' then fb else (l', sfb')
  in
  List.Smart.map map sb

and hcons_module_signature ms =
  hcons_functorize hcons_module_type hcons_structure_body hcons_module_signature ms

and hcons_module_expression me =
  hcons_functorize hcons_module_type hcons_module_alg_expr hcons_module_expression me

and hcons_module_implementation mip = match mip with
| Abstract -> Abstract
| Algebraic me ->
  let me' = hcons_module_expression me in
  if me == me' then mip else Algebraic me'
| Struct ms ->
  let ms' = hcons_module_signature ms in
  if ms == ms' then mip else Struct ms
| FullStruct -> FullStruct

and hcons_generic_module_body :
  'a. ('a -> 'a) -> 'a generic_module_body -> 'a generic_module_body =
  fun hcons_impl mb ->
  let mp' = mb.mod_mp in
  let expr' = hcons_impl mb.mod_expr in
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

and hcons_module_body mb =
  hcons_generic_module_body hcons_module_implementation mb

and hcons_module_type mb =
  hcons_generic_module_body (fun () -> ()) mb
