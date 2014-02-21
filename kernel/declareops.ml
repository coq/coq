(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Mod_subst
open Lazyconstr
open Util

(** Operations concernings types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

(** {6 Constants } *)

let body_of_constant cb = match cb.const_body with
  | Undef _ -> None
  | Def c -> Some (Lazyconstr.force c)
  | OpaqueDef lc -> Some (Lazyconstr.force_opaque lc)

let constraints_of_constant cb = Univ.union_constraints cb.const_constraints
 (match cb.const_body with
  | Undef _ -> Univ.empty_constraint
  | Def c -> Univ.empty_constraint
  | OpaqueDef lc -> snd (Lazyconstr.force_opaque_w_constraints lc))

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

let subst_const_type sub arity = match arity with
  | NonPolymorphicType s ->
    let s' = subst_mps sub s in
    if s==s' then arity else NonPolymorphicType s'
  | PolymorphicArity (ctx,s) ->
    let ctx' = subst_rel_context sub ctx in
    if ctx==ctx' then arity else PolymorphicArity (ctx',s)

(** No need here to check for physical equality after substitution,
    at least for Def due to the delayed substitution [subst_constr_subst]. *)

let subst_const_def sub def = match def with
  | Undef _ -> def
  | Def c -> Def (subst_constr_subst sub c)
  | OpaqueDef lc -> OpaqueDef (subst_lazy_constr sub lc)

let subst_const_body sub cb =
  assert (List.is_empty cb.const_hyps); (* we're outside sections *)
  if is_empty_subst sub then cb
  else
    let body' = subst_const_def sub cb.const_body in
    let type' = subst_const_type sub cb.const_type in
    if body' == cb.const_body && type' == cb.const_type then cb
    else
      { const_hyps = [];
        const_body = body';
        const_type = type';
        const_body_code =
          Cemitcodes.subst_to_patch_subst sub cb.const_body_code;
        const_constraints = cb.const_constraints;
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

let hcons_polyarity ar =
  { poly_param_levels =
      List.smartmap (Option.smartmap Univ.hcons_univ) ar.poly_param_levels;
    poly_level = Univ.hcons_univ ar.poly_level }

let hcons_const_type = function
  | NonPolymorphicType t ->
    NonPolymorphicType (Term.hcons_constr t)
  | PolymorphicArity (ctx,s) ->
    PolymorphicArity (hcons_rel_context ctx, hcons_polyarity s)

let hcons_const_def = function
  | Undef inl -> Undef inl
  | Def l_constr ->
    let constr = force l_constr in
    Def (from_val (Term.hcons_constr constr))
  | OpaqueDef _ as x -> x (* hashconsed when turned indirect *)

let hcons_const_body cb =
  { cb with
    const_body = hcons_const_def cb.const_body;
    const_type = hcons_const_type cb.const_type;
    const_constraints = Univ.hcons_constraints cb.const_constraints; }

(** {6 Inductive types } *)

let eq_recarg r1 r2 = match r1, r2 with
| Norec, Norec -> true
| Mrec i1, Mrec i2 -> Names.eq_ind i1 i2
| Imbr i1, Imbr i2 -> Names.eq_ind i1 i2
| _ -> false

let subst_recarg sub r = match r with
  | Norec -> r
  | Mrec (kn,i) ->
    let kn' = subst_ind sub kn in
    if kn==kn' then r else Mrec (kn',i)
  | Imbr (kn,i) ->
    let kn' = subst_ind sub kn in
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

let subst_indarity sub ar = match ar with
  | Monomorphic s ->
    let uar' = subst_mps sub s.mind_user_arity in
    if uar' == s.mind_user_arity then ar
    else Monomorphic { mind_user_arity = uar'; mind_sort = s.mind_sort }
  | Polymorphic _ -> ar

let subst_mind_packet sub mip =
  let { mind_nf_lc = nf;
        mind_user_lc = user;
        mind_arity_ctxt = ctxt;
        mind_arity = ar;
        mind_recargs = ra } = mip
  in
  let nf' = Array.smartmap (subst_mps sub) nf in
  let user' =
    (* maintain sharing of [mind_user_lc] and [mind_nf_lc] *)
    if user==nf then nf'
    else Array.smartmap (subst_mps sub) user
  in
  let ctxt' = subst_rel_context sub ctxt in
  let ar' = subst_indarity sub ar in
  let ra' = subst_wf_paths sub ra in
  if nf==nf' && user==user' && ctxt==ctxt' && ar==ar' && ra==ra'
  then mip
  else
    { mip with
      mind_nf_lc = nf';
      mind_user_lc = user';
      mind_arity_ctxt = ctxt';
      mind_arity = ar';
      mind_recargs = ra' }

let subst_mind sub mib =
  assert (List.is_empty mib.mind_hyps); (* we're outside sections *)
  if is_empty_subst sub then mib
  else
    let params = mib.mind_params_ctxt in
    let params' = Context.map_rel_context (subst_mps sub) params in
    let packets = mib.mind_packets in
    let packets' = Array.smartmap (subst_mind_packet sub) packets in
    if params==params' && packets==packets' then mib
    else
      { mib with
        mind_params_ctxt = params';
        mind_packets = packets' }

(** {6 Hash-consing of inductive declarations } *)

(** Just as for constants, this hash-consing is quite partial *)

let hcons_indarity = function
  | Monomorphic a ->
    Monomorphic
      { mind_user_arity = Term.hcons_constr a.mind_user_arity;
        mind_sort = Term.hcons_sorts a.mind_sort }
  | Polymorphic a -> Polymorphic (hcons_polyarity a)

let hcons_mind_packet oib =
  let user = Array.smartmap Term.hcons_types oib.mind_user_lc in
  let nf = Array.smartmap Term.hcons_types oib.mind_nf_lc in
  (* Special optim : merge [mind_user_lc] and [mind_nf_lc] if possible *)
  let nf = if Array.equal (==) user nf then user else nf in
  { oib with
    mind_typename = Names.Id.hcons oib.mind_typename;
    mind_arity_ctxt = hcons_rel_context oib.mind_arity_ctxt;
    mind_arity = hcons_indarity oib.mind_arity;
    mind_consnames = Array.smartmap Names.Id.hcons oib.mind_consnames;
    mind_user_lc = user;
    mind_nf_lc = nf }

let hcons_mind mib =
  { mib with
    mind_packets = Array.smartmap hcons_mind_packet mib.mind_packets;
    mind_params_ctxt = hcons_rel_context mib.mind_params_ctxt;
    mind_constraints = Univ.hcons_constraints mib.mind_constraints }

(** {6 Stm machinery } *)

let join_constant_body cb =
  match cb.const_body with
  | OpaqueDef d -> Lazyconstr.join_lazy_constr d
  | _ -> ()

let string_of_side_effect = function
  | SEsubproof (c,_) -> Names.string_of_con c
  | SEscheme (cl,_) ->
      String.concat ", " (List.map (fun (_,c,_) -> Names.string_of_con c) cl)
type side_effects = side_effect list
let no_seff = ([] : side_effects)
let iter_side_effects f l = List.iter f (List.rev l)
let fold_side_effects f a l = List.fold_left f a l
let uniquize_side_effects l = List.uniquize l
let union_side_effects l1 l2 = l1 @ l2
let flatten_side_effects l = List.flatten l
let side_effects_of_list l = l
let cons_side_effects x l = x :: l
let side_effects_is_empty = List.is_empty
