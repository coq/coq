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

(** Constants *)

let body_of_constant cb = match cb.const_body with
  | Undef _ -> None
  | Def c -> Some (Lazyconstr.force c)
  | OpaqueDef lc -> Some (Lazyconstr.force_opaque lc)

let constant_has_body cb = match cb.const_body with
  | Undef _ -> false
  | Def _ | OpaqueDef _ -> true

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Undef _ | Def _ -> false

(** Constant substitutions *)

let subst_rel_declaration sub (id,copt,t as x) =
  let copt' = Option.smartmap (subst_mps sub) copt in
  let t' = subst_mps sub t in
  if copt == copt' & t == t' then x else (id,copt',t')

let subst_rel_context sub = List.smartmap (subst_rel_declaration sub)

(* TODO: these substitution functions could avoid duplicating things
   when the substitution have preserved all the fields *)

let subst_const_type sub arity =
  if is_empty_subst sub then arity
  else match arity with
    | NonPolymorphicType s -> NonPolymorphicType (subst_mps sub s)
    | PolymorphicArity (ctx,s) -> PolymorphicArity (subst_rel_context sub ctx,s)

let subst_const_def sub = function
  | Undef inl -> Undef inl
  | Def c -> Def (subst_constr_subst sub c)
  | OpaqueDef lc -> OpaqueDef (subst_lazy_constr sub lc)

let subst_const_body sub cb = {
  const_hyps = (match cb.const_hyps with [] -> [] | _ -> assert false);
  const_body = subst_const_def sub cb.const_body;
  const_type = subst_const_type sub cb.const_type;
  const_body_code = Cemitcodes.subst_to_patch_subst sub cb.const_body_code;
  const_constraints = cb.const_constraints;
  const_native_name = ref NotLinked;
  const_inline_code = cb.const_inline_code }

(** Hash-consing of constants *)

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
  | Def cs -> Def (from_val (Term.hcons_constr (Lazyconstr.force cs)))
  | OpaqueDef lc -> OpaqueDef (Lazyconstr.hcons_lazy_constr lc)

let hcons_const_body cb =
  { cb with
    const_body = hcons_const_def cb.const_body;
    const_type = hcons_const_type cb.const_type;
    const_constraints = Univ.hcons_constraints cb.const_constraints }

(** Inductive types *)

let eq_recarg r1 r2 = match r1, r2 with
| Norec, Norec -> true
| Mrec i1, Mrec i2 -> Names.eq_ind i1 i2
| Imbr i1, Imbr i2 -> Names.eq_ind i1 i2
| _ -> false

let subst_recarg sub r = match r with
  | Norec -> r
  | Mrec (kn,i) -> let kn' = subst_ind sub kn in
      if kn==kn' then r else Mrec (kn',i)
  | Imbr (kn,i) -> let kn' = subst_ind sub kn in
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

(** Substitution of inductive declarations *)

let subst_indarity sub = function
| Monomorphic s ->
    Monomorphic {
      mind_user_arity = subst_mps sub s.mind_user_arity;
      mind_sort = s.mind_sort;
    }
| Polymorphic s as x -> x

let subst_mind_packet sub mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.smartmap (subst_mps sub) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context sub mbp.mind_arity_ctxt;
    mind_arity = subst_indarity sub mbp.mind_arity;
    mind_user_lc = Array.smartmap (subst_mps sub) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealargs_ctxt = mbp.mind_nrealargs_ctxt;
    mind_kelim = mbp.mind_kelim;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*);
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }

let subst_mind sub mib =
  { mind_record = mib.mind_record ;
    mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
    mind_hyps = (match mib.mind_hyps with [] -> [] | _ -> assert false);
    mind_nparams = mib.mind_nparams;
    mind_nparams_rec = mib.mind_nparams_rec;
    mind_params_ctxt =
      Sign.map_rel_context (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = Array.smartmap (subst_mind_packet sub) mib.mind_packets ;
    mind_constraints = mib.mind_constraints;
    mind_native_name = ref NotLinked }

(** Hash-consing of inductive declarations *)

let hcons_indarity = function
  | Monomorphic a ->
    Monomorphic { mind_user_arity = Term.hcons_constr a.mind_user_arity;
		  mind_sort = Term.hcons_sorts a.mind_sort }
  | Polymorphic a -> Polymorphic (hcons_polyarity a)

let hcons_mind_packet oib =
 { oib with
   mind_typename = Names.Id.hcons oib.mind_typename;
   mind_arity_ctxt = hcons_rel_context oib.mind_arity_ctxt;
   mind_arity = hcons_indarity oib.mind_arity;
   mind_consnames = Array.smartmap Names.Id.hcons oib.mind_consnames;
   mind_user_lc = Array.smartmap Term.hcons_types oib.mind_user_lc;
   mind_nf_lc = Array.smartmap Term.hcons_types oib.mind_nf_lc }

let hcons_mind mib =
  { mib with
    mind_packets = Array.smartmap hcons_mind_packet mib.mind_packets;
    mind_params_ctxt = hcons_rel_context mib.mind_params_ctxt;
    mind_constraints = Univ.hcons_constraints mib.mind_constraints }
