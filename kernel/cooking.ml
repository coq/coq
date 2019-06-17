(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of V6.3 file constants.ml
   as part of the rebuilding of Coq around a purely functional
   abstract type-checker, Nov 1999 *)

(* This module implements kernel-level discharching of local
   declarations over global constants and inductive types *)

open Util
open Names
open Term
open Constr
open Declarations
open Univ
open Context

module NamedDecl = Context.Named.Declaration
module RelDecl = Context.Rel.Declaration

(*s Cooking the constants. *)

type my_global_reference =
  | ConstRef of Constant.t
  | IndRef of inductive
  | ConstructRef of constructor

module RefHash =
struct
  type t = my_global_reference
  let equal gr1 gr2 = match gr1, gr2 with
  | ConstRef c1, ConstRef c2 -> Constant.SyntacticOrd.equal c1 c2
  | IndRef i1, IndRef i2 -> eq_syntactic_ind i1 i2
  | ConstructRef c1, ConstructRef c2 -> eq_syntactic_constructor c1 c2
  | _ -> false
  open Hashset.Combine
  let hash = function
  | ConstRef c -> combinesmall 1 (Constant.SyntacticOrd.hash c)
  | IndRef i -> combinesmall 2 (ind_syntactic_hash i)
  | ConstructRef c -> combinesmall 3 (constructor_syntactic_hash c)
end

module RefTable = Hashtbl.Make(RefHash)

let instantiate_my_gr gr u =
  match gr with
  | ConstRef c -> mkConstU (c, u)
  | IndRef i -> mkIndU (i, u)
  | ConstructRef c -> mkConstructU (c, u)

let share cache r (cstl,knl) =
  try RefTable.find cache r
  with Not_found ->
  let (u,l) =
    match r with
    | IndRef (kn,_i) ->
        Mindmap.find kn knl
    | ConstructRef ((kn,_i),_j) ->
        Mindmap.find kn knl
    | ConstRef cst ->
        Cmap.find cst cstl in
  let c = (u, Array.map mkVar l) in
  RefTable.add cache r c;
  c

let share_univs cache r u l =
  let (u', args) = share cache r l in
    mkApp (instantiate_my_gr r (Instance.append u' u), args)

let update_case_info cache ci modlist =
  try
    let (_u,l) = share cache (IndRef ci.ci_ind) modlist in
    { ci with ci_npar = ci.ci_npar + Array.length l }
  with Not_found ->
    ci

let is_empty_modlist (cm, mm) =
  Cmap.is_empty cm && Mindmap.is_empty mm

let expmod_constr cache modlist c =
  let share_univs = share_univs cache in
  let update_case_info = update_case_info cache in
  let rec substrec c =
    match kind c with
      | Case (ci,p,t,br) ->
	  Constr.map substrec (mkCase (update_case_info ci modlist,p,t,br))

      | Ind (ind,u) ->
	  (try
	    share_univs (IndRef ind) u modlist
	   with
	    | Not_found -> Constr.map substrec c)

      | Construct (cstr,u) ->
	  (try
	     share_univs (ConstructRef cstr) u modlist
	   with
	    | Not_found -> Constr.map substrec c)

      | Const (cst,u) ->
	  (try
	    share_univs (ConstRef cst) u modlist
	   with
	    | Not_found -> Constr.map substrec c)

      | Proj (p, c') ->
        let map cst npars =
          let _, newpars = Mindmap.find cst (snd modlist) in
          (cst, npars + Array.length newpars)
        in
        let p' = try Projection.map_npars map p with Not_found -> p in
        let c'' = substrec c' in
        if p == p' && c' == c'' then c else mkProj (p', c'')

  | _ -> Constr.map substrec c

  in
  if is_empty_modlist modlist then c
  else substrec c

(** Transforms a named context into a rel context. Also returns the list of
    variables [id1 ... idn] that need to be replaced by [Rel 1 ... Rel n] to
    abstract a term that lived in that context. *)
let abstract_context hyps =
  let fold decl (ctx, subst) =
    let id, decl = match decl with
    | NamedDecl.LocalDef (id, b, t) ->
      let b = Vars.subst_vars subst b in
      let t = Vars.subst_vars subst t in
      id, RelDecl.LocalDef (map_annot Name.mk_name id, b, t)
    | NamedDecl.LocalAssum (id, t) ->
      let t = Vars.subst_vars subst t in
      id, RelDecl.LocalAssum (map_annot Name.mk_name id, t)
    in
    (decl :: ctx, id.binder_name :: subst)
  in
  Context.Named.fold_outside fold hyps ~init:([], [])

let abstract_constant_type t (hyps, subst) =
  let t = Vars.subst_vars subst t in
  List.fold_left (fun c d -> mkProd_wo_LetIn d c) t hyps

let abstract_constant_body c (hyps, subst) =
  let c = Vars.subst_vars subst c in
  it_mkLambda_or_LetIn c hyps

type recipe = { from : Opaqueproof.opaque constant_body; info : Opaqueproof.cooking_info }
type inline = bool

type 'opaque result = {
  cook_body : (constr Mod_subst.substituted, 'opaque) constant_def;
  cook_type : types;
  cook_universes : universes;
  cook_relevance : Sorts.relevance;
  cook_inline : inline;
  cook_context : Constr.named_context option;
}

let expmod_constr_subst cache modlist subst c =
  let subst = Univ.make_instance_subst subst in
  let c = expmod_constr cache modlist c in
    Vars.subst_univs_level_constr subst c

let discharge_abstract_universe_context subst abs_ctx auctx =
  (** Given a named instance [subst := u₀ ... uₙ₋₁] together with an abstract
      context [auctx0 := 0 ... n - 1 |= C{0, ..., n - 1}] of the same length,
      and another abstract context relative to the former context
      [auctx := 0 ... m - 1 |= C'{u₀, ..., uₙ₋₁, 0, ..., m - 1}],
      construct the lifted abstract universe context
      [0 ... n - 1 n ... n + m - 1 |=
        C{0, ... n - 1} ∪
        C'{0, ..., n - 1, n, ..., n + m - 1} ]
      together with the instance
      [u₀ ... uₙ₋₁ Var(0) ... Var (m - 1)].
  *)
  if (Univ.Instance.is_empty subst) then
    (** Still need to take the union for the constraints between globals *)
    subst, (AUContext.union abs_ctx auctx)
  else
    let open Univ in
    let ainst = make_abstract_instance auctx in
    let subst = Instance.append subst ainst in
    let substf = make_instance_subst subst in
    let auctx = Univ.subst_univs_level_abstract_universe_context substf auctx in
    subst, (AUContext.union abs_ctx auctx)

let lift_univs cb subst auctx0 =
  match cb.const_universes with
  | Monomorphic ctx ->
    assert (AUContext.is_empty auctx0);
    subst, (Monomorphic ctx)
  | Polymorphic auctx ->
    let subst, auctx = discharge_abstract_universe_context subst auctx0 auctx in
    subst, (Polymorphic auctx)

let cook_constr { Opaqueproof.modlist ; abstract } (c, priv) =
  let cache = RefTable.create 13 in
  let abstract, usubst, abs_ctx = abstract in
  let usubst, priv = match priv with
  | Opaqueproof.PrivateMonomorphic () ->
    let () = assert (AUContext.is_empty abs_ctx) in
    let () = assert (Instance.is_empty usubst) in
    usubst, priv
  | Opaqueproof.PrivatePolymorphic (univs, ctx) ->
    let ainst = Instance.of_array (Array.init univs Level.var) in
    let usubst = Instance.append usubst ainst in
    let ctx = on_snd (Univ.subst_univs_level_constraints (Univ.make_instance_subst usubst)) ctx in
    let univs = univs + AUContext.size abs_ctx in
    usubst, Opaqueproof.PrivatePolymorphic (univs, ctx)
  in
  let expmod = expmod_constr_subst cache modlist usubst in
  let hyps = Context.Named.map expmod abstract in
  let hyps = abstract_context hyps in
  let c = abstract_constant_body (expmod c) hyps in
  (c, priv)

let cook_constr infos c =
  let fold info c = cook_constr info c in
  List.fold_right fold infos c

let cook_constant { from = cb; info } =
  let { Opaqueproof.modlist; abstract } = info in
  let cache = RefTable.create 13 in
  let abstract, usubst, abs_ctx = abstract in
  let usubst, univs = lift_univs cb usubst abs_ctx in
  let expmod = expmod_constr_subst cache modlist usubst in
  let hyps0 = Context.Named.map expmod abstract in
  let hyps = abstract_context hyps0 in
  let map c = abstract_constant_body (expmod c) hyps in
  let body = match cb.const_body with
  | Undef _ as x -> x
  | Def cs -> Def (Mod_subst.from_val (map (Mod_subst.force_constr cs)))
  | OpaqueDef o ->
    OpaqueDef (Opaqueproof.discharge_direct_opaque info o)
  | Primitive _ -> CErrors.anomaly (Pp.str "Primitives cannot be cooked")
  in
  let const_hyps =
    Context.Named.fold_outside (fun decl hyps ->
      List.filter (fun decl' -> not (Id.equal (NamedDecl.get_id decl) (NamedDecl.get_id decl')))
		  hyps)
      hyps0 ~init:cb.const_hyps in
  let typ = abstract_constant_type (expmod cb.const_type) hyps in
  {
    cook_body = body;
    cook_type = typ;
    cook_universes = univs;
    cook_relevance = cb.const_relevance;
    cook_inline = cb.const_inline_code;
    cook_context = Some const_hyps;
  }

(* let cook_constant_key = CProfile.declare_profile "cook_constant" *)
(* let cook_constant = CProfile.profile2 cook_constant_key cook_constant *)

(********************************)
(* Discharging mutual inductive *)

(* Replace

     Var(y1)..Var(yq):C1..Cq |- Ij:Bj
     Var(y1)..Var(yq):C1..Cq; I1..Ip:B1..Bp |- ci : Ti

   by

     |- Ij: (y1..yq:C1..Cq)Bj
     I1..Ip:(B1 y1..yq)..(Bp y1..yq) |- ci : (y1..yq:C1..Cq)Ti[Ij:=(Ij y1..yq)]
*)

let it_mkNamedProd_wo_LetIn b d =
  List.fold_left (fun c d -> mkNamedProd_wo_LetIn d c) b d

let abstract_inductive decls nparamdecls inds =
  let open Entries in
  let ntyp = List.length inds in
  let ndecls = Context.Named.length decls in
  let args = Context.Named.to_instance mkVar (List.rev decls) in
  let args = Array.of_list args in
  let subs = List.init ntyp (fun k -> lift ndecls (mkApp(mkRel (k+1),args))) in
  let inds' =
    List.map
      (function (tname,arity,template,cnames,lc) ->
        let lc' = List.map (Vars.substl subs) lc in
        let lc'' = List.map (fun b -> it_mkNamedProd_wo_LetIn b decls) lc' in
        let arity' = it_mkNamedProd_wo_LetIn arity decls in
        (tname,arity',template,cnames,lc''))
        inds in
  let nparamdecls' = nparamdecls + Array.length args in
(* To be sure to be the same as before, should probably be moved to cook_inductive *)
  let params' = let (_,arity,_,_,_) = List.hd inds' in
                let (params,_) = decompose_prod_n_assum nparamdecls' arity in
    params
  in
  let ind'' =
  List.map
    (fun (a,arity,template,c,lc) ->
      let _, short_arity = decompose_prod_n_assum nparamdecls' arity in
      let shortlc =
        List.map (fun c -> snd (decompose_prod_n_assum nparamdecls' c)) lc in
      { mind_entry_typename = a;
        mind_entry_arity = short_arity;
        mind_entry_template = template;
        mind_entry_consnames = c;
        mind_entry_lc = shortlc })
    inds'
  in (params',ind'')

let refresh_polymorphic_type_of_inductive (_,mip) =
  match mip.mind_arity with
  | RegularArity s -> s.mind_user_arity, false
  | TemplateArity ar ->
    let ctx = List.rev mip.mind_arity_ctxt in
      mkArity (List.rev ctx, Sorts.sort_of_univ ar.template_level), true

let dummy_variance = let open Entries in function
  | Monomorphic_entry _ -> assert false
  | Polymorphic_entry (_,uctx) -> Array.make (Univ.UContext.size uctx) Univ.Variance.Irrelevant

let cook_inductive { Opaqueproof.modlist; abstract } mib =
  let open Entries in
  let (section_decls, subst, abs_uctx) = abstract in
  let nparamdecls = Context.Rel.length mib.mind_params_ctxt in
  let subst, ind_univs =
    match mib.mind_universes with
    | Monomorphic ctx -> Univ.empty_level_subst, Monomorphic_entry ctx
    | Polymorphic auctx ->
      let subst, auctx = discharge_abstract_universe_context subst abs_uctx auctx in
      let subst = Univ.make_instance_subst subst in
      let nas = Univ.AUContext.names auctx in
      let auctx = Univ.AUContext.repr auctx in
      subst, Polymorphic_entry (nas, auctx)
  in
  let variance = match mib.mind_variance with
    | None -> None
    | Some _ -> Some (dummy_variance ind_univs)
  in
  let cache = RefTable.create 13 in
  let discharge c = Vars.subst_univs_level_constr subst (expmod_constr cache modlist c) in
  let inds =
    Array.map_to_list
      (fun mip ->
        let ty, template = refresh_polymorphic_type_of_inductive (mib,mip) in
        let arity = discharge ty in
        let lc = Array.map discharge mip.mind_user_lc  in
          (mip.mind_typename,
           arity, template,
           Array.to_list mip.mind_consnames,
           Array.to_list lc))
      mib.mind_packets in
  let section_decls' = Context.Named.map discharge section_decls in
  let (params',inds') = abstract_inductive section_decls' nparamdecls inds in
  let record = match mib.mind_record with
    | PrimRecord info ->
      Some (Some (Array.map (fun (x,_,_,_) -> x) info))
    | FakeRecord -> Some None
    | NotRecord -> None
  in
  { mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds';
    mind_entry_private = mib.mind_private;
    mind_entry_variance = variance;
    mind_entry_universes = ind_univs
  }

let expmod_constr modlist c = expmod_constr (RefTable.create 13) modlist c
