(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of V6.3 file constants.ml
   as part of the rebuilding of Coq around a purely functional
   abstract type-checker, Nov 1999 *)

(* This module implements kernel-level discharching of local
   declarations over global constants and inductive types *)

open CErrors
open Util
open Names
open Term
open Declarations
open Univ

module NamedDecl = Context.Named.Declaration

(*s Cooking the constants. *)

let pop_dirpath p = match DirPath.repr p with
  | [] -> anomaly ~label:"dirpath_prefix" (Pp.str "empty dirpath.")
  | _::l -> DirPath.make l

let pop_mind kn =
  let (mp,dir,l) = Names.repr_mind kn in
  Names.make_mind mp (pop_dirpath dir) l

let pop_con con =
  let (mp,dir,l) = Names.repr_con con in
  Names.make_con mp (pop_dirpath dir) l

type my_global_reference =
  | ConstRef of constant
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
  let f,(u,l) =
    match r with
    | IndRef (kn,i) ->
	IndRef (pop_mind kn,i), Mindmap.find kn knl
    | ConstructRef ((kn,i),j) ->
	ConstructRef ((pop_mind kn,i),j), Mindmap.find kn knl
    | ConstRef cst ->
	ConstRef (pop_con cst), Cmap.find cst cstl in
  let c = (f, (u, Array.map mkVar l)) in
  RefTable.add cache r c;
  c

let share_univs cache r u l =
  let r', (u', args) = share cache r l in
    mkApp (instantiate_my_gr r' (Instance.append u' u), args)

let update_case_info cache ci modlist =
  try
    let ind, n =
      match share cache (IndRef ci.ci_ind) modlist with
      | (IndRef f,(u,l)) -> (f, Array.length l)
      | _ -> assert false in
    { ci with ci_ind = ind; ci_npar = ci.ci_npar + n }
  with Not_found ->
    ci

let is_empty_modlist (cm, mm) =
  Cmap.is_empty cm && Mindmap.is_empty mm

let expmod_constr cache modlist c =
  let share_univs = share_univs cache in
  let update_case_info = update_case_info cache in
  let rec substrec c =
    match kind_of_term c with
      | Case (ci,p,t,br) ->
	  map_constr substrec (mkCase (update_case_info ci modlist,p,t,br))

      | Ind (ind,u) ->
	  (try
	    share_univs (IndRef ind) u modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Construct (cstr,u) ->
	  (try
	     share_univs (ConstructRef cstr) u modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Const (cst,u) ->
	  (try
	    share_univs (ConstRef cst) u modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Proj (p, c') ->
          (try 
	     let p' = share_univs (ConstRef (Projection.constant p)) Univ.Instance.empty modlist in
	     let make c = Projection.make c (Projection.unfolded p) in
	     match kind_of_term p' with
	     | Const (p',_) -> mkProj (make p', substrec c')
	     | App (f, args) -> 
	       (match kind_of_term f with 
	       | Const (p', _) -> mkProj (make p', substrec c')
	       | _ -> assert false)
	     | _ -> assert false
	   with Not_found -> map_constr substrec c)

  | _ -> map_constr substrec c

  in
  if is_empty_modlist modlist then c
  else substrec c

let abstract_constant_type =
   List.fold_left (fun c d -> mkNamedProd_wo_LetIn d c)

let abstract_constant_body =
  List.fold_left (fun c d -> mkNamedLambda_or_LetIn d c)

type recipe = { from : constant_body; info : Opaqueproof.cooking_info }
type inline = bool

type result = {
  cook_body : constant_def;
  cook_type : types;
  cook_proj : projection_body option;
  cook_universes : constant_universes;
  cook_inline : inline;
  cook_context : Context.Named.t option;
}

let on_body ml hy f = function
  | Undef _ as x -> x
  | Def cs -> Def (Mod_subst.from_val (f (Mod_subst.force_constr cs)))
  | OpaqueDef o ->
    OpaqueDef (Opaqueproof.discharge_direct_opaque ~cook_constr:f
                 { Opaqueproof.modlist = ml; abstract = hy } o)

let expmod_constr_subst cache modlist subst c =
  let c = expmod_constr cache modlist c in
    Vars.subst_univs_level_constr subst c

let cook_constr { Opaqueproof.modlist ; abstract } c =
  let cache = RefTable.create 13 in
  let expmod = expmod_constr_subst cache modlist (pi2 abstract) in
  let hyps = Context.Named.map expmod (pi1 abstract) in
  abstract_constant_body (expmod c) hyps

let lift_univs cb subst =
  match cb.const_universes with
  | Monomorphic_const ctx -> subst, (Monomorphic_const ctx)
  | Polymorphic_const auctx ->  
    if (Univ.LMap.is_empty subst) then
      subst, (Polymorphic_const auctx)
    else
      let len = Univ.LMap.cardinal subst in
      let rec gen_subst i acc =
        if i < 0 then acc
        else
          let acc = Univ.LMap.add (Level.var i) (Level.var (i + len)) acc in
          gen_subst (pred i) acc
      in
      let subst = gen_subst (Univ.AUContext.size auctx - 1) subst in
      let auctx' = Univ.subst_univs_level_abstract_universe_context subst auctx in
      subst, (Polymorphic_const auctx')

let cook_constant ~hcons env { from = cb; info } =
  let { Opaqueproof.modlist; abstract } = info in
  let cache = RefTable.create 13 in
  let abstract, usubst, abs_ctx = abstract in
  let usubst, univs = lift_univs cb usubst in
  let expmod = expmod_constr_subst cache modlist usubst in
  let hyps = Context.Named.map expmod abstract in
  let map c =
    let c = abstract_constant_body (expmod c) hyps in
    if hcons then hcons_constr c else c
  in
  let body = on_body modlist (hyps, usubst, abs_ctx)
    map
    cb.const_body
  in
  let const_hyps =
    Context.Named.fold_outside (fun decl hyps ->
      List.filter (fun decl' -> not (Id.equal (NamedDecl.get_id decl) (NamedDecl.get_id decl')))
		  hyps)
      hyps ~init:cb.const_hyps in
  let typ = abstract_constant_type (expmod cb.const_type) hyps in
  let projection pb =
    let c' = abstract_constant_body (expmod pb.proj_body) hyps in
    let etab = abstract_constant_body (expmod (fst pb.proj_eta)) hyps in
    let etat = abstract_constant_body (expmod (snd pb.proj_eta)) hyps in
    let ((mind, _), _), n' =
      try 
	let c' = share_univs cache (IndRef (pb.proj_ind,0)) Univ.Instance.empty modlist in
	  match kind_of_term c' with
	  | App (f,l) -> (destInd f, Array.length l)
	  | Ind ind -> ind, 0
	  | _ -> assert false 
      with Not_found -> (((pb.proj_ind,0),Univ.Instance.empty), 0)
    in 
    let ctx, ty' = decompose_prod_n (n' + pb.proj_npars + 1) typ in
      { proj_ind = mind; proj_npars = pb.proj_npars + n'; proj_arg = pb.proj_arg;
	proj_eta = etab, etat;
	proj_type = ty'; proj_body = c' }
  in
  let univs =
    match univs with
    | Monomorphic_const ctx -> 
      assert (AUContext.is_empty abs_ctx); univs
    | Polymorphic_const auctx -> 
      Polymorphic_const (AUContext.union abs_ctx auctx)
  in
  {
    cook_body = body;
    cook_type = typ;
    cook_proj = Option.map projection cb.const_proj;
    cook_universes = univs;
    cook_inline = cb.const_inline_code;
    cook_context = Some const_hyps;
  }

(* let cook_constant_key = Profile.declare_profile "cook_constant" *)
(* let cook_constant = Profile.profile2 cook_constant_key cook_constant *)

let expmod_constr modlist c = expmod_constr (RefTable.create 13) modlist c
