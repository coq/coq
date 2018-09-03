(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

open CErrors
open Util
open Names
open Term
open Constr
open Declarations
open Univ

module NamedDecl = Context.Named.Declaration
module RelDecl = Context.Rel.Declaration

(*s Cooking the constants. *)

let pop_dirpath p = match DirPath.repr p with
  | [] -> anomaly ~label:"dirpath_prefix" (Pp.str "empty dirpath.")
  | _::l -> DirPath.make l

let pop_mind kn =
  let (mp,dir,l) = MutInd.repr3 kn in
  MutInd.make3 mp (pop_dirpath dir) l

let pop_con con =
  let (mp,dir,l) = Constant.repr3 con in
  Constant.make3 mp (pop_dirpath dir) l

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
          pop_mind cst, npars + Array.length newpars
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
      id, RelDecl.LocalDef (Name id, b, t)
    | NamedDecl.LocalAssum (id, t) ->
      let t = Vars.subst_vars subst t in
      id, RelDecl.LocalAssum (Name id, t)
    in
    (decl :: ctx, id :: subst)
  in
  Context.Named.fold_outside fold hyps ~init:([], [])

let abstract_constant_type t (hyps, subst) =
  let t = Vars.subst_vars subst t in
  List.fold_left (fun c d -> mkProd_wo_LetIn d c) t hyps

let abstract_constant_body c (hyps, subst) =
  let c = Vars.subst_vars subst c in
  it_mkLambda_or_LetIn c hyps

type recipe = { from : constant_body; info : Opaqueproof.cooking_info }
type inline = bool

type result = {
  cook_body : constant_def;
  cook_type : types;
  cook_universes : constant_universes;
  cook_inline : inline;
  cook_context : Constr.named_context option;
}

let on_body ml hy f = function
  | Undef _ as x -> x
  | Def cs -> Def (Mod_subst.from_val (f (Mod_subst.force_constr cs)))
  | OpaqueDef o ->
    OpaqueDef (Opaqueproof.discharge_direct_opaque ~cook_constr:f
                 { Opaqueproof.modlist = ml; abstract = hy } o)

let expmod_constr_subst cache modlist subst c =
  let subst = Univ.make_instance_subst subst in
  let c = expmod_constr cache modlist c in
    Vars.subst_univs_level_constr subst c

let cook_constr { Opaqueproof.modlist ; abstract = (vars, subst, _) } c =
  let cache = RefTable.create 13 in
  let expmod = expmod_constr_subst cache modlist subst in
  let hyps = Context.Named.map expmod vars in
  let hyps = abstract_context hyps in
  abstract_constant_body (expmod c) hyps

let lift_univs cb subst auctx0 =
  match cb.const_universes with
  | Monomorphic_const ctx ->
    assert (AUContext.is_empty auctx0);
    subst, (Monomorphic_const ctx)
  | Polymorphic_const auctx ->
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
      subst, (Polymorphic_const (AUContext.union auctx0 auctx))
    else
      let ainst = Univ.make_abstract_instance auctx in
      let subst = Instance.append subst ainst in
      let auctx' = Univ.subst_univs_level_abstract_universe_context (Univ.make_instance_subst subst) auctx in
      subst, (Polymorphic_const (AUContext.union auctx0 auctx'))

let cook_constant ~hcons { from = cb; info } =
  let { Opaqueproof.modlist; abstract } = info in
  let cache = RefTable.create 13 in
  let abstract, usubst, abs_ctx = abstract in
  let usubst, univs = lift_univs cb usubst abs_ctx in
  let expmod = expmod_constr_subst cache modlist usubst in
  let hyps0 = Context.Named.map expmod abstract in
  let hyps = abstract_context hyps0 in
  let map c =
    let c = abstract_constant_body (expmod c) hyps in
    if hcons then Constr.hcons c else c
  in
  let body = on_body modlist (hyps0, usubst, abs_ctx)
    map
    cb.const_body
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
    cook_inline = cb.const_inline_code;
    cook_context = Some const_hyps;
  }

(* let cook_constant_key = CProfile.declare_profile "cook_constant" *)
(* let cook_constant = CProfile.profile2 cook_constant_key cook_constant *)

let expmod_constr modlist c = expmod_constr (RefTable.create 13) modlist c
