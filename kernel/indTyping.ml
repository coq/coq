(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Univ
open Term
open Constr
open Vars
open Declarations
open Environ
open Reduction
open Typeops
open Entries
open Pp
open Type_errors
open Context.Rel.Declaration

let is_constructor_head t =
  isRel(fst(decompose_app t))

(************************************************************************)
(* Various well-formedness check for inductive declarations            *)

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

let check_constructors_names =
  let rec check idset = function
    | [] -> idset
    | c::cl ->
        if Id.Set.mem c idset then
          raise (InductiveError (SameNamesConstructors c))
        else
          check (Id.Set.add c idset) cl
  in
  check

(* [mind_check_names mie] checks the names of an inductive types declaration,
   and raises the corresponding exceptions when two types or two constructors
   have the same name. *)

let mind_check_names mie =
  let rec check indset cstset = function
    | [] -> ()
    | ind::inds ->
        let id = ind.mind_entry_typename in
        let cl = ind.mind_entry_consnames in
        if Id.Set.mem id indset then
          raise (InductiveError (SameNamesTypes id))
        else
          let cstset' = check_constructors_names cstset cl in
          check (Id.Set.add id indset) cstset' inds
  in
  check Id.Set.empty Id.Set.empty mie.mind_entry_inds
(* The above verification is not necessary from the kernel point of
  vue since inductive and constructors are not referred to by their
  name, but only by the name of the inductive packet and an index. *)

(************************************************************************)
(************************************************************************)

(* Typing the arities and constructor types *)

let infos_and_sort env t =
  let rec aux env t max =
    let t = whd_all env t in
      match kind t with
      | Prod (name,c1,c2) ->
        let varj = infer_type env c1 in
        let env1 = Environ.push_rel (LocalAssum (name,varj.utj_val)) env in
        let max = Universe.sup max (Sorts.univ_of_sort varj.utj_type) in
          aux env1 c2 max
    | _ when is_constructor_head t -> max
    | _ -> (* don't fail if not positive, it is tested later *) max
  in aux env t Universe.type0m

(* Computing the levels of polymorphic inductive types

   For each inductive type of a block that is of level u_i, we have
   the constraints that u_i >= v_i where v_i is the type level of the
   types of the constructors of this inductive type. Each v_i depends
   of some of the u_i and of an extra (maybe non variable) universe,
   say w_i that summarize all the other constraints. Typically, for
   three inductive types, we could have

   u1,u2,u3,w1 <= u1
   u1       w2 <= u2
      u2,u3,w3 <= u3

   From this system of inequations, we shall deduce

   w1,w2,w3 <= u1
   w1,w2 <= u2
   w1,w2,w3 <= u3
*)

(* This (re)computes informations relevant to extraction and the sort of an
   arity or type constructor; we do not to recompute universes constraints *)

let infer_constructor_packet env_ar_par params lc =
  (* type-check the constructors *)
  let jlc = List.map (infer_type env_ar_par) lc in
  let jlc = Array.of_list jlc in
  (* generalize the constructor over the parameters *)
  let lc'' = Array.map (fun j -> Term.it_mkProd_or_LetIn j.utj_val params) jlc in
  (* compute the max of the sorts of the products of the constructors types *)
  let levels = List.map (infos_and_sort env_ar_par) lc in
  let min = if Array.length jlc > 1 then Universe.type0 else Universe.type0m in
  let level = List.fold_left (fun max l -> Universe.sup max l) min levels in
  (lc'', level)

(* If indices matter *)
let cumulate_arity_large_levels env sign =
  fst (List.fold_right
    (fun d (lev,env) ->
     match d with
     | LocalAssum (_,t) ->
        let tj = infer_type env t in
        let u = Sorts.univ_of_sort tj.utj_type in
          (Universe.sup u lev, push_rel d env)
     | LocalDef _ ->
        lev, push_rel d env)
    sign (Universe.type0m,env))

let is_impredicative env u =
  is_type0m_univ u || (is_type0_univ u && is_impredicative_set env)

(* Returns the list [x_1, ..., x_n] of levels contributing to template
   polymorphism. The elements x_k is None if the k-th parameter (starting
   from the most recent and ignoring let-definitions) is not contributing
   or is Some u_k if its level is u_k and is contributing. *)
let param_ccls paramsctxt =
  let fold acc = function
    | (LocalAssum (_, p)) ->
      (let c = Term.strip_prod_assum p in
      match kind c with
        | Sort (Type u) -> Univ.Universe.level u
        | _ -> None) :: acc
    | LocalDef _ -> acc
  in
  List.fold_left fold [] paramsctxt

(* Check arities and constructors *)
let check_subtyping_arity_constructor env (subst : constr -> constr) (arcn : types) numparams is_arity =
  let numchecked = ref 0 in
  let basic_check ev tp =
    if !numchecked < numparams then () else conv_leq ev tp (subst tp);
    numchecked := !numchecked + 1
  in
  let check_typ typ typ_env =
    match typ with
    | LocalAssum (_, typ') ->
      begin
       try
          basic_check typ_env typ'; Environ.push_rel typ typ_env
        with NotConvertible ->
          anomaly ~label:"bad inductive subtyping relation" (Pp.str "Invalid subtyping relation")
      end
    | _ -> anomaly (Pp.str "")
  in
  let typs, codom = dest_prod env arcn in
  let last_env = Context.Rel.fold_outside check_typ typs ~init:env in
  if not is_arity then basic_check last_env codom else ()

(* Check that the subtyping information inferred for inductive types in the block is correct. *)
(* This check produces a value of the unit type if successful or raises an anomaly if check fails. *)
let check_subtyping cumi paramsctxt env_ar inds =
    let numparams = Context.Rel.nhyps paramsctxt in
    let uctx = CumulativityInfo.univ_context cumi in
    let new_levels = Array.init (UContext.size uctx)
        (fun i -> Level.(make (UGlobal.make DirPath.empty i)))
    in
    let lmap = Array.fold_left2 (fun lmap u u' -> LMap.add u u' lmap)
        LMap.empty (Instance.to_array @@ UContext.instance uctx) new_levels
    in
    let dosubst = subst_univs_level_constr lmap in
    let instance_other = Instance.of_array new_levels in
    let constraints_other = Univ.subst_univs_level_constraints lmap (Univ.UContext.constraints uctx) in
    let uctx_other = Univ.UContext.make (instance_other, constraints_other) in
    let env = Environ.push_context uctx_other env_ar in
    let subtyp_constraints =
      CumulativityInfo.leq_constraints cumi
        (UContext.instance uctx) instance_other
        Constraint.empty
    in
    let env = Environ.add_constraints subtyp_constraints env in
    (* process individual inductive types: *)
    Array.iter (fun (_id,_cn,lc,(_sign,arity)) ->
      match arity with
        | RegularArity (_, full_arity, _) ->
           check_subtyping_arity_constructor env dosubst full_arity numparams true;
           Array.iter (fun cnt -> check_subtyping_arity_constructor env dosubst cnt numparams false) lc
        | TemplateArity _ ->
          anomaly ~label:"check_subtyping"
            Pp.(str "template polymorphism and cumulative polymorphism are not compatible")
    ) inds

(* Type-check an inductive definition. Does not check positivity
   conditions. *)
(* TODO check that we don't overgeneralize construcors/inductive arities with
   universes that are absent from them. Is it possible?
*)
let typecheck_inductive env mie =
  let () = match mie.mind_entry_inds with
  | [] -> anomaly (Pp.str "empty inductive types declaration.")
  | _ -> ()
  in
  (* Check unicity of names *)
  mind_check_names mie;
  (* Params are typed-checked here *)
  let env' =
    match mie.mind_entry_universes with
    | Monomorphic_ind_entry ctx -> push_context_set ctx env
    | Polymorphic_ind_entry (_, ctx) -> push_context ctx env
    | Cumulative_ind_entry (_, cumi) -> push_context (Univ.CumulativityInfo.univ_context cumi) env
  in
  let env_params = check_context env' mie.mind_entry_params in
  let paramsctxt = mie.mind_entry_params in
  (* We first type arity of each inductive definition *)
  (* This allows building the environment of arities and to share *)
  (* the set of constraints *)
  let env_arities, rev_arity_list =
    List.fold_left
      (fun (env_ar,l) ind ->
         (* Arities (without params) are typed-checked here *)
         let template = ind.mind_entry_template in
         let arity =
           if isArity ind.mind_entry_arity then
             let (ctx,s) = dest_arity env_params ind.mind_entry_arity in
               match s with
               | Type u when Univ.universe_level u = None ->
                 (** We have an algebraic universe as the conclusion of the arity,
                     typecheck the dummy Π ctx, Prop and do a special case for the conclusion.
                 *)
                 let proparity = infer_type env_params (mkArity (ctx, Sorts.prop)) in
                 let (cctx, _) = destArity proparity.utj_val in
                   (* Any universe is well-formed, we don't need to check [s] here *)
                   mkArity (cctx, s)
               | _ ->
                 let arity = infer_type env_params ind.mind_entry_arity in
                   arity.utj_val
           else let arity = infer_type env_params ind.mind_entry_arity in
                  arity.utj_val
         in
         let (sign, deflev) = dest_arity env_params arity in
         let inflev =
           (* The level of the inductive includes levels of indices if
              in indices_matter mode *)
             if indices_matter env
             then Some (cumulate_arity_large_levels env_params sign)
             else None
         in
         (* We do not need to generate the universe of full_arity; if
            later, after the validation of the inductive definition,
            full_arity is used as argument or subject to cast, an
            upper universe will be generated *)
         let full_arity = it_mkProd_or_LetIn arity paramsctxt in
         let id = ind.mind_entry_typename in
         let env_ar' =
           push_rel (LocalAssum (Name id, full_arity)) env_ar in
             (* (add_constraints cst2 env_ar) in *)
           (env_ar', (id,full_arity,sign @ paramsctxt,template,deflev,inflev)::l))
      (env',[])
      mie.mind_entry_inds in

  let arity_list = List.rev rev_arity_list in

  (* builds the typing context "Gamma, I1:A1, ... In:An, params" *)
  let env_ar_par = push_rel_context paramsctxt env_arities in

  (* Now, we type the constructors (without params) *)
  let inds =
    List.fold_right2
      (fun ind arity_data inds ->
         let (lc',cstrs_univ) =
           infer_constructor_packet env_ar_par paramsctxt ind.mind_entry_lc in
         let consnames = ind.mind_entry_consnames in
         let ind' = (arity_data,consnames,lc',cstrs_univ) in
           ind'::inds)
      mie.mind_entry_inds
      arity_list
    ([]) in

  let inds = Array.of_list inds in

  (* Compute/check the sorts of the inductive types *)

  let inds =
    Array.map (fun ((id,full_arity,sign,template,def_level,inf_level),cn,lc,clev)  ->
      let infu =
        (** Inferred level, with parameters and constructors. *)
        match inf_level with
        | Some alev -> Universe.sup clev alev
        | None -> clev
      in
      let full_polymorphic () =
        let defu = Sorts.univ_of_sort def_level in
        let is_natural =
          type_in_type env || (UGraph.check_leq (universes env') infu defu)
        in
        let _ =
          (** Impredicative sort, always allow *)
          if is_impredicative env defu then ()
          else (** Predicative case: the inferred level must be lower or equal to the
                   declared level. *)
            if not is_natural then
              anomaly ~label:"check_inductive"
                (Pp.str"Incorrect universe " ++
                   Universe.pr defu ++ Pp.str " declared for inductive type, inferred level is "
                 ++ Universe.pr infu ++ Pp.str ".")
        in
          RegularArity (not is_natural,full_arity,defu)
      in
      let template_polymorphic () =
        let _sign, s =
          try dest_arity env full_arity
          with NotArity -> raise (InductiveError (NotAnArity (env, full_arity)))
        in
        let u = Sorts.univ_of_sort s in
        (* The polymorphic level is a function of the level of the *)
        (* conclusions of the parameters *)
        (* We enforce [u >= lev] in case [lev] has a strict upper *)
        (* constraints over [u] *)
        let b = type_in_type env || UGraph.check_leq (universes env') infu u in
        if not b then
          anomaly ~label:"check_inductive"
            (Pp.str"Incorrect universe " ++
             Universe.pr u ++ Pp.str " declared for inductive type, inferred level is "
             ++ Universe.pr clev ++ Pp.str ".")
        else
          TemplateArity (param_ccls paramsctxt, infu)
      in
      let arity =
        match mie.mind_entry_universes with
        | Monomorphic_ind_entry _ ->
          if template then template_polymorphic ()
          else full_polymorphic ()
        | Polymorphic_ind_entry _ | Cumulative_ind_entry _ ->
          if template
          then anomaly ~label:"polymorphic_template_ind"
              Pp.(strbrk "Template polymorphism and full polymorphism are incompatible.")
          else full_polymorphic ()
      in
        (id,cn,lc,(sign,arity)))
    inds
  in
  (* Check that the subtyping information inferred for inductive types in the block is correct. *)
  (* This check produces a value of the unit type if successful or raises an anomaly if check fails. *)
  let () =
    match mie.mind_entry_universes with
    | Monomorphic_ind_entry _ -> ()
    | Polymorphic_ind_entry _ -> ()
    | Cumulative_ind_entry (_, cumi) -> check_subtyping cumi paramsctxt env_arities inds
  in (env_arities, env_ar_par, paramsctxt, inds)
