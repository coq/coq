(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Util
open Names
open Term
open Vars
open Termops
open Namegen
open Pre_env
open Environ
open Evd
open Sigma.Notations

let safe_evar_value sigma ev =
  try Some (Evd.existential_value sigma ev)
  with NotInstantiatedEvar | Not_found -> None

(** Combinators *)

let evd_comb0 f evdref =
  let (evd',x) = f !evdref in
    evdref := evd';
    x

let evd_comb1 f evdref x =
  let (evd',y) = f !evdref x in
    evdref := evd';
    y

let evd_comb2 f evdref x y =
  let (evd',z) = f !evdref x y in
    evdref := evd';
    z

let e_new_global evdref x = 
  evd_comb1 (Evd.fresh_global (Global.env())) evdref x

let new_global evd x = 
  Sigma.fresh_global (Global.env()) evd x

(****************************************************)
(* Expanding/testing/exposing existential variables *)
(****************************************************)

(* flush_and_check_evars fails if an existential is undefined *)

exception Uninstantiated_evar of existential_key

let rec flush_and_check_evars sigma c =
  match kind_of_term c with
  | Evar (evk,_ as ev) ->
      (match existential_opt_value sigma ev with
       | None -> raise (Uninstantiated_evar evk)
       | Some c -> flush_and_check_evars sigma c)
  | _ -> map_constr (flush_and_check_evars sigma) c

(* let nf_evar_key = Profile.declare_profile "nf_evar"  *)
(* let nf_evar = Profile.profile2 nf_evar_key Reductionops.nf_evar *)

let rec whd_evar sigma c =
  match kind_of_term c with
    | Evar ev ->
        let (evk, args) = ev in
        let args = Array.map (fun c -> whd_evar sigma c) args in
        (match safe_evar_value sigma (evk, args) with
            Some c -> whd_evar sigma c
          | None -> c)
    | Sort (Type u) -> 
      let u' = Evd.normalize_universe sigma u in
	if u' == u then c else mkSort (Sorts.sort_of_univ u')
    | Const (c', u) when not (Univ.Instance.is_empty u) -> 
      let u' = Evd.normalize_universe_instance sigma u in
	if u' == u then c else mkConstU (c', u')
    | Ind (i, u) when not (Univ.Instance.is_empty u) -> 
      let u' = Evd.normalize_universe_instance sigma u in
	if u' == u then c else mkIndU (i, u')
    | Construct (co, u) when not (Univ.Instance.is_empty u) ->
      let u' = Evd.normalize_universe_instance sigma u in
	if u' == u then c else mkConstructU (co, u')
    | _ -> c

let rec nf_evar sigma t = Constr.map (fun t -> nf_evar sigma t) (whd_evar sigma t)

let j_nf_evar sigma j =
  { uj_val = nf_evar sigma j.uj_val;
    uj_type = nf_evar sigma j.uj_type }
let jl_nf_evar sigma jl = List.map (j_nf_evar sigma) jl
let jv_nf_evar sigma = Array.map (j_nf_evar sigma)
let tj_nf_evar sigma {utj_val=v;utj_type=t} =
  {utj_val=nf_evar sigma v;utj_type=t}

let nf_evars_universes evm =
  Universes.nf_evars_and_universes_opt_subst (safe_evar_value evm) 
    (Evd.universe_subst evm)
    
let nf_evars_and_universes evm =
  let evm = Evd.nf_constraints evm in
    evm, nf_evars_universes evm

let e_nf_evars_and_universes evdref =
  evdref := Evd.nf_constraints !evdref;
  nf_evars_universes !evdref, Evd.universe_subst !evdref

let nf_evar_map_universes evm =
  let evm = Evd.nf_constraints evm in
  let subst = Evd.universe_subst evm in
    if Univ.LMap.is_empty subst then evm, nf_evar evm
    else
      let f = nf_evars_universes evm in
	Evd.raw_map (fun _ -> map_evar_info f) evm, f

let nf_named_context_evar sigma ctx =
  Context.Named.map (nf_evar sigma) ctx

let nf_rel_context_evar sigma ctx =
  Context.Rel.map (nf_evar sigma) ctx

let nf_env_evar sigma env =
  let nc' = nf_named_context_evar sigma (Environ.named_context env) in
  let rel' = nf_rel_context_evar sigma (Environ.rel_context env) in
    push_rel_context rel' (reset_with_named_context (val_of_named_context nc') env)

let nf_evar_info evc info = map_evar_info (nf_evar evc) info

let nf_evar_map evm =
  Evd.raw_map (fun _ evi -> nf_evar_info evm evi) evm

let nf_evar_map_undefined evm =
  Evd.raw_map_undefined (fun _ evi -> nf_evar_info evm evi) evm

(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

(* A probably faster though more approximative variant of
   [has_undefined (nf_evar c)]: instances are not substituted and
   maybe an evar occurs in an instance and it would disappear by
   instantiation *)

let has_undefined_evars evd t =
  let rec has_ev t =
    match kind_of_term t with
    | Evar (ev,args) ->
        (match evar_body (Evd.find evd ev) with
        | Evar_defined c ->
            has_ev c; Array.iter has_ev args
        | Evar_empty ->
	    raise NotInstantiatedEvar)
    | _ -> iter_constr has_ev t in
  try let _ = has_ev t in false
  with (Not_found | NotInstantiatedEvar) -> true

let is_ground_term evd t =
  not (has_undefined_evars evd t)

let is_ground_env evd env =
  let open Context.Rel.Declaration in
  let is_ground_rel_decl = function
    | LocalDef (_,b,_) -> is_ground_term evd b
    | _ -> true in
  let open Context.Named.Declaration in
  let is_ground_named_decl = function
    | LocalDef (_,b,_) -> is_ground_term evd b
    | _ -> true in
  List.for_all is_ground_rel_decl (rel_context env) &&
  List.for_all is_ground_named_decl (named_context env)

(* Memoization is safe since evar_map and environ are applicative
   structures *)
let memo f =
  let m = ref None in
  fun x y -> match !m with
  | Some (x', y', r) when x == x' && y == y' -> r
  | _ -> let r = f x y in m := Some (x, y, r); r

let is_ground_env = memo is_ground_env

(* Return the head evar if any *)

exception NoHeadEvar

let head_evar =
  let rec hrec c = match kind_of_term c with
    | Evar (evk,_)   -> evk
    | Case (_,_,c,_) -> hrec c
    | App (c,_)      -> hrec c
    | Cast (c,_,_)   -> hrec c
    | Proj (p, c)    -> hrec c
    | _              -> raise NoHeadEvar
  in
  hrec

(* Expand head evar if any (currently consider only applications but I
   guess it should consider Case too) *)

let whd_head_evar_stack sigma c =
  let rec whrec (c, l as s) =
    match kind_of_term c with
      | Evar (evk,args as ev) ->
        let v =
          try Some (existential_value sigma ev)
          with NotInstantiatedEvar | Not_found  -> None in
        begin match v with
        | None -> s
        | Some c -> whrec (c, l)
        end
      | Cast (c,_,_) -> whrec (c, l)
      | App (f,args) -> whrec (f, args :: l)
      | _ -> s
  in
  whrec (c, [])

let whd_head_evar sigma c =
  let (f, args) = whd_head_evar_stack sigma c in
  (** optim: don't reallocate if empty/singleton *)
  match args with
  | [] -> f
  | [arg] -> mkApp (f, arg)
  | _ -> mkApp (f, Array.concat args)

(**********************)
(* Creating new metas *)
(**********************)

let meta_counter_summary_name = "meta counter"

(* Generator of metavariables *)
let new_meta =
  let meta_ctr = Summary.ref 0 ~name:meta_counter_summary_name in
  fun () -> incr meta_ctr; !meta_ctr

let mk_new_meta () = mkMeta(new_meta())

(* The list of non-instantiated existential declarations (order is important) *)

let non_instantiated sigma =
  let listev = Evd.undefined_map sigma in
  Evar.Map.smartmap (fun evi -> nf_evar_info sigma evi) listev

(************************)
(* Manipulating filters *)
(************************)

let make_pure_subst evi args =
  let open Context.Named.Declaration in
  snd (List.fold_right
    (fun decl (args,l) ->
      match args with
        | a::rest -> (rest, (get_id decl, a)::l)
        | _ -> anomaly (Pp.str "Instance does not match its signature"))
    (evar_filtered_context evi) (Array.rev_to_list args,[]))

(*------------------------------------*
 * functional operations on evar sets *
 *------------------------------------*)

(* [push_rel_context_to_named_context] builds the defining context and the
 * initial instance of an evar. If the evar is to be used in context
 *
 * Gamma =  a1     ...    an xp      ...       x1
 *          \- named part -/ \- de Bruijn part -/
 *
 * then the x1...xp are turned into variables so that the evar is declared in
 * context
 *
 *          a1     ...    an xp      ...       x1
 *          \----------- named part ------------/
 *
 * but used applied to the initial instance "a1 ... an Rel(p) ... Rel(1)"
 * so that ev[a1:=a1 ... an:=an xp:=Rel(p) ... x1:=Rel(1)] is correctly typed
 * in context Gamma.
 *
 * Remark 1: The instance is reverted in practice (i.e. Rel(1) comes first)
 * Remark 2: If some of the ai or xj are definitions, we keep them in the
 *   instance. This is necessary so that no unfolding of local definitions
 *   happens when inferring implicit arguments (consider e.g. the problem
 *   "x:nat; x':=x; f:forall y, y=y -> Prop |- f _ (refl_equal x')" which
 *   produces the equation "?y[x,x']=?y[x,x']" =? "x'=x'": we want
 *   the hole to be instantiated by x', not by x (which would have been
 *   the case in [invert_definition] if x' had disappeared from the instance).
 *   Note that at any time, if, in some context env, the instance of
 *   declaration x:A is t and the instance of definition x':=phi(x) is u, then
 *   we have the property that u and phi(t) are convertible in env.
 *)

let subst2 subst vsubst c =
  substl subst (replace_vars vsubst c)

let push_rel_context_to_named_context env typ =
  (* compute the instances relative to the named context and rel_context *)
  let open Context.Named.Declaration in
  let ids = List.map get_id (named_context env) in
  let inst_vars = List.map mkVar ids in
  let inst_rels = List.rev (rel_list 0 (nb_rel env)) in
  let replace_var_named_declaration id0 id decl =
    let id' = get_id decl in
    let id' = if Id.equal id0 id' then id else id' in
    let vsubst = [id0 , mkVar id] in
    decl |> set_id id' |> map_constr (replace_vars vsubst)
  in
  let replace_var_named_context id0 id  env =
    let nc = Environ.named_context env in
    let nc' = List.map (replace_var_named_declaration id0 id) nc in
    Environ.reset_with_named_context (val_of_named_context nc') env
  in
  let extract_if_neq id = function
    | Anonymous -> None
    | Name id' when id_ord id id' = 0 -> None
    | Name id' -> Some id'
  in
  (* move the rel context to a named context and extend the named instance *)
  (* with vars of the rel context *)
  (* We do keep the instances corresponding to local definition (see above) *)
  let (subst, vsubst, _, env) =
    Context.Rel.fold_outside
      (fun decl (subst, vsubst, avoid, env) ->
        let open Context.Rel.Declaration in
        let na = get_name decl in
	let c = get_value decl in
	let t = get_type decl in
        let open Context.Named.Declaration in
        let id =
          (* ppedrot: we want to infer nicer names for the refine tactic, but
             keeping at the same time backward compatibility in other code
             using this function. For now, we only attempt to preserve the
             old behaviour of Program, but ultimately, one should do something
             about this whole name generation problem. *)
          if Flags.is_program_mode () then next_name_away na avoid
          else next_ident_away (id_of_name_using_hdchar env t na) avoid
        in
        match extract_if_neq id na with
        | Some id0 when not (is_section_variable id0) ->
            (* spiwack: if [id<>id0], rather than introducing a new
               binding named [id], we will keep [id0] (the name given
               by the user) and rename [id0] into [id] in the named
               context. Unless [id] is a section variable. *)
            let subst = List.map (replace_vars [id0,mkVar id]) subst in
            let vsubst = (id0,mkVar id)::vsubst in
            let d = match c with
              | None -> LocalAssum (id0, subst2 subst vsubst t)
              | Some c -> LocalDef (id0, subst2 subst vsubst c, subst2 subst vsubst t)
            in
            let env = replace_var_named_context id0  id env in
            (mkVar id0 :: subst, vsubst, id::avoid, push_named d env)
        | _ ->
            (* spiwack: if [id0] is a section variable renaming it is
               incorrect. We revert to a less robust behaviour where
               the new binder has name [id]. Which amounts to the same
               behaviour than when [id=id0]. *)
            let d = match c with
              | None -> LocalAssum (id, subst2 subst vsubst t)
              | Some c -> LocalDef (id, subst2 subst vsubst c, subst2 subst vsubst t)
            in
	    (mkVar id :: subst, vsubst, id::avoid, push_named d env)
      )
      (rel_context env) ~init:([], [], ids, env) in
  (named_context_val env, subst2 subst vsubst typ, inst_rels@inst_vars, subst, vsubst)

(*------------------------------------*
 * Entry points to define new evars   *
 *------------------------------------*)

let default_source = (Loc.ghost,Evar_kinds.InternalHole)

let restrict_evar evd evk filter candidates =
  let evd = Sigma.to_evar_map evd in
  let evd, evk' = Evd.restrict evk filter ?candidates evd in
  Sigma.Unsafe.of_pair (evk', Evd.declare_future_goal evk' evd)

let new_pure_evar_full evd evi =
  let evd = Sigma.to_evar_map evd in
  let (evd, evk) = Evd.new_evar evd evi in
  let evd = Evd.declare_future_goal evk evd in
  Sigma.Unsafe.of_pair (evk, evd)

let new_pure_evar sign evd ?(src=default_source) ?(filter = Filter.identity) ?candidates ?(store = Store.empty) ?naming ?(principal=false) typ =
  let evd = Sigma.to_evar_map evd in
  let default_naming = Misctypes.IntroAnonymous in
  let naming = Option.default default_naming naming in
  let evi = {
    evar_hyps = sign;
    evar_concl = typ;
    evar_body = Evar_empty;
    evar_filter = filter;
    evar_source = src;
    evar_candidates = candidates;
    evar_extra = store; }
  in
  let (evd, newevk) = Evd.new_evar evd ~naming evi in
  let evd =
    if principal then Evd.declare_principal_goal newevk evd
    else Evd.declare_future_goal newevk evd
  in
  Sigma.Unsafe.of_pair (newevk, evd)

let new_evar_instance sign evd typ ?src ?filter ?candidates ?store ?naming ?principal instance =
  assert (not !Flags.debug ||
            List.distinct (ids_of_named_context (named_context_of_val sign)));
  let Sigma (newevk, evd, p) = new_pure_evar sign evd ?src ?filter ?candidates ?store ?naming ?principal typ in
  Sigma (mkEvar (newevk,Array.of_list instance), evd, p)

(* [new_evar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)
let new_evar env evd ?src ?filter ?candidates ?store ?naming ?principal typ =
  let sign,typ',instance,subst,vsubst = push_rel_context_to_named_context env typ in
  let candidates = Option.map (List.map (subst2 subst vsubst)) candidates in
  let instance =
    match filter with
    | None -> instance
    | Some filter -> Filter.filter_list filter instance in
  new_evar_instance sign evd typ' ?src ?filter ?candidates ?store ?naming ?principal instance

let new_evar_unsafe env evd ?src ?filter ?candidates ?store ?naming ?principal typ =
  let evd = Sigma.Unsafe.of_evar_map evd in
  let Sigma (evk, evd, _) = new_evar env evd ?src ?filter ?candidates ?store ?naming ?principal typ in
  (Sigma.to_evar_map evd, evk)

let new_type_evar env evd ?src ?filter ?naming ?principal rigid =
  let Sigma (s, evd', p) = Sigma.new_sort_variable rigid evd in
  let Sigma (e, evd', q) = new_evar env evd' ?src ?filter ?naming ?principal (mkSort s) in
  Sigma ((e, s), evd', p +> q)

let e_new_type_evar env evdref ?src ?filter ?naming ?principal rigid =
  let sigma = Sigma.Unsafe.of_evar_map !evdref in
  let Sigma (c, sigma, _) = new_type_evar env sigma ?src ?filter ?naming ?principal rigid in
  let sigma = Sigma.to_evar_map sigma in
    evdref := sigma;
    c

let new_Type ?(rigid=Evd.univ_flexible) env evd = 
  let Sigma (s, sigma, p) = Sigma.new_sort_variable rigid evd in
  Sigma (mkSort s, sigma, p)

let e_new_Type ?(rigid=Evd.univ_flexible) env evdref =
  let evd', s = new_sort_variable rigid !evdref in
    evdref := evd'; mkSort s

  (* The same using side-effect *)
let e_new_evar env evdref ?(src=default_source) ?filter ?candidates ?store ?naming ?principal ty =
  let (evd',ev) = new_evar_unsafe env !evdref ~src:src ?filter ?candidates ?store ?naming ?principal ty in
  evdref := evd';
  ev

(* This assumes an evar with identity instance and generalizes it over only
   the De Bruijn part of the context *)
let generalize_evar_over_rels sigma (ev,args) =
  let evi = Evd.find sigma ev in
  let sign = named_context_of_val evi.evar_hyps in
  List.fold_left2
    (fun (c,inst as x) a d ->
      if isRel a then (mkNamedProd_or_LetIn d c,a::inst) else x)
     (evi.evar_concl,[]) (Array.to_list args) sign

(************************************)
(* Removing a dependency in an evar *)
(************************************)

type clear_dependency_error =
| OccurHypInSimpleClause of Id.t option
| EvarTypingBreak of existential

exception ClearDependencyError of Id.t * clear_dependency_error

let cleared = Store.field ()

exception Depends of Id.t

let rec check_and_clear_in_constr env evdref err ids global c =
  (* returns a new constr where all the evars have been 'cleaned'
     (ie the hypotheses ids have been removed from the contexts of
     evars). [global] should be true iff there is some variable of [ids] which
     is a section variable *)
    match kind_of_term c with
      | Var id' ->
      if Id.Set.mem id' ids then raise (ClearDependencyError (id', err)) else c

      | ( Const _ | Ind _ | Construct _ ) ->
        let () = if global then
          let check id' =
            if Id.Set.mem id' ids then
              raise (ClearDependencyError (id',err))
          in
          Id.Set.iter check (Environ.vars_of_global env c)
        in
        c

      | Evar (evk,l as ev) ->
	  if Evd.is_defined !evdref evk then
	    (* If evk is already defined we replace it by its definition *)
	    let nc = whd_evar !evdref c in
	      (check_and_clear_in_constr env evdref err ids global nc)
	  else
	    (* We check for dependencies to elements of ids in the
	       evar_info corresponding to e and in the instance of
	       arguments. Concurrently, we build a new evar
	       corresponding to e where hypotheses of ids have been
	       removed *)
	    let evi = Evd.find_undefined !evdref evk in
	    let ctxt = Evd.evar_filtered_context evi in
	    let (rids,filter) =
              List.fold_right2
                (fun h a (ri,filter) ->
                  try
                  (* Check if some id to clear occurs in the instance
                     a of rid in ev and remember the dependency *)
                    let check id = if Id.Set.mem id ids then raise (Depends id) in
                    let () = Id.Set.iter check (collect_vars a) in
                  (* Check if some rid to clear in the context of ev
                     has dependencies in another hyp of the context of ev
                     and transitively remember the dependency *)
                    let check id _ =
                      if occur_var_in_decl (Global.env ()) id h
                      then raise (Depends id)
                    in
                    let () = Id.Map.iter check ri in
                  (* No dependency at all, we can keep this ev's context hyp *)
                    (ri, true::filter)
                  with Depends id -> let open Context.Named.Declaration in
                                     (Id.Map.add (get_id h) id ri, false::filter))
		ctxt (Array.to_list l) (Id.Map.empty,[]) in
	    (* Check if some rid to clear in the context of ev has dependencies
	       in the type of ev and adjust the source of the dependency *)
	    let _nconcl =
	      try
                let nids = Id.Map.domain rids in
                let global = Id.Set.exists is_section_variable nids in
                check_and_clear_in_constr env evdref (EvarTypingBreak ev) nids global (evar_concl evi)
	      with ClearDependencyError (rid,err) ->
		raise (ClearDependencyError (Id.Map.find rid rids,err)) in

            if Id.Map.is_empty rids then c
            else
              let origfilter = Evd.evar_filter evi in
              let filter = Evd.Filter.apply_subfilter origfilter filter in
              let evd = Sigma.Unsafe.of_evar_map !evdref in
              let Sigma (_, evd, _) = restrict_evar evd evk filter None in
              let evd = Sigma.to_evar_map evd in
              evdref := evd;
	    (* spiwack: hacking session to mark the old [evk] as having been "cleared" *)
	      let evi = Evd.find !evdref evk in
	      let extra = evi.evar_extra in
	      let extra' = Store.set extra cleared true in
	      let evi' = { evi with evar_extra = extra' } in
	      evdref := Evd.add !evdref evk evi' ;
	    (* spiwack: /hacking session *)
              whd_evar !evdref c

      | _ -> map_constr (check_and_clear_in_constr env evdref err ids global) c

let clear_hyps_in_evi_main env evdref hyps terms ids =
  (* clear_hyps_in_evi erases hypotheses ids in hyps, checking if some
     hypothesis does not depend on a element of ids, and erases ids in
     the contexts of the evars occurring in evi *)
  let global = Id.Set.exists is_section_variable ids in
  let terms =
    List.map (check_and_clear_in_constr env evdref (OccurHypInSimpleClause None) ids global) terms in
  let nhyps =
    let open Context.Named.Declaration in
    let check_context decl =
      let err = OccurHypInSimpleClause (Some (get_id decl)) in
      map_constr (check_and_clear_in_constr env evdref err ids global) decl
    in
    let check_value vk = match force_lazy_val vk with
    | None -> vk
    | Some (_, d) ->
      if (Id.Set.for_all (fun e -> not (Id.Set.mem e d)) ids) then
        (* v does depend on any of ids, it's ok *)
        vk
      else
        (* v depends on one of the cleared hyps:
            we forget the computed value *)
        dummy_lazy_val ()
    in
      remove_hyps ids check_context check_value hyps
  in
  (nhyps,terms)

let clear_hyps_in_evi env evdref hyps concl ids =
  match clear_hyps_in_evi_main env evdref hyps [concl] ids with
  | (nhyps,[nconcl]) -> (nhyps,nconcl)
  | _ -> assert false

let clear_hyps2_in_evi env evdref hyps t concl ids =
  match clear_hyps_in_evi_main env evdref hyps [t;concl] ids with
  | (nhyps,[t;nconcl]) -> (nhyps,t,nconcl)
  | _ -> assert false

(* spiwack: a few functions to gather evars on which goals depend. *)
let queue_set q is_dependent set =
  Evar.Set.iter (fun a -> Queue.push (is_dependent,a) q) set
let queue_term q is_dependent c =
  queue_set q is_dependent (evars_of_term c)

let process_dependent_evar q acc evm is_dependent e =
  let evi = Evd.find evm e in
  (* Queues evars appearing in the types of the goal (conclusion, then
     hypotheses), they are all dependent. *)
  queue_term q true evi.evar_concl;
  List.iter begin fun decl ->
    let open Context.Named.Declaration in
    queue_term q true (get_type decl);
    match decl with
    | LocalAssum _ -> ()
    | LocalDef (_,b,_) -> queue_term q true b
  end (Environ.named_context_of_val evi.evar_hyps);
  match evi.evar_body with
  | Evar_empty ->
      if is_dependent then Evar.Map.add e None acc else acc
  | Evar_defined b ->
      let subevars = evars_of_term b in
      (* evars appearing in the definition of an evar [e] are marked
         as dependent when [e] is dependent itself: if [e] is a
         non-dependent goal, then, unless they are reach from another
         path, these evars are just other non-dependent goals. *)
      queue_set q is_dependent subevars;
      if is_dependent then Evar.Map.add e (Some subevars) acc else acc

let gather_dependent_evars q evm =
  let acc = ref Evar.Map.empty in
  while not (Queue.is_empty q) do
    let (is_dependent,e) = Queue.pop q in
    (* checks if [e] has already been added to [!acc] *)
    begin if not (Evar.Map.mem e !acc) then
        acc := process_dependent_evar q !acc evm is_dependent e  
    end
  done;
  !acc

let gather_dependent_evars evm l =
  let q = Queue.create () in
  List.iter (fun a -> Queue.add (false,a) q) l;
  gather_dependent_evars q evm

(* /spiwack *)

(** The following functions return the set of undefined evars
    contained in the object, the defined evars being traversed.
    This is roughly a combination of the previous functions and
    [nf_evar]. *)

let undefined_evars_of_term evd t =
  let rec evrec acc c =
    match kind_of_term c with
      | Evar (n, l) ->
	let acc = Array.fold_left evrec acc l in
	(try match (Evd.find evd n).evar_body with
	  | Evar_empty -> Evar.Set.add n acc
	  | Evar_defined c -> evrec acc c
	 with Not_found -> anomaly ~label:"undefined_evars_of_term" (Pp.str "evar not found"))
      | _ -> fold_constr evrec acc c
  in
  evrec Evar.Set.empty t

let undefined_evars_of_named_context evd nc =
  let open Context.Named.Declaration in
  Context.Named.fold_outside
    (fold (fun c s -> Evar.Set.union s (undefined_evars_of_term evd c)))
    nc
    ~init:Evar.Set.empty

let undefined_evars_of_evar_info evd evi =
  Evar.Set.union (undefined_evars_of_term evd evi.evar_concl)
    (Evar.Set.union
       (match evi.evar_body with
	 | Evar_empty -> Evar.Set.empty
	 | Evar_defined b -> undefined_evars_of_term evd b)
       (undefined_evars_of_named_context evd
	  (named_context_of_val evi.evar_hyps)))

(* spiwack: this is a more complete version of
   {!Termops.occur_evar}. The latter does not look recursively into an
   [evar_map]. If unification only need to check superficially, tactics
   do not have this luxury, and need the more complete version. *)
let occur_evar_upto sigma n c =
  let rec occur_rec c = match kind_of_term c with
    | Evar (sp,_) when Evar.equal sp n -> raise Occur
    | Evar e -> Option.iter occur_rec (existential_opt_value sigma e)
    | _ -> iter_constr occur_rec c
  in
  try occur_rec c; false with Occur -> true

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)

let judge_of_new_Type evd =
  let Sigma (s, evd', p) = Sigma.new_univ_variable univ_rigid evd in
  Sigma ({ uj_val = mkSort (Type s); uj_type = mkSort (Type (Univ.super s)) }, evd', p)

let subterm_source evk (loc,k) =
  let evk = match k with
    | Evar_kinds.SubEvar (evk) -> evk
    | _ -> evk in
  (loc,Evar_kinds.SubEvar evk)


(** Term exploration up to instantiation. *)
let kind_of_term_upto sigma t =
  Constr.kind (whd_evar sigma t)

(** [eq_constr_univs_test sigma1 sigma2 t u] tests equality of [t] and
    [u] up to existential variable instantiation and equalisable
    universes. The term [t] is interpreted in [sigma1] while [u] is
    interpreted in [sigma2]. The universe constraints in [sigma2] are
    assumed to be an extention of those in [sigma1]. *)
let eq_constr_univs_test sigma1 sigma2 t u =
  (* spiwack: mild code duplication with {!Evd.eq_constr_univs}. *)
  let open Evd in
  let fold cstr sigma =
    try Some (add_universe_constraints sigma cstr)
    with Univ.UniverseInconsistency _ | UniversesDiffer -> None
  in
  let ans =
    Universes.eq_constr_univs_infer_with
      (fun t -> kind_of_term_upto sigma1 t)
      (fun u -> kind_of_term_upto sigma2 u)
      (universes sigma2) fold t u sigma2
  in
  match ans with None -> false | Some _ -> true

type type_constraint = types option
type val_constraint = constr option
