(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Pp
open Names
open Term
open Vars
open Context
open Termops
open Namegen
open Pre_env
open Environ
open Evd
open Reductionops
open Pretype_errors

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
  Evd.fresh_global (Global.env()) evd x

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
let nf_evar = Reductionops.nf_evar
let j_nf_evar sigma j =
  { uj_val = nf_evar sigma j.uj_val;
    uj_type = nf_evar sigma j.uj_type }
let j_nf_betaiotaevar sigma j =
  { uj_val = nf_evar sigma j.uj_val;
    uj_type = Reductionops.nf_betaiota sigma j.uj_type }
let jl_nf_evar sigma jl = List.map (j_nf_evar sigma) jl
let jv_nf_betaiotaevar sigma jl =
  Array.map (j_nf_betaiotaevar sigma) jl
let jv_nf_evar sigma = Array.map (j_nf_evar sigma)
let tj_nf_evar sigma {utj_val=v;utj_type=t} =
  {utj_val=nf_evar sigma v;utj_type=t}

let env_nf_evar sigma env =
  process_rel_context
    (fun d e -> push_rel (map_rel_declaration (nf_evar sigma) d) e) env

let env_nf_betaiotaevar sigma env =
  process_rel_context
    (fun d e ->
      push_rel (map_rel_declaration (Reductionops.nf_betaiota sigma) d) e) env

let nf_evars_universes evm =
  Universes.nf_evars_and_universes_opt_subst (Reductionops.safe_evar_value evm) 
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
  Context.map_named_context (nf_evar sigma) ctx

let nf_rel_context_evar sigma ctx =
  Context.map_rel_context (nf_evar sigma) ctx

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
  let is_ground_decl = function
      (_,Some b,_) -> is_ground_term evd b
    | _ -> true in
  List.for_all is_ground_decl (rel_context env) &&
  List.for_all is_ground_decl (named_context env)

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

(* Generator of metavariables *)
let new_meta =
  let meta_ctr = Summary.ref 0 ~name:"meta counter" in
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
  snd (List.fold_right
    (fun (id,b,c) (args,l) ->
      match args with
        | a::rest -> (rest, (id,a)::l)
        | _ -> anomaly (Pp.str "Instance does not match its signature"))
    (evar_filtered_context evi) (Array.rev_to_list args,[]))

(**********************)
(* Creating new evars *)
(**********************)

(* Generator of existential names *)
let new_untyped_evar =
  let evar_ctr = Summary.ref 0 ~name:"evar counter" in
  fun () -> incr evar_ctr; Evar.unsafe_of_int !evar_ctr

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
  let ids = List.map pi1 (named_context env) in
  let inst_vars = List.map mkVar ids in
  let inst_rels = List.rev (rel_list 0 (nb_rel env)) in
  let replace_var_named_declaration id0 id (id',b,t) =
    let id' = if Id.equal id0 id' then id else id' in
    let vsubst = [id0 , mkVar id] in
    let b = match b with
    | None -> None
    | Some c -> Some (replace_vars vsubst c)
    in
    id', b, replace_vars vsubst t
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
    Context.fold_rel_context
      (fun (na,c,t) (subst, vsubst, avoid, env) ->
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
            let d = (id0, Option.map (subst2 subst vsubst) c, subst2 subst vsubst t) in
            let env = replace_var_named_context id0  id env in
            (mkVar id0 :: subst, vsubst, id::avoid, push_named d env)
        | _ ->
            (* spiwack: if [id0] is a section variable renaming it is
               incorrect. We revert to a less robust behaviour where
               the new binder has name [id]. Which amounts to the same
               behaviour than when [id=id0]. *)
	    let d = (id,Option.map (subst2 subst vsubst) c,subst2 subst vsubst t) in
	    (mkVar id :: subst, vsubst, id::avoid, push_named d env)
      )
      (rel_context env) ~init:([], [], ids, env) in
  (named_context_val env, subst2 subst vsubst typ, inst_rels@inst_vars, subst, vsubst)

(*------------------------------------*
 * Entry points to define new evars   *
 *------------------------------------*)

let default_source = (Loc.ghost,Evar_kinds.InternalHole)

let restrict_evar evd evk filter candidates =
  let evk' = new_untyped_evar () in
  let evd = Evd.restrict evk evk' filter ?candidates evd in
  Evd.declare_future_goal evk' evd, evk'

let new_pure_evar_full evd evi =
  let evk = new_untyped_evar () in
  let evd = Evd.add evd evk evi in
  let evd = Evd.declare_future_goal evk evd in
  (evd, evk)

let new_pure_evar sign evd ?(src=default_source) ?filter ?candidates ?store ?naming ?(principal=false) typ =
  let default_naming =
    if principal then
        (* waiting for a more principled approach
           (unnamed evars, private names?) *)
        Misctypes.IntroFresh (Names.Id.of_string "tmp_goal")
      else
        Misctypes.IntroAnonymous
  in
  let naming = Option.default default_naming naming in
  let newevk = new_untyped_evar() in
  let evd = evar_declare sign newevk typ ~src ?filter ?candidates ?store ~naming evd in
  let evd =
    if principal then Evd.declare_principal_goal newevk evd
    else Evd.declare_future_goal newevk evd
  in
  (evd,newevk)

let new_evar_instance sign evd typ ?src ?filter ?candidates ?store ?naming ?principal instance =
  assert (not !Flags.debug ||
            List.distinct (ids_of_named_context (named_context_of_val sign)));
  let evd,newevk = new_pure_evar sign evd ?src ?filter ?candidates ?store ?naming ?principal typ in
  (evd,mkEvar (newevk,Array.of_list instance))

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

let new_type_evar env evd ?src ?filter ?naming ?principal rigid =
  let evd', s = new_sort_variable rigid evd in
  let evd', e = new_evar env evd' ?src ?filter ?naming ?principal (mkSort s) in
    evd', (e, s)

let e_new_type_evar env evdref ?src ?filter ?naming ?principal rigid =
  let evd', c = new_type_evar env !evdref ?src ?filter ?naming ?principal rigid in
    evdref := evd';
    c

let new_Type ?(rigid=Evd.univ_flexible) env evd = 
  let evd', s = new_sort_variable rigid evd in
    evd', mkSort s

let e_new_Type ?(rigid=Evd.univ_flexible) env evdref =
  let evd', s = new_sort_variable rigid !evdref in
    evdref := evd'; mkSort s

  (* The same using side-effect *)
let e_new_evar env evdref ?(src=default_source) ?filter ?candidates ?store ?naming ?principal ty =
  let (evd',ev) = new_evar env !evdref ~src:src ?filter ?candidates ?store ?naming ?principal ty in
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

let rec check_and_clear_in_constr env evdref err ids c =
  (* returns a new constr where all the evars have been 'cleaned'
     (ie the hypotheses ids have been removed from the contexts of
     evars) *)
  let check id' =
    if Id.Set.mem id' ids then
      raise (ClearDependencyError (id',err))
  in
    match kind_of_term c with
      | Var id' ->
	  check id'; c

      | ( Const _ | Ind _ | Construct _ ) ->
          let vars = Environ.vars_of_global env c in
            Id.Set.iter check vars; c

      | Evar (evk,l as ev) ->
	  if Evd.is_defined !evdref evk then
	    (* If evk is already defined we replace it by its definition *)
	    let nc = whd_evar !evdref c in
	      (check_and_clear_in_constr env evdref err ids nc)
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
                (fun (rid, ob,c as h) a (ri,filter) ->
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
                  with Depends id -> (Id.Map.add rid id ri, false::filter))
		ctxt (Array.to_list l) (Id.Map.empty,[]) in
	    (* Check if some rid to clear in the context of ev has dependencies
	       in the type of ev and adjust the source of the dependency *)
	    let _nconcl =
	      try
                let nids = Id.Map.domain rids in
                check_and_clear_in_constr env evdref (EvarTypingBreak ev) nids (evar_concl evi)
	      with ClearDependencyError (rid,err) ->
		raise (ClearDependencyError (Id.Map.find rid rids,err)) in

            if Id.Map.is_empty rids then c
            else
              let origfilter = Evd.evar_filter evi in
              let filter = Evd.Filter.apply_subfilter origfilter filter in
              let evd,_ = restrict_evar !evdref evk filter None in
              evdref := evd;
	    (* spiwack: hacking session to mark the old [evk] as having been "cleared" *)
	      let evi = Evd.find !evdref evk in
	      let extra = evi.evar_extra in
	      let extra' = Store.set extra cleared true in
	      let evi' = { evi with evar_extra = extra' } in
	      evdref := Evd.add !evdref evk evi' ;
	    (* spiwack: /hacking session *)
              whd_evar !evdref c

      | _ -> map_constr (check_and_clear_in_constr env evdref err ids) c

let clear_hyps_in_evi_main env evdref hyps terms ids =
  (* clear_hyps_in_evi erases hypotheses ids in hyps, checking if some
     hypothesis does not depend on a element of ids, and erases ids in
     the contexts of the evars occuring in evi *)
  let terms =
    List.map (check_and_clear_in_constr env evdref (OccurHypInSimpleClause None) ids) terms in
  let nhyps =
    let check_context ((id,ob,c) as decl) =
      let err = OccurHypInSimpleClause (Some id) in
      let ob' = Option.smartmap (fun c -> check_and_clear_in_constr env evdref err ids c) ob in
      let c' = check_and_clear_in_constr env evdref err ids c in
      if ob == ob' && c == c' then decl else (id, ob', c')
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
  List.iter begin fun (_,b,t) ->
    queue_term q true t;
    match b with
    | None -> ()
    | Some b -> queue_term q true b
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
  List.fold_right (fun (_, b, t) s ->
    Option.fold_left (fun s t ->
      Evar.Set.union s (undefined_evars_of_term evd t))
      (Evar.Set.union s (undefined_evars_of_term evd t)) b)
    nc Evar.Set.empty

let undefined_evars_of_evar_info evd evi =
  Evar.Set.union (undefined_evars_of_term evd evi.evar_concl)
    (Evar.Set.union
       (match evi.evar_body with
	 | Evar_empty -> Evar.Set.empty
	 | Evar_defined b -> undefined_evars_of_term evd b)
       (undefined_evars_of_named_context evd
	  (named_context_of_val evi.evar_hyps)))

(* [check_evars] fails if some unresolved evar remains *)

let check_evars env initial_sigma sigma c =
  let rec proc_rec c =
    match kind_of_term c with
    | Evar (evk,_ as ev) ->
        (match existential_opt_value sigma ev with
        | Some c -> proc_rec c
        | None ->
	  if not (Evd.mem initial_sigma evk) then
            let (loc,k) = evar_source evk sigma in
	      match k with
	      | Evar_kinds.ImplicitArg (gr, (i, id), false) -> ()
	      | _ -> error_unsolvable_implicit loc env sigma evk None)
      | _ -> iter_constr proc_rec c
  in proc_rec c

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


(****************************************)
(* Operations on value/type constraints *)
(****************************************)

type type_constraint = types option

type val_constraint = constr option

(* Old comment...
 * Basically, we have the following kind of constraints (in increasing
 * strength order):
 *   (false,(None,None)) -> no constraint at all
 *   (true,(None,None))  -> we must build a judgement which _TYPE is a kind
 *   (_,(None,Some ty))  -> we must build a judgement which _TYPE is ty
 *   (_,(Some v,_))      -> we must build a judgement which _VAL is v
 * Maybe a concrete datatype would be easier to understand.
 * We differentiate (true,(None,None)) from (_,(None,Some Type))
 * because otherwise Case(s) would be misled, as in
 * (n:nat) Case n of bool [_]nat end  would infer the predicate Type instead
 * of Set.
 *)

(* The empty type constraint *)
let empty_tycon = None

(* Builds a type constraint *)
let mk_tycon ty = Some ty

(* Constrains the value of a type *)
let empty_valcon = None

(* Builds a value constraint *)
let mk_valcon c = Some c

let idx = Namegen.default_dependent_ident

(* Refining an evar to a product *)

let define_pure_evar_as_product evd evk =
  let evi = Evd.find_undefined evd evk in
  let evenv = evar_env evi in
  let id = next_ident_away idx (ids_of_named_context (evar_context evi)) in
  let concl = whd_evar evd evi.evar_concl in
  let s = destSort concl in
  let evd1,(dom,u1) = new_type_evar evenv evd univ_flexible_alg ~filter:(evar_filter evi) in
  let evd2,rng =
    let newenv = push_named (id, None, dom) evenv in
    let src = evar_source evk evd1 in
    let filter = Filter.extend 1 (evar_filter evi) in
      if is_prop_sort s then
       (* Impredicative product, conclusion must fall in [Prop]. *)
        new_evar newenv evd1 concl ~src ~filter
      else
	let evd3, (rng, srng) =
	  new_type_evar newenv evd1 univ_flexible_alg ~src ~filter in
	let prods = Univ.sup (univ_of_sort u1) (univ_of_sort srng) in
	let evd3 = Evd.set_leq_sort evenv evd3 (Type prods) s in
	  evd3, rng
  in
  let prod = mkProd (Name id, dom, subst_var id rng) in
  let evd3 = Evd.define evk prod evd2 in
    evd3,prod

(* Refine an applied evar to a product and returns its instantiation *)

let define_evar_as_product evd (evk,args) =
  let evd,prod = define_pure_evar_as_product evd evk in
  (* Quick way to compute the instantiation of evk with args *)
  let na,dom,rng = destProd prod in
  let evdom = mkEvar (fst (destEvar dom), args) in
  let evrngargs = Array.cons (mkRel 1) (Array.map (lift 1) args) in
  let evrng =  mkEvar (fst (destEvar rng), evrngargs) in
  evd,mkProd (na, evdom, evrng)

(* Refine an evar with an abstraction

   I.e., solve x1..xq |- ?e:T(x1..xq) with e:=λy:A.?e'[x1..xq,y] where:
   - either T(x1..xq) = πy:A(x1..xq).B(x1..xq,y)
     or T(x1..xq) = ?d[x1..xq] and we define ?d := πy:?A.?B
        with x1..xq |- ?A:Type and x1..xq,y |- ?B:Type
   - x1..xq,y:A |- ?e':B
*)

let define_pure_evar_as_lambda env evd evk =
  let evi = Evd.find_undefined evd evk in
  let evenv = evar_env evi in
  let typ = whd_betadeltaiota env evd (evar_concl evi) in
  let evd1,(na,dom,rng) = match kind_of_term typ with
  | Prod (na,dom,rng) -> (evd,(na,dom,rng))
  | Evar ev' -> let evd,typ = define_evar_as_product evd ev' in evd,destProd typ
  | _ -> error_not_product_loc Loc.ghost env evd typ in
  let avoid = ids_of_named_context (evar_context evi) in
  let id =
    next_name_away_with_default_using_types "x" na avoid (whd_evar evd dom) in
  let newenv = push_named (id, None, dom) evenv in
  let filter = Filter.extend 1 (evar_filter evi) in
  let src = evar_source evk evd1 in
  let evd2,body = new_evar newenv evd1 ~src (subst1 (mkVar id) rng) ~filter in
  let lam = mkLambda (Name id, dom, subst_var id body) in
  Evd.define evk lam evd2, lam

let define_evar_as_lambda env evd (evk,args) =
  let evd,lam = define_pure_evar_as_lambda env evd evk in
  (* Quick way to compute the instantiation of evk with args *)
  let na,dom,body = destLambda lam in
  let evbodyargs = Array.cons (mkRel 1) (Array.map (lift 1) args) in
  let evbody = mkEvar (fst (destEvar body), evbodyargs) in
  evd,mkLambda (na, dom, evbody)

let rec evar_absorb_arguments env evd (evk,args as ev) = function
  | [] -> evd,ev
  | a::l ->
      (* TODO: optimize and avoid introducing intermediate evars *)
      let evd,lam = define_pure_evar_as_lambda env evd evk in
      let _,_,body = destLambda lam in
      let evk = fst (destEvar body) in
      evar_absorb_arguments env evd (evk, Array.cons a args) l

(* Refining an evar to a sort *)

let define_evar_as_sort env evd (ev,args) =
  let evd, u = new_univ_variable univ_rigid evd in
  let evi = Evd.find_undefined evd ev in 
  let s = Type u in
  let evd' = Evd.define ev (mkSort s) evd in
    Evd.set_leq_sort env evd' (Type (Univ.super u)) (destSort evi.evar_concl), s

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)

let judge_of_new_Type evd =
  let evd', s = new_univ_variable univ_rigid evd in
    evd', { uj_val = mkSort (Type s); uj_type = mkSort (Type (Univ.super s)) }

(* Propagation of constraints through application and abstraction:
   Given a type constraint on a functional term, returns the type
   constraint on its domain and codomain. If the input constraint is
   an evar instantiate it with the product of 2 new evars. *)

let split_tycon loc env evd tycon =
  let rec real_split evd c =
    let t = whd_betadeltaiota env evd c in
      match kind_of_term t with
	| Prod (na,dom,rng) -> evd, (na, dom, rng)
	| Evar ev (* ev is undefined because of whd_betadeltaiota *) ->
	    let (evd',prod) = define_evar_as_product evd ev in
	    let (_,dom,rng) = destProd prod in
	      evd',(Anonymous, dom, rng)
	| App (c,args) when isEvar c ->
	    let (evd',lam) = define_evar_as_lambda env evd (destEvar c) in
	    real_split evd' (mkApp (lam,args))
	| _ -> error_not_product_loc loc env evd c
  in
    match tycon with
      | None -> evd,(Anonymous,None,None)
      | Some c ->
	  let evd', (n, dom, rng) = real_split evd c in
	    evd', (n, mk_tycon dom, mk_tycon rng)

let valcon_of_tycon x = x
let lift_tycon n = Option.map (lift n)

let pr_tycon env = function
    None -> str "None"
  | Some t -> Termops.print_constr_env env t

let subterm_source evk (loc,k) =
  let evk = match k with
    | Evar_kinds.SubEvar (evk) -> evk
    | _ -> evk in
  (loc,Evar_kinds.SubEvar evk)
