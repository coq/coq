(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Pp
open Names
open Term
open Termops
open Namegen
open Pre_env
open Environ
open Evd
open Reductionops
open Pretype_errors
open Retyping

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

let nf_named_context_evar sigma ctx =
  Sign.map_named_context (Reductionops.nf_evar sigma) ctx

let nf_rel_context_evar sigma ctx =
  Sign.map_rel_context (Reductionops.nf_evar sigma) ctx

let nf_env_evar sigma env =
  let nc' = nf_named_context_evar sigma (Environ.named_context env) in
  let rel' = nf_rel_context_evar sigma (Environ.rel_context env) in
    push_rel_context rel' (reset_with_named_context (val_of_named_context nc') env)

let nf_evar_info evc info =
  { info with
    evar_concl = Reductionops.nf_evar evc info.evar_concl;
    evar_hyps = map_named_val (Reductionops.nf_evar evc) info.evar_hyps;
    evar_body = match info.evar_body with
      | Evar_empty -> Evar_empty
      | Evar_defined c -> Evar_defined (Reductionops.nf_evar evc c) }
let nf_evars evm =
  Evd.fold
    (fun ev evi evm' -> Evd.add evm' ev (nf_evar_info evm evi))
    evm Evd.empty

let nf_evars_undefined evm =
  Evd.fold_undefined
    (fun ev evi evm' -> Evd.add evm' ev (nf_evar_info evm evi))
    evm (defined_evars evm)

let nf_evar_map evd = Evd.evars_reset_evd (nf_evars evd) evd
let nf_evar_map_undefined evd = Evd.evars_reset_evd (nf_evars_undefined evd) evd

(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

let has_undefined_evars_or_sorts evd t =
  let rec has_ev t =
    match kind_of_term t with
    | Evar (ev,args) ->
        (match evar_body (Evd.find evd ev) with
        | Evar_defined c ->
            has_ev c; Array.iter has_ev args
        | Evar_empty ->
	    raise NotInstantiatedEvar)
    | Sort s when is_sort_variable evd s -> raise Not_found
    | _ -> iter_constr has_ev t in
  try let _ = has_ev t in false
  with (Not_found | NotInstantiatedEvar) -> true

let is_ground_term evd t =
  not (has_undefined_evars_or_sorts evd t)

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
      | Evar (evk,args as ev) when Evd.is_defined sigma evk
	  -> whrec (existential_value sigma ev, l)
      | Cast (c,_,_) -> whrec (c, l)
      | App (f,args) -> whrec (f, Array.fold_right (fun a l -> a::l) args l)
      | _ -> s
  in
  whrec (c, [])

let whd_head_evar sigma c = applist (whd_head_evar_stack sigma c)

(**********************)
(* Creating new metas *)
(**********************)

(* Generator of metavariables *)
let new_meta =
  let meta_ctr = ref 0 in
  Summary.declare_summary "meta counter"
    { Summary.freeze_function = (fun () -> !meta_ctr);
      Summary.unfreeze_function = (fun n -> meta_ctr := n);
      Summary.init_function = (fun () -> meta_ctr := 0) };
  fun () -> incr meta_ctr; !meta_ctr

let mk_new_meta () = mkMeta(new_meta())

let collect_evars emap c =
  let rec collrec acc c =
    match kind_of_term c with
      | Evar (evk,_) ->
	  if Evd.is_undefined emap evk then evk::acc
	  else (* No recursion on the evar instantiation *) acc
      | _         ->
	  fold_constr collrec acc c in
  List.uniquize (collrec [] c)

let push_dependent_evars sigma emap =
  Evd.fold_undefined (fun ev {evar_concl = ccl} (sigma',emap') ->
    List.fold_left
      (fun (sigma',emap') ev ->
	(Evd.add sigma' ev (Evd.find emap' ev),Evd.remove emap' ev))
      (sigma',emap') (collect_evars emap' ccl))
    emap (sigma,emap)

let push_duplicated_evars sigma emap c =
  let rec collrec (one,(sigma,emap) as acc) c =
    match kind_of_term c with
    | Evar (evk,_) when not (Evd.mem sigma evk) ->
	if List.mem evk one then
	  let sigma' = Evd.add sigma evk (Evd.find emap evk) in
	  let emap' = Evd.remove emap evk in
	  (one,(sigma',emap'))
	else
	  (evk::one,(sigma,emap))
    | _ ->
	fold_constr collrec acc c
  in
  snd (collrec ([],(sigma,emap)) c)

(* replaces a mapping of existentials into a mapping of metas.
   Problem if an evar appears in the type of another one (pops anomaly) *)
let evars_to_metas sigma (emap, c) =
  let emap = nf_evar_map_undefined emap in
  let sigma',emap' = push_dependent_evars sigma emap in
  let sigma',emap' = push_duplicated_evars sigma' emap' c in
  (* if an evar has been instantiated in [emap] (as part of typing [c])
     then it is instantiated in [sigma]. *)
  let repair_evars sigma emap =
    fold_undefined begin fun ev _ sigma' ->
      try
	let info = find emap ev in
	match evar_body info with
	| Evar_empty -> sigma'
	| Evar_defined body -> define ev body sigma'
      with Not_found -> sigma'
    end sigma sigma
  in
  let sigma' = repair_evars sigma' emap in
  let change_exist evar =
    let ty = nf_betaiota emap (existential_type emap evar) in
    let n = new_meta() in
    mkCast (mkMeta n, DEFAULTcast, ty) in
  let rec replace c =
    match kind_of_term c with
      | Evar (evk,_ as ev) when Evd.mem emap' evk -> change_exist ev
      | _ -> map_constr replace c in
  (sigma', replace c)

(* The list of non-instantiated existential declarations (order is important) *)

let non_instantiated sigma =
  let listev = Evd.undefined_list sigma in
  List.map (fun (ev,evi) -> (ev,nf_evar_info sigma evi)) listev

(************************)
(* Manipulating filters *)
(************************)

let extract_subfilter initial_filter refined_filter =
  snd (List.filter2 (fun b1 b2 -> b1) initial_filter refined_filter)

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
  let evar_ctr = ref 0 in
  Summary.declare_summary "evar counter"
    { Summary.freeze_function = (fun () -> !evar_ctr);
      Summary.unfreeze_function = (fun n -> evar_ctr := n);
      Summary.init_function = (fun () -> evar_ctr := 0) };
  fun () -> incr evar_ctr; existential_of_int !evar_ctr

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

let push_rel_context_to_named_context env typ =
  (* compute the instances relative to the named context and rel_context *)
  let ids = List.map pi1 (named_context env) in
  let inst_vars = List.map mkVar ids in
  let inst_rels = List.rev (rel_list 0 (nb_rel env)) in
  (* move the rel context to a named context and extend the named instance *)
  (* with vars of the rel context *)
  (* We do keep the instances corresponding to local definition (see above) *)
  let (subst, _, env) =
    Sign.fold_rel_context
      (fun (na,c,t) (subst, avoid, env) ->
	let id = next_name_away na avoid in
	let d = (id,Option.map (substl subst) c,substl subst t) in
	(mkVar id :: subst, id::avoid, push_named d env))
      (rel_context env) ~init:([], ids, env) in
  (named_context_val env, substl subst typ, inst_rels@inst_vars, subst)

(*------------------------------------*
 * Entry points to define new evars   *
 *------------------------------------*)

let default_source = (Loc.ghost,Evar_kinds.InternalHole)

let new_pure_evar evd sign ?(src=default_source) ?filter ?candidates typ =
  let newevk = new_untyped_evar() in
  let evd = evar_declare sign newevk typ ~src ?filter ?candidates evd in
  (evd,newevk)

let new_evar_instance sign evd typ ?src ?filter ?candidates instance =
  assert (not !Flags.debug ||
            List.distinct (ids_of_named_context (named_context_of_val sign)));
  let evd,newevk = new_pure_evar evd sign ?src ?filter ?candidates typ in
  (evd,mkEvar (newevk,Array.of_list instance))

(* [new_evar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)

let new_evar evd env ?src ?filter ?candidates typ =
  let sign,typ',instance,subst = push_rel_context_to_named_context env typ in
  let candidates = Option.map (List.map (substl subst)) candidates in
  let instance =
    match filter with
    | None -> instance
    | Some filter -> List.filter_with filter instance in
  new_evar_instance sign evd typ' ?src ?filter ?candidates instance

let new_type_evar ?src ?filter evd env =
  let evd', s = new_sort_variable evd in
  new_evar evd' env ?src ?filter (mkSort s)

  (* The same using side-effect *)
let e_new_evar evdref env ?(src=(Loc.ghost,Evar_kinds.InternalHole)) ?filter ?candidates ty =
  let (evd',ev) = new_evar !evdref env ~src:src ?filter ?candidates ty in
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

let rec check_and_clear_in_constr evdref err ids c =
  (* returns a new constr where all the evars have been 'cleaned'
     (ie the hypotheses ids have been removed from the contexts of
     evars) *)
  let check id' =
    if List.mem id' ids then
      raise (ClearDependencyError (id',err))
  in
    match kind_of_term c with
      | Var id' ->
	  check id'; c

      | ( Const _ | Ind _ | Construct _ ) ->
          let vars = Environ.vars_of_global (Global.env()) c in
            List.iter check vars; c

      | Evar (evk,l as ev) ->
	  if Evd.is_defined !evdref evk then
	    (* If evk is already defined we replace it by its definition *)
	    let nc = whd_evar !evdref c in
	      (check_and_clear_in_constr evdref err ids nc)
	  else
	    (* We check for dependencies to elements of ids in the
	       evar_info corresponding to e and in the instance of
	       arguments. Concurrently, we build a new evar
	       corresponding to e where hypotheses of ids have been
	       removed *)
	    let evi = Evd.find_undefined !evdref evk in
	    let ctxt = Evd.evar_filtered_context evi in
	    let (nhyps,nargs,rids) =
	      List.fold_right2
		(fun (rid,ob,c as h) a (hy,ar,ri) ->
		  (* Check if some id to clear occurs in the instance
		     a of rid in ev and remember the dependency *)
		  match
		    List.filter (fun id -> List.mem id ids) (Id.Set.elements (collect_vars a))
		  with
		  | id :: _ -> (hy,ar,(rid,id)::ri)
		  | _ ->
		  (* Check if some rid to clear in the context of ev
		     has dependencies in another hyp of the context of ev
		     and transitively remember the dependency *)
		  match List.filter (fun (id,_) -> occur_var_in_decl (Global.env()) id h) ri with
		  | (_,id') :: _ -> (hy,ar,(rid,id')::ri)
		  | _ ->
		  (* No dependency at all, we can keep this ev's context hyp *)
		      (h::hy,a::ar,ri))
		ctxt (Array.to_list l) ([],[],[]) in
	    (* Check if some rid to clear in the context of ev has dependencies
	       in the type of ev and adjust the source of the dependency *)
	    let nconcl =
	      try check_and_clear_in_constr evdref (EvarTypingBreak ev)
		    (List.map fst rids) (evar_concl evi)
	      with ClearDependencyError (rid,err) ->
		raise (ClearDependencyError (List.assoc rid rids,err)) in

            begin match rids with
            | [] -> c
            | _ ->
	      let env = Sign.fold_named_context push_named nhyps ~init:(empty_env) in
	      let ev'= e_new_evar evdref env ~src:(evar_source evk !evdref) nconcl in
	      evdref := Evd.define evk ev' !evdref;
	      let (evk',_) = destEvar ev' in
	    (* spiwack: hacking session to mark the old [evk] as having been "cleared" *)
	      let evi = Evd.find !evdref evk in
	      let extra = evi.evar_extra in
	      let extra' = Store.set extra cleared true in
	      let evi' = { evi with evar_extra = extra' } in
	      evdref := Evd.add !evdref evk evi' ;
	    (* spiwack: /hacking session *)
	      mkEvar(evk', Array.of_list nargs)
            end

      | _ -> map_constr (check_and_clear_in_constr evdref err ids) c

let clear_hyps_in_evi evdref hyps concl ids =
  (* clear_hyps_in_evi erases hypotheses ids in hyps, checking if some
     hypothesis does not depend on a element of ids, and erases ids in
     the contexts of the evars occuring in evi *)
  let nconcl =
    check_and_clear_in_constr evdref (OccurHypInSimpleClause None) ids concl in
  let nhyps =
    let check_context (id,ob,c) =
      let err = OccurHypInSimpleClause (Some id) in
      (id, Option.map (check_and_clear_in_constr evdref err ids) ob,
	check_and_clear_in_constr evdref err ids c)
    in
    let check_value vk =
      match !vk with
	| VKnone -> vk
	| VKvalue (v,d) ->
	    if (List.for_all (fun e -> not (Id.Set.mem e d)) ids) then
	      (* v does depend on any of ids, it's ok *)
	      vk
	    else
	      (* v depends on one of the cleared hyps: we forget the computed value *)
	      ref VKnone
    in
      remove_hyps ids check_context check_value hyps
  in
  (nhyps,nconcl)


(** The following functions return the set of evars immediately
    contained in the object, including defined evars *)

let evars_of_term c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, l) -> Int.Set.add n (Array.fold_left evrec acc l)
    | _ -> fold_constr evrec acc c
  in
  evrec Int.Set.empty c

(* spiwack: a few functions to gather evars on which goals depend. *)
let queue_set q is_dependent set =
  Int.Set.iter (fun a -> Queue.push (is_dependent,a) q) set
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
      if is_dependent then Int.Map.add e None acc else acc
  | Evar_defined b ->
      let subevars = evars_of_term b in
      (* evars appearing in the definition of an evar [e] are marked
         as dependent when [e] is dependent itself: if [e] is a
         non-dependent goal, then, unless they are reach from another
         path, these evars are just other non-dependent goals. *)
      queue_set q is_dependent subevars;
      if is_dependent then Int.Map.add e (Some subevars) acc else acc

let gather_dependent_evars q evm =
  let acc = ref Int.Map.empty in
  while not (Queue.is_empty q) do
    let (is_dependent,e) = Queue.pop q in
    (* checks if [e] has already been added to [!acc] *)
    begin if not (Int.Map.mem e !acc) then
        acc := process_dependent_evar q !acc evm is_dependent e  
    end
  done;
  !acc

let gather_dependent_evars evm l =
  let q = Queue.create () in
  List.iter (fun a -> Queue.add (false,a) q) l;
  gather_dependent_evars q evm

(* /spiwack *)

let evars_of_named_context nc =
  List.fold_right (fun (_, b, t) s ->
    Option.fold_left (fun s t ->
      Int.Set.union s (evars_of_term t))
      (Int.Set.union s (evars_of_term t)) b)
    nc Int.Set.empty

let evars_of_evar_info evi =
  Int.Set.union (evars_of_term evi.evar_concl)
    (Int.Set.union
	(match evi.evar_body with
	| Evar_empty -> Int.Set.empty
	| Evar_defined b -> evars_of_term b)
	(evars_of_named_context (named_context_of_val evi.evar_hyps)))

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
	  | Evar_empty -> Int.Set.add n acc
	  | Evar_defined c -> evrec acc c
	 with Not_found -> anomaly ~label:"undefined_evars_of_term" (Pp.str "evar not found"))
      | _ -> fold_constr evrec acc c
  in
  evrec Int.Set.empty t

let undefined_evars_of_named_context evd nc =
  List.fold_right (fun (_, b, t) s ->
    Option.fold_left (fun s t ->
      Int.Set.union s (undefined_evars_of_term evd t))
      (Int.Set.union s (undefined_evars_of_term evd t)) b)
    nc Int.Set.empty

let undefined_evars_of_evar_info evd evi =
  Int.Set.union (undefined_evars_of_term evd evi.evar_concl)
    (Int.Set.union
       (match evi.evar_body with
	 | Evar_empty -> Int.Set.empty
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
	      | _ ->
		  let evi = nf_evar_info sigma (Evd.find_undefined sigma evk) in
		    error_unsolvable_implicit loc env sigma evi k None)
      | _ -> iter_constr proc_rec c
  in proc_rec c

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

let idx = Id.of_string "x"

(* Refining an evar to a product *)

let define_pure_evar_as_product evd evk =
  let evi = Evd.find_undefined evd evk in
  let evenv = evar_env evi in
  let id = next_ident_away idx (ids_of_named_context (evar_context evi)) in
  let evd1,dom = new_type_evar evd evenv ~filter:(evar_filter evi) in
  let evd2,rng =
    let newenv = push_named (id, None, dom) evenv in
    let src = evar_source evk evd1 in
    let filter = true::evar_filter evi in
    new_type_evar evd1 newenv ~src ~filter in
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
  let filter = true::evar_filter evi in
  let src = evar_source evk evd1 in
  let evd2,body = new_evar evd1 newenv ~src (subst1 (mkVar id) rng) ~filter in
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

let define_evar_as_sort evd (ev,args) =
  let evd, s = new_sort_variable evd in
    Evd.define ev (mkSort s) evd, s

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)

let judge_of_new_Type evd =
  let evd', s = new_univ_variable evd in
    evd', Typeops.judge_of_type s

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
