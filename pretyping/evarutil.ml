(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Pp
open Names
open Univ
open Term
open Termops
open Namegen
open Sign
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

let nf_evar = Pretype_errors.nf_evar
let j_nf_evar = Pretype_errors.j_nf_evar
let jl_nf_evar = Pretype_errors.jl_nf_evar
let jv_nf_evar = Pretype_errors.jv_nf_evar
let tj_nf_evar = Pretype_errors.tj_nf_evar

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
let is_ground_env = memo1_2 is_ground_env

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

let noccur_evar evd evk c =
  let rec occur_rec c = match kind_of_term c with
  | Evar (evk',_ as ev') ->
      (match safe_evar_value evd ev' with
       | Some c -> occur_rec c
       | None -> if evk = evk' then raise Occur)
  | _ -> iter_constr occur_rec c
  in
  try occur_rec c; true with Occur -> false

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
  list_uniquize (collrec [] c)

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

let apply_subfilter filter subfilter =
  fst (List.fold_right (fun oldb (l,filter) ->
    if oldb then List.hd filter::l,List.tl filter else (false::l,filter))
         filter ([], List.rev subfilter))

let extract_subfilter initial_filter refined_filter =
  snd (list_filter2 (fun b1 b2 -> b1) (initial_filter,refined_filter))

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

let default_source = (dummy_loc,InternalHole)

let new_pure_evar evd sign ?(src=default_source) ?filter ?candidates typ =
  let newevk = new_untyped_evar() in
  let evd = evar_declare sign newevk typ ~src ?filter ?candidates evd in
  (evd,newevk)

let new_evar_instance sign evd typ ?src ?filter ?candidates instance =
  assert (not !Flags.debug ||
            list_distinct (ids_of_named_context (named_context_of_val sign)));
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
    | Some filter -> list_filter_with filter instance in
  new_evar_instance sign evd typ' ?src ?filter ?candidates instance

let new_type_evar ?src ?filter evd env =
  let evd', s = new_sort_variable evd in
  new_evar evd' env ?src ?filter (mkSort s)

  (* The same using side-effect *)
let e_new_evar evdref env ?(src=(dummy_loc,InternalHole)) ?filter ?candidates ty =
  let (evd',ev) = new_evar !evdref env ~src:src ?filter ?candidates ty in
  evdref := evd';
  ev

(*------------------------------------*
 * Restricting existing evars         *
 *------------------------------------*)

let restrict_evar_key evd evk filter candidates =
  if filter = None && candidates = None then
    evd,evk
  else
    let evi = Evd.find_undefined evd evk in
    let oldfilter = evar_filter evi in
    if filter = Some oldfilter && candidates = None then
      evd,evk
    else
    let filter =
      match filter with
      | None -> evar_filter evi
      | Some filter -> filter in
    let candidates =
      match candidates with None -> evi.evar_candidates | _ -> candidates in
    let ccl = evi.evar_concl in
    let sign = evar_hyps evi in
    let src = evi.evar_source in
    let evd,newevk = new_pure_evar evd sign ccl ~src ~filter ?candidates in
    let ctxt = snd (list_filter2 (fun b c -> b) (filter,evar_context evi)) in
    let id_inst = Array.of_list (List.map (fun (id,_,_) -> mkVar id) ctxt) in
    Evd.define evk (mkEvar(newevk,id_inst)) evd,newevk

(* Restrict an applied evar and returns its restriction in the same context *)
let restrict_applied_evar evd (evk,argsv) filter candidates =
  let evd,newevk = restrict_evar_key evd evk filter candidates in
  let newargsv = match filter with
  | None -> (* optim *) argsv
  | Some filter ->
      let evi = Evd.find evd evk in
      let subfilter = extract_subfilter (evar_filter evi) filter in
      array_filter_with subfilter argsv in
  evd,(newevk,newargsv)

(* Restrict an evar in the current evar_map *)
let restrict_evar evd evk filter candidates =
  fst (restrict_evar_key evd evk filter candidates)

(* Restrict an evar in the current evar_map *)
let restrict_instance evd evk filter argsv =
  match filter with None -> argsv | Some filter ->
  let evi = Evd.find evd evk in
  array_filter_with (extract_subfilter (evar_filter evi) filter) argsv

(* This assumes an evar with identity instance and generalizes it over only
   the De Bruijn part of the context *)
let generalize_evar_over_rels sigma (ev,args) =
  let evi = Evd.find sigma ev in
  let sign = named_context_of_val evi.evar_hyps in
  List.fold_left2
    (fun (c,inst as x) a d ->
      if isRel a then (mkNamedProd_or_LetIn d c,a::inst) else x)
     (evi.evar_concl,[]) (Array.to_list args) sign

(***************************************)
(* Managing chains of local definitons *)
(***************************************)

(* Expand rels and vars that are bound to other rels or vars so that
   dependencies in variables are canonically associated to the most ancient
   variable in its family of aliased variables *)

let compute_var_aliases sign =
  List.fold_right (fun (id,b,c) aliases ->
    match b with
    | Some t ->
        (match kind_of_term t with
        | Var id' ->
            let aliases_of_id =
              try Idmap.find id' aliases with Not_found -> [] in
            Idmap.add id (aliases_of_id@[t]) aliases
	| _ ->
            Idmap.add id [t] aliases)
    | None -> aliases)
    sign Idmap.empty

let compute_rel_aliases var_aliases rels =
  snd (List.fold_right (fun (_,b,t) (n,aliases) ->
    (n-1,
     match b with
     | Some t ->
         (match kind_of_term t with
         | Var id' ->
             let aliases_of_n =
               try Idmap.find id' var_aliases with Not_found -> [] in
             Intmap.add n (aliases_of_n@[t]) aliases
         | Rel p ->
             let aliases_of_n =
               try Intmap.find (p+n) aliases with Not_found -> [] in
             Intmap.add n (aliases_of_n@[mkRel (p+n)]) aliases
         | _ ->
             Intmap.add n [lift n t] aliases)
     | None -> aliases))
         rels (List.length rels,Intmap.empty))

let make_alias_map env =
  (* We compute the chain of aliases for each var and rel *)
  let var_aliases = compute_var_aliases (named_context env) in
  let rel_aliases = compute_rel_aliases var_aliases (rel_context env) in
  (var_aliases,rel_aliases)

let lift_aliases n (var_aliases,rel_aliases as aliases) =
  if n = 0 then aliases else
  (var_aliases,
   Intmap.fold (fun p l -> Intmap.add (p+n) (List.map (lift n) l))
     rel_aliases Intmap.empty)

let get_alias_chain_of aliases x = match kind_of_term x with
  | Rel n -> (try Intmap.find n (snd aliases) with Not_found -> [])
  | Var id -> (try Idmap.find id (fst aliases) with Not_found -> [])
  | _ -> []

let normalize_alias_opt aliases x =
  match get_alias_chain_of aliases x with
  | []  -> None
  | a::_ when isRel a or isVar a -> Some a
  | [_] -> None
  | _::a::_ -> Some a

let normalize_alias aliases x =
  match normalize_alias_opt aliases x with
  | Some a -> a
  | None -> x

let normalize_alias_var var_aliases id =
  destVar (normalize_alias (var_aliases,Intmap.empty) (mkVar id))

let extend_alias (_,b,_) (var_aliases,rel_aliases) =
  let rel_aliases =
    Intmap.fold (fun n l -> Intmap.add (n+1) (List.map (lift 1) l))
      rel_aliases Intmap.empty in
  let rel_aliases =
    match b with
    | Some t ->
        (match kind_of_term t with
        | Var id' ->
            let aliases_of_binder =
              try Idmap.find id' var_aliases with Not_found -> [] in
	    Intmap.add 1 (aliases_of_binder@[t]) rel_aliases
        | Rel p ->
            let aliases_of_binder =
              try Intmap.find (p+1) rel_aliases with Not_found -> [] in
	    Intmap.add 1 (aliases_of_binder@[mkRel (p+1)]) rel_aliases
        | _ ->
            Intmap.add 1 [lift 1 t] rel_aliases)
    | None -> rel_aliases in
  (var_aliases, rel_aliases)

let expand_alias_once aliases x =
  match get_alias_chain_of aliases x with
  | []  -> None
  | l -> Some (list_last l)

let rec expansions_of_var aliases x =
  match get_alias_chain_of aliases x with
  | [] -> [x]
  | a::_ as l when isRel a || isVar a -> x :: List.rev l
  | _::l -> x :: List.rev l

let expansion_of_var aliases x =
  match get_alias_chain_of aliases x with
  | [] -> x
  | a::_ -> a

let rec expand_vars_in_term_using aliases t = match kind_of_term t with
  | Rel _ | Var _ ->
      normalize_alias aliases t
  | _ ->
      map_constr_with_full_binders
	extend_alias expand_vars_in_term_using aliases t

let expand_vars_in_term env = expand_vars_in_term_using (make_alias_map env)

let free_vars_and_rels_up_alias_expansion aliases c =
  let acc1 = ref Intset.empty and acc2 = ref Idset.empty in
  let cache_rel = ref Intset.empty and cache_var = ref Idset.empty in
  let is_in_cache depth = function
    | Rel n -> Intset.mem (n-depth) !cache_rel
    | Var s -> Idset.mem s !cache_var
    | _ -> false in
  let put_in_cache depth = function
    | Rel n -> cache_rel := Intset.add (n-depth) !cache_rel
    | Var s -> cache_var := Idset.add s !cache_var
    | _ -> () in
  let rec frec (aliases,depth) c =
    match kind_of_term c with
    | Rel _ | Var _ as ck ->
      if is_in_cache depth ck then () else begin
      put_in_cache depth ck;
      let c = expansion_of_var aliases c in
        match kind_of_term c with
        | Var id -> acc2 := Idset.add id !acc2
        | Rel n -> if n >= depth+1 then acc1 := Intset.add (n-depth) !acc1
        | _ -> frec (aliases,depth) c end
    | Const _ | Ind _ | Construct _ ->
        acc2 := List.fold_right Idset.add (vars_of_global (Global.env()) c) !acc2
    | _ ->
        iter_constr_with_full_binders
          (fun d (aliases,depth) -> (extend_alias d aliases,depth+1))
          frec (aliases,depth) c
  in
  frec (aliases,0) c;
  (!acc1,!acc2)

(************************************)
(* Removing a dependency in an evar *)
(************************************)

type clear_dependency_error =
| OccurHypInSimpleClause of identifier option
| EvarTypingBreak of existential

exception ClearDependencyError of identifier * clear_dependency_error

open Store.Field

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
		    List.filter (fun id -> List.mem id ids) (Idset.elements (collect_vars a))
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

            if rids = [] then c else begin
	      let env = Sign.fold_named_context push_named nhyps ~init:(empty_env) in
	      let ev'= e_new_evar evdref env ~src:(evar_source evk !evdref) nconcl in
	      evdref := Evd.define evk ev' !evdref;
	      let (evk',_) = destEvar ev' in
	    (* spiwack: hacking session to mark the old [evk] as having been "cleared" *)
	      let evi = Evd.find !evdref evk in
	      let extra = evi.evar_extra in
	      let extra' = cleared.set true extra in
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
	    if (List.for_all (fun e -> not (Idset.mem e d)) ids) then
	      (* v does depend on any of ids, it's ok *)
	      vk
	    else
	      (* v depends on one of the cleared hyps: we forget the computed value *)
	      ref VKnone
    in
      remove_hyps ids check_context check_value hyps
  in
  (nhyps,nconcl)

(********************************)
(* Managing pattern-unification *)
(********************************)

let rec expand_and_check_vars aliases = function
  | [] -> []
  | a::l when isRel a or isVar a ->
      let a = expansion_of_var aliases a in
      if isRel a or isVar a then a :: expand_and_check_vars aliases l
      else raise Exit
  | _ ->
      raise Exit

module Constrhash = Hashtbl.Make
  (struct type t = constr
	  let equal = eq_constr
	  let hash = hash_constr
   end)

let rec constr_list_distinct l =
  let visited = Constrhash.create 23 in
  let rec loop = function
    | h::t ->
	if Constrhash.mem visited h then false
	else (Constrhash.add visited h h; loop t)
    | [] -> true
  in loop l

let get_actual_deps aliases l t =
  if occur_meta_or_existential t then
    (* Probably no restrictions on allowed vars in presence of evars *)
    l
  else
    (* Probably strong restrictions coming from t being evar-closed *)
    let (fv_rels,fv_ids) = free_vars_and_rels_up_alias_expansion aliases t in
    List.filter (fun c ->
      match kind_of_term c with
      | Var id -> Idset.mem id fv_ids
      | Rel n -> Intset.mem n fv_rels
      | _ -> assert false) l

let remove_instance_local_defs evd evk args =
  let evi = Evd.find evd evk in
  let rec aux = function
  | (_,Some _,_)::sign, a::args -> aux (sign,args)
  | (_,None,_)::sign, a::args -> a::aux (sign,args)
  | [], [] -> []
  | _ -> assert false in
  aux (evar_filtered_context evi, args)

(* Check if an applied evar "?X[args] l" is a Miller's pattern *)

let find_unification_pattern_args env l t =
  if List.for_all (fun x -> isRel x || isVar x) l (* common failure case *) then
    let aliases = make_alias_map env in
    match (try Some (expand_and_check_vars aliases l) with Exit -> None) with
    | Some l as x when constr_list_distinct (get_actual_deps aliases l t) -> x
    | _ -> None
  else
    None

let is_unification_pattern_meta env nb m l t =
  (* Variables from context and rels > nb are implicitly all there *)
  (* so we need to be a rel <= nb *)
  if List.for_all (fun x -> isRel x && destRel x <= nb) l then
    match find_unification_pattern_args env l t with
    | Some _ as x when not (dependent (mkMeta m) t) -> x
    | _ -> None
  else
    None

let is_unification_pattern_evar env evd (evk,args) l t =
  if List.for_all (fun x -> isRel x || isVar x) l & noccur_evar evd evk t then
    let args = remove_instance_local_defs evd evk (Array.to_list args) in
    let n = List.length args in
    match find_unification_pattern_args env (args @ l) t with
    | Some l -> Some (list_skipn n l)
    | _ -> None
  else
    None

let is_unification_pattern_pure_evar env evd (evk,args) t =
  is_unification_pattern_evar env evd (evk,args) [] t <> None

let is_unification_pattern (env,nb) evd f l t =
  match kind_of_term f with
  | Meta m -> is_unification_pattern_meta env nb m l t
  | Evar ev -> is_unification_pattern_evar env evd ev l t
  | _ -> None

(* From a unification problem "?X l = c", build "\x1...xn.(term1 l2)"
   (pattern unification). It is assumed that l is made of rel's that
   are distinct and not bound to aliases. *)
(* It is also assumed that c does not contain metas because metas
   *implicitly* depend on Vars but lambda abstraction will not reflect this
   dependency: ?X x = ?1 (?1 is a meta) will return \_.?1 while it should
   return \y. ?1{x\y} (non constant function if ?1 depends on x) (BB) *)
let solve_pattern_eqn env l c =
  let c' = List.fold_right (fun a c ->
    let c' = subst_term (lift 1 a) (lift 1 c) in
    match kind_of_term a with
      (* Rem: if [a] links to a let-in, do as if it were an assumption *)
      | Rel n ->
          let d = map_rel_declaration (lift n) (lookup_rel n env) in
          mkLambda_or_LetIn d c'
      | Var id ->
          let d = lookup_named id env in mkNamedLambda_or_LetIn d c'
      | _ -> assert false)
    l c in
  (* Warning: we may miss some opportunity to eta-reduce more since c'
     is not in normal form *)
  whd_eta c'

(*****************************************)
(* Refining/solving unification problems *)
(*****************************************)

(* Knowing that [Gamma |- ev : T] and that [ev] is applied to [args],
 * [make_projectable_subst ev args] builds the substitution [Gamma:=args].
 * If a variable and an alias of it are bound to the same instance, we skip
 * the alias (we just use eq_constr -- instead of conv --, since anyway,
 * only instances that are variables -- or evars -- are later considered;
 * morever, we can bet that similar instances came at some time from
 * the very same substitution. The removal of aliased duplicates is
 * useful to ensure the uniqueness of a projection.
*)

let make_projectable_subst aliases sigma evi args =
  let sign = evar_filtered_context evi in
  let evar_aliases = compute_var_aliases sign in
  let (_,full_subst,cstr_subst) =
    List.fold_right
      (fun (id,b,c) (args,all,cstrs) ->
        match b,args with
	| None, a::rest ->
	    let a = whd_evar sigma a in
	    let cstrs =
	      let a',args = decompose_app_vect a in
	      match kind_of_term a' with
	      | Construct cstr ->
		  let l = try Constrmap.find cstr cstrs with Not_found -> [] in
		  Constrmap.add cstr ((args,id)::l) cstrs
	      | _ -> cstrs in
	    (rest,Idmap.add id [a,normalize_alias_opt aliases a,id] all,cstrs)
	| Some c, a::rest ->
	    let a = whd_evar sigma a in
	    (match kind_of_term c with
	    | Var id' ->
		let idc = normalize_alias_var evar_aliases id' in
		let sub = try Idmap.find idc all with Not_found -> [] in
		if List.exists (fun (c,_,_) -> eq_constr a c) sub then
		  (rest,all,cstrs)
		else
		  (rest,
		   Idmap.add idc ((a,normalize_alias_opt aliases a,id)::sub) all,
		   cstrs)
	    | _ ->
		(rest,Idmap.add id [a,normalize_alias_opt aliases a,id] all,cstrs))
	| _ -> anomaly "Instance does not match its signature")
      sign (array_rev_to_list args,Idmap.empty,Constrmap.empty) in
  (full_subst,cstr_subst)

let make_pure_subst evi args =
  snd (List.fold_right
    (fun (id,b,c) (args,l) ->
      match args with
	| a::rest -> (rest, (id,a)::l)
	| _ -> anomaly "Instance does not match its signature")
    (evar_filtered_context evi) (array_rev_to_list args,[]))

(*------------------------------------*
 * operations on the evar constraints *
 *------------------------------------*)

(* We have a unification problem Σ; Γ |- ?e[u1..uq] = t : s where ?e is not yet
 * declared in Σ but yet known to be declarable in some context x1:T1..xq:Tq.
 * [define_evar_from_virtual_equation ... Γ Σ t (x1:T1..xq:Tq) .. (u1..uq) (x1..xq)]
 * declares x1:T1..xq:Tq |- ?e : s such that ?e[u1..uq] = t holds.
 *)

let define_evar_from_virtual_equation define_fun env evd t_in_env sign filter inst_in_env =
  let ty_t_in_env = Retyping.get_type_of env evd t_in_env in
  let evd,evar_in_env = new_evar_instance sign evd ty_t_in_env ~filter inst_in_env in
  let t_in_env = whd_evar evd t_in_env in
  let evd = define_fun env evd (destEvar evar_in_env) t_in_env in
  let ids = List.map pi1 (named_context_of_val sign) in
  let inst_in_sign = List.map mkVar (list_filter_with filter ids) in
  let evar_in_sign = mkEvar (fst (destEvar evar_in_env), Array.of_list inst_in_sign) in
  (evd,whd_evar evd evar_in_sign)

(* We have x1..xq |- ?e1 : τ and had to solve something like
 * Σ; Γ |- ?e1[u1..uq] = (...\y1 ... \yk ... c), where c is typically some
 * ?e2[v1..vn], hence flexible. We had to go through k binders and now
 * virtually have x1..xq, y1'..yk' | ?e1' : τ' and the equation
 * Γ, y1..yk |- ?e1'[u1..uq y1..yk] = c.
 * [materialize_evar Γ evd k (?e1[u1..uq]) τ'] extends Σ with the declaration
 * of ?e1' and returns both its instance ?e1'[x1..xq y1..yk] in an extension
 * of the context of e1 so that e1 can be instantiated by
 * (...\y1' ... \yk' ... ?e1'[x1..xq y1'..yk']),
 * and the instance ?e1'[u1..uq y1..yk] so that the remaining equation
 * ?e1'[u1..uq y1..yk] = c can be registered
 *
 * Note that, because invert_definition does not check types, we need to
 * guess the types of y1'..yn' by inverting the types of y1..yn along the
 * substitution u1..uq.
 *)

let materialize_evar define_fun env evd k (evk1,args1) ty_in_env =
  let evi1 = Evd.find_undefined evd evk1 in
  let env1,rel_sign = env_rel_context_chop k env in
  let sign1 = evar_hyps evi1 in
  let filter1 = evar_filter evi1 in
  let ids1 = List.map pi1 (named_context_of_val sign1) in
  let inst_in_sign = List.map mkVar (list_filter_with filter1 ids1) in
  let (sign2,filter2,inst2_in_env,inst2_in_sign,_,evd,_) =
    List.fold_right (fun (na,b,t_in_env as d) (sign,filter,inst_in_env,inst_in_sign,env,evd,avoid) ->
      let id = next_name_away na avoid in
      let evd,t_in_sign =
        define_evar_from_virtual_equation define_fun env evd t_in_env
          sign filter inst_in_env in
      let evd,b_in_sign = match b with
      | None -> evd,None
      | Some b ->
          let evd,b = define_evar_from_virtual_equation define_fun env evd b
            sign filter inst_in_env in
          evd,Some b in
      (push_named_context_val (id,b_in_sign,t_in_sign) sign,true::filter,
       (mkRel 1)::(List.map (lift 1) inst_in_env),
       (mkRel 1)::(List.map (lift 1) inst_in_sign),
       push_rel d env,evd,id::avoid))
      rel_sign
      (sign1,filter1,Array.to_list args1,inst_in_sign,env1,evd,ids1)
  in
  let evd,ev2ty_in_sign =
    define_evar_from_virtual_equation define_fun env evd ty_in_env
      sign2 filter2 inst2_in_env in
  let evd,ev2_in_sign =
    new_evar_instance sign2 evd ev2ty_in_sign ~filter:filter2 inst2_in_sign in
  let ev2_in_env = (fst (destEvar ev2_in_sign), Array.of_list inst2_in_env) in
  (evd, ev2_in_sign, ev2_in_env)

let restrict_upon_filter evd evk p args =
  let newfilter = List.map p args in
  if List.for_all (fun id -> id) newfilter then
    None
  else
    let oldfullfilter = evar_filter (Evd.find_undefined evd evk) in
    Some (apply_subfilter oldfullfilter newfilter)

(* Inverting constructors in instances (common when inferring type of match) *)

let find_projectable_constructor env evd cstr k args cstr_subst =
  try
    let l = Constrmap.find cstr cstr_subst in
    let args = Array.map (lift (-k)) args in
    let l =
      List.filter (fun (args',id) ->
	(* is_conv is maybe too strong (and source of useless computation) *)
	(* (at least expansion of aliases is needed) *)
	array_for_all2 (is_conv env evd) args args') l in
    List.map snd l
  with Not_found ->
    []

(* [find_projectable_vars env sigma y subst] finds all vars of [subst]
 * that project on [y]. It is able to find solutions to the following
 * two kinds of problems:
 *
 * - ?n[...;x:=y;...] = y
 * - ?n[...;x:=?m[args];...] = y with ?m[args] = y recursively solvable
 *
 * (see test-suite/success/Fixpoint.v for an example of application of
 * the second kind of problem).
 *
 * The seek for [y] is up to variable aliasing.  In case of solutions that
 * differ only up to aliasing, the binding that requires the less
 * steps of alias reduction is kept. At the end, only one solution up
 * to aliasing is kept.
 *
 * [find_projectable_vars] also unifies against evars that themselves mention
 * [y] and recursively.
 *
 * In short, the following situations give the following solutions:
 *
 * problem                        evar ctxt   soluce remark
 * z1; z2:=z1 |- ?ev[z1;z2] = z1  y1:A; y2:=y1  y1  \ thanks to defs kept in
 * z1; z2:=z1 |- ?ev[z1;z2] = z2  y1:A; y2:=y1  y2  / subst and preferring =
 * z1; z2:=z1 |- ?ev[z1]    = z2  y1:A          y1  thanks to expand_var
 * z1; z2:=z1 |- ?ev[z2]    = z1  y1:A          y1  thanks to expand_var
 * z3         |- ?ev[z3;z3] = z3  y1:A; y2:=y1  y2  see make_projectable_subst
 *
 * Remark: [find_projectable_vars] assumes that identical instances of
 * variables in the same set of aliased variables are already removed (see
 * [make_projectable_subst])
 *)

type evar_projection =
| ProjectVar
| ProjectEvar of existential * evar_info * identifier * evar_projection

exception NotUnique
exception NotUniqueInType of (identifier * evar_projection) list

let rec assoc_up_to_alias sigma aliases y yc = function
  | [] -> raise Not_found
  | (c,cc,id)::l ->
      let c' = whd_evar sigma c in
      if eq_constr y c' then id
      else
	if l <> [] then assoc_up_to_alias sigma aliases y yc l
	else
	  (* Last chance, we reason up to alias conversion *)
	  match (if c == c' then cc else normalize_alias_opt aliases c') with
	  | Some cc when eq_constr yc cc -> id
	  | _ -> if eq_constr yc c then id else raise Not_found

let rec find_projectable_vars with_evars aliases sigma y subst =
  let yc = normalize_alias aliases y in
  let is_projectable idc idcl subst' =
    (* First test if some [id] aliased to [idc] is bound to [y] in [subst] *)
    try
      let id = assoc_up_to_alias sigma aliases y yc idcl in
      (id,ProjectVar)::subst'
    with Not_found ->
    (* Then test if [idc] is (indirectly) bound in [subst] to some evar *)
    (* projectable on [y] *)
      if with_evars then
	let idcl' = List.filter (fun (c,_,id) -> isEvar c) idcl in
	match idcl' with
	| [c,_,id] ->
	  begin
	    let (evk,argsv as t) = destEvar c in
	    let evi = Evd.find sigma evk in
	    let subst,_ = make_projectable_subst aliases sigma evi argsv in
	    let l = find_projectable_vars with_evars aliases sigma y subst in
	    match l with
	    | [id',p] -> (id,ProjectEvar (t,evi,id',p))::subst'
	    | _ -> subst'
	  end
	| [] -> subst'
	| _ -> anomaly "More than one non var in aliases class of evar instance"
      else
	subst' in
  Idmap.fold is_projectable subst []

(* [filter_solution] checks if one and only one possible projection exists
 * among a set of solutions to a projection problem *)

let filter_solution = function
  | [] -> raise Not_found
  | (id,p)::_::_ -> raise NotUnique
  | [id,p] -> (mkVar id, p)

let project_with_effects aliases sigma effects t subst =
  let c, p =
    filter_solution (find_projectable_vars false aliases sigma t subst) in
  effects := p :: !effects;
  c

let rec find_solution_type evarenv = function
  | (id,ProjectVar)::l -> pi3 (lookup_named id evarenv)
  | [id,ProjectEvar _] -> (* bugged *) pi3 (lookup_named id evarenv)
  | (id,ProjectEvar _)::l -> find_solution_type evarenv l
  | [] -> assert false

(* In case the solution to a projection problem requires the instantiation of
 * subsidiary evars, [do_projection_effects] performs them; it
 * also try to instantiate the type of those subsidiary evars if their
 * type is an evar too.
 *
 * Note: typing creates new evar problems, which induces a recursive dependency
 * with [define]. To avoid a too large set of recursive functions, we
 * pass [define] to [do_projection_effects] as a parameter.
 *)

let rec do_projection_effects define_fun env ty evd = function
  | ProjectVar -> evd
  | ProjectEvar ((evk,argsv),evi,id,p) ->
      let evd = Evd.define evk (mkVar id) evd in
      (* TODO: simplify constraints involving evk *)
      let evd = do_projection_effects define_fun env ty evd p in
      let ty = whd_betadeltaiota env evd (Lazy.force ty) in
      if not (isSort ty) then
	(* Don't try to instantiate if a sort because if evar_concl is an
           evar it may commit to a univ level which is not the right
           one (however, regarding coercions, because t is obtained by
           unif, we know that no coercion can be inserted) *)
	let subst = make_pure_subst evi argsv in
	let ty' = replace_vars subst evi.evar_concl in
	let ty' = whd_evar evd ty' in
	if isEvar ty' then define_fun env evd (destEvar ty') ty else evd
      else
	evd

(* Assuming Σ; Γ, y1..yk |- c, [invert_arg_from_subst Γ k Σ [x1:=u1..xn:=un] c]
 * tries to return φ(x1..xn) such that equation φ(u1..un) = c is valid.
 * The strategy is to imitate the structure of c and then to invert
 * the variables of c (i.e. rels or vars of Γ) using the algorithm
 * implemented by project_with_effects/find_projectable_vars.
 * It returns either a unique solution or says whether 0 or more than
 * 1 solutions is found.
 *
 * Precondition:  Σ; Γ, y1..yk |- c /\ Σ; Γ |- u1..un
 * Postcondition: if φ(x1..xn) is returned then
 *                Σ; Γ, y1..yk |- φ(u1..un) = c /\ x1..xn |- φ(x1..xn)
 *
 * The effects correspond to evars instantiated while trying to project.
 *
 * [invert_arg_from_subst] is used on instances of evars. Since the
 * evars are flexible, these instances are potentially erasable. This
 * is why we don't investigate whether evars in the instances of evars
 * are unifiable, to the contrary of [invert_definition].
 *)

type projectibility_kind =
  | NoUniqueProjection
  | UniqueProjection of constr * evar_projection list

type projectibility_status =
  | CannotInvert
  | Invertible of projectibility_kind

let invert_arg_from_subst evd aliases k0 subst_in_env_extended_with_k_binders c_in_env_extended_with_k_binders =
  let effects = ref [] in
  let rec aux k t =
    let t = whd_evar evd t in
    match kind_of_term t with
    | Rel i when i>k0+k -> aux' k (mkRel (i-k))
    | Var id -> aux' k t
    | _ -> map_constr_with_binders succ aux k t
  and aux' k t =
    try project_with_effects aliases evd effects t subst_in_env_extended_with_k_binders
    with Not_found ->
      match expand_alias_once aliases t with
      | None -> raise Not_found
      | Some c -> aux k c in
  try
    let c = aux 0 c_in_env_extended_with_k_binders in
    Invertible (UniqueProjection (c,!effects))
  with
    | Not_found -> CannotInvert
    | NotUnique -> Invertible NoUniqueProjection

let invert_arg evd aliases k evk subst_in_env_extended_with_k_binders c_in_env_extended_with_k_binders =
  let res = invert_arg_from_subst evd aliases k subst_in_env_extended_with_k_binders c_in_env_extended_with_k_binders in
  match res with
  | Invertible (UniqueProjection (c,_)) when not (noccur_evar evd evk c) ->
      CannotInvert
  | _ ->
      res

let effective_projections =
  map_succeed (function Invertible c -> c | _ -> failwith"")

let instance_of_projection f env t evd projs =
  let ty = lazy (nf_evar evd (Retyping.get_type_of env evd t)) in
  match projs with
  | NoUniqueProjection -> raise NotUnique
  | UniqueProjection (c,effects) ->
      (List.fold_left (do_projection_effects f env ty) evd effects, c)

exception NotEnoughInformationToInvert

let extract_unique_projections projs =
  List.map (function
    | Invertible (UniqueProjection (c,_)) -> c
    | _ ->
        (* For instance, there are evars with non-invertible arguments and *)
        (* we cannot arbitrarily restrict these evars before knowing if there *)
        (* will really be used; it can also be due to some argument *)
        (* (typically a rel) that is not inversible and that cannot be *)
        (* inverted either because it is needed for typing the conclusion *)
        (* of the evar to project *)
      raise NotEnoughInformationToInvert) projs

let extract_candidates sols =
  try
    Some
      (List.map (function (id,ProjectVar) -> mkVar id | _ -> raise Exit) sols)
  with Exit ->
    None

let filter_of_projection = function Invertible _ -> true | _ -> false

let invert_invertible_arg evd aliases k (evk,argsv) args' =
  let evi = Evd.find_undefined evd evk in
  let subst,_ = make_projectable_subst aliases evd evi argsv in
  let projs = array_map_to_list (invert_arg evd aliases k evk subst) args' in
  Array.of_list (extract_unique_projections projs)

(* Redefines an evar with a smaller context (i.e. it may depend on less
 * variables) such that c becomes closed.
 * Example: in "fun (x:?1) (y:list ?2[x]) => x = y :> ?3[x,y] /\ x = nil bool"
 * ?3 <-- ?1          no pb: env of ?3 is larger than ?1's
 * ?1 <-- list ?2     pb: ?2 may depend on x, but not ?1.
 * What we do is that ?2 is defined by a new evar ?4 whose context will be
 * a prefix of ?2's env, included in ?1's env.
 *
 * If "hyps |- ?e : T" and "filter" selects a subset hyps' of hyps then
 * [do_restrict_hyps evd ?e filter] sets ?e:=?e'[hyps'] and returns ?e'
 * such that "hyps' |- ?e : T"
 *)

let filter_candidates evd evk filter candidates =
  let evi = Evd.find_undefined evd evk in
  let candidates = match candidates with
  | None -> evi.evar_candidates
  | Some _ -> candidates in
  match candidates,filter with
  | None,_ | _, None -> candidates
  | Some l, Some filter ->
      let ids = List.map pi1 (list_filter_with filter (evar_context evi)) in
      Some (List.filter (fun a ->
        list_subset (Idset.elements (collect_vars a)) ids) l)

let closure_of_filter evd evk filter =
  let evi = Evd.find_undefined evd evk in
  let vars = collect_vars (evar_concl evi) in
  let ids = List.map pi1 (evar_context evi) in
  let test id b = b || Idset.mem id vars in
  let newfilter = List.map2 test ids filter in
  if newfilter = evar_filter evi then None else Some newfilter

let restrict_hyps evd evk filter candidates =
    (* What to do with dependencies?
       Assume we have x:A, y:B(x), z:C(x,y) |- ?e:T(x,y,z) and restrict on y.
       - If y is in a non-erasable position in C(x,y) (i.e. it is not below an
         occurrence of x in the hnf of C), then z should be removed too.
       - If y is in a non-erasable position in T(x,y,z) then the problem is
         unsolvable.
       Computing whether y is erasable or not may be costly and the
       interest for this early detection in practice is not obvious. We let
       it for future work. In any case, thanks to the use of filters, the whole
       (unrestricted) context remains consistent. *)
    let candidates = filter_candidates evd evk (Some filter) candidates in
    let typablefilter = closure_of_filter evd evk filter in
    (typablefilter,candidates)

exception EvarSolvedWhileRestricting of evar_map

let do_restrict_hyps evd (evk,args as ev) filter candidates =
  let filter,candidates = match filter with
  | None -> None,candidates
  | Some filter -> restrict_hyps evd evk filter candidates in
  match candidates,filter with
  | Some [], _ -> error "Not solvable."
  | Some [nc],_ -> raise (EvarSolvedWhileRestricting (Evd.define evk nc evd))
  | None, None -> evd,ev
  | _ -> restrict_applied_evar evd ev filter candidates

(* [postpone_non_unique_projection] postpones equation of the form ?e[?] = c *)
(* ?e is assumed to have no candidates *)

let postpone_non_unique_projection env evd (evk,argsv as ev) sols rhs =
  let rhs = expand_vars_in_term env rhs in
  let filter =
    restrict_upon_filter evd evk
      (* Keep only variables that occur in rhs *)
      (* This is not safe: is the variable is a local def, its body *)
      (* may contain references to variables that are removed, leading to *)
      (* a ill-formed context. We would actually need a notion of filter *)
      (* that says that the body is hidden. Note that expand_vars_in_term *)
      (* expands only rels and vars aliases, not rels or vars bound to an *)
      (* arbitrary complex term *)
      (fun a -> not (isRel a || isVar a)
                || dependent a rhs || List.exists (fun (id,_) -> isVarId id a) sols)
      (Array.to_list argsv) in
  let filter = match filter with
  | None -> None
  | Some filter -> closure_of_filter evd evk filter in
  let candidates = extract_candidates sols in
  if candidates <> None then
    restrict_evar evd evk filter candidates
  else
    (* We made an approximation by not expanding a local definition *)
    let evd,ev = restrict_applied_evar evd ev filter None in
    let pb = (Reduction.CONV,env,mkEvar ev,rhs) in
    Evd.add_conv_pb pb evd

(* [postpone_evar_evar] postpones an equation of the form ?e1[?1] = ?e2[?2] *)

let postpone_evar_evar f env evd filter1 ev1 filter2 ev2 =
  (* Leave an equation between (restrictions of) ev1 andv ev2 *)
  try
    let evd,ev1' = do_restrict_hyps evd ev1 filter1 None in
    try
      let evd,ev2' = do_restrict_hyps evd ev2 filter2 None in
      add_conv_pb (Reduction.CONV,env,mkEvar ev1',mkEvar ev2') evd
    with EvarSolvedWhileRestricting evd ->
      (* ev2 solved on the fly *)
      f env evd ev1' (mkEvar ev2)
  with EvarSolvedWhileRestricting evd ->
    (* ev1 solved on the fly *)
    f env evd ev2 (mkEvar ev1)

(* [solve_evar_evar f Γ Σ ?e1[u1..un] ?e2[v1..vp]] applies an heuristic
 * to solve the equation Σ; Γ ⊢ ?e1[u1..un] = ?e2[v1..vp]:
 * - if there are at most one φj for each vj s.t. vj = φj(u1..un),
 *   we first restrict ?e2 to the subset v_k1..v_kq of the vj that are
 *   inversible and we set ?e1[x1..xn] := ?e2[φk1(x1..xn)..φkp(x1..xn)]
 *   (this is a case of pattern-unification)
 * - symmetrically if there are at most one ψj for each uj s.t.
 *   uj = ψj(v1..vp),
 * - otherwise, each position i s.t. ui does not occur in v1..vp has to
 *   be restricted and similarly for the vi, and we leave the equation
 *   as an open equation (performed by [postpone_evar])
 *
 * Warning: the notion of unique φj is relative to some given class
 * of unification problems
 *
 * Note: argument f is the function used to instantiate evars.
 *)

let are_canonical_instances args1 args2 env =
  let n1 = Array.length args1 in
  let n2 = Array.length args2 in
  let rec aux n = function
    | (id,_,c)::sign
	when n < n1 && isVarId id args1.(n) && isVarId id args2.(n) ->
	aux (n+1) sign
    | [] ->
	let rec aux2 n =
	  n = n1 ||
	  (isRelN (n1-n) args1.(n) && isRelN (n1-n) args2.(n) && aux2 (n+1))
	in aux2 n
    | _ -> false in
  n1 = n2 & aux 0 (named_context env)

let filter_compatible_candidates conv_algo env evd evi args rhs c =
  let c' = instantiate_evar (evar_filtered_context evi) c args in
  let evd, b = conv_algo env evd Reduction.CONV rhs c' in
  if b then Some (c,evd) else None

exception DoesNotPreserveCandidateRestriction

let restrict_candidates conv_algo env evd filter1 (evk1,argsv1) (evk2,argsv2) =
  let evi1 = Evd.find evd evk1 in
  let evi2 = Evd.find evd evk2 in
  let cand1 = filter_candidates evd evk1 filter1 None in
  let cand2 = evi2.evar_candidates in
  match cand1, cand2 with
  | _, None -> cand1
  | None, Some _ -> raise DoesNotPreserveCandidateRestriction
  | Some l1, Some l2 ->
      let args1 = Array.to_list argsv1 in
      let args2 = Array.to_list argsv2 in
      let l1' = List.filter (fun c1 ->
        let c1' = instantiate_evar (evar_filtered_context evi1) c1 args1 in
        List.filter (fun c2 ->
          (filter_compatible_candidates conv_algo env evd evi2 args2 c1' c2
           <> None)) l2 <> []) l1 in
      if List.length l1 = List.length l1' then None else Some l1'

exception CannotProject of bool list option

(* Assume that FV(?n[x1:=t1..xn:=tn]) belongs to some set U.
   Can ?n be instantiated by a term u depending essentially on xi such that the
   FV(u[x1:=t1..xn:=tn]) are in the set U?
   - If ti is a variable, it has to be in U.
   - If ti is a constructor, its parameters cannot be erased even if u
     matches on it, so we have to discard ti if the parameters
     contain variables not in U.
   - If ti is rigid, we have to discard it if it contains variables in U.

  Note: when restricting as part of an equation ?n[x1:=t1..xn:=tn] = ?m[...]
  then, occurrences of ?m in the ti can be seen, like variables, as occurrences
  of subterms to eventually discard so as to be allowed to keep ti.
*)

let rec is_constrainable_in k (ev,(fv_rels,fv_ids) as g) t =
  let f,args = decompose_app_vect t in
  match kind_of_term f with
  | Construct (ind,_) ->
      let params,_ = array_chop (Inductiveops.inductive_nparams ind) args in
      array_for_all (is_constrainable_in k g) params
  | Ind _ -> array_for_all (is_constrainable_in k g) args
  | Prod (_,t1,t2) -> is_constrainable_in k g t1 && is_constrainable_in k g t2
  | Evar (ev',_) -> ev' <> ev (*If ev' needed, one may also try to restrict it*)
  | Var id -> Idset.mem id fv_ids
  | Rel n -> n <= k || Intset.mem n fv_rels
  | Sort _ -> true
  | _ -> (* We don't try to be more clever *) true

let has_constrainable_free_vars evd aliases k ev (fv_rels,fv_ids as fvs) t =
  let t = expansion_of_var aliases t in
  match kind_of_term t with
  | Var id -> Idset.mem id fv_ids
  | Rel n -> n <= k || Intset.mem n fv_rels
  | _ -> is_constrainable_in k (ev,fvs) t

let ensure_evar_independent g env evd (evk1,argsv1 as ev1) (evk2,argsv2 as ev2)=
  let filter1 =
    restrict_upon_filter evd evk1 (noccur_evar evd evk2) (Array.to_list argsv1)
  in
  let candidates1 = restrict_candidates g env evd filter1 ev1 ev2 in
  let evd,(evk1,_ as ev1) = do_restrict_hyps evd ev1 filter1 candidates1 in
  let filter2 =
    restrict_upon_filter evd evk2 (noccur_evar evd evk1) (Array.to_list argsv2)
  in
  let candidates2 = restrict_candidates g env evd filter2 ev2 ev1 in
  let evd,ev2 = do_restrict_hyps evd ev2 filter2 candidates2 in
  evd,ev1,ev2

exception EvarSolvedOnTheFly of evar_map * constr

let project_evar_on_evar g env evd aliases k2 (evk1,argsv1 as ev1) (evk2,argsv2 as ev2) =
  (* Apply filtering on ev1 so that fvs(ev1) are in fvs(ev2). *)
  let fvs2 = free_vars_and_rels_up_alias_expansion aliases (mkEvar ev2) in
  let filter1 = restrict_upon_filter evd evk1
    (has_constrainable_free_vars evd aliases k2 evk2 fvs2)
    (Array.to_list argsv1) in
  (* Only try pruning on variable substitutions, postpone otherwise. *)
  (* Rules out non-linear instances. *)
  if is_unification_pattern_pure_evar env evd ev2 (mkEvar ev1) then
    try
      let candidates1 = restrict_candidates g env evd filter1 ev1 ev2 in
      let evd,(evk1',args1) = do_restrict_hyps evd ev1 filter1 candidates1 in
      evd,mkEvar (evk1',invert_invertible_arg evd aliases k2 ev2 args1)
    with
    | EvarSolvedWhileRestricting evd ->
        raise (EvarSolvedOnTheFly (evd,mkEvar ev1))
    | DoesNotPreserveCandidateRestriction | NotEnoughInformationToInvert ->
        raise (CannotProject filter1)
  else
    raise (CannotProject filter1)

let solve_evar_evar_l2r f g env evd aliases ev1 (evk2,_ as ev2) =
  try
    let evd,body = project_evar_on_evar g env evd aliases 0 ev1 ev2 in
    Evd.define evk2 body evd
  with EvarSolvedOnTheFly (evd,c) ->
    f env evd ev2 c

let solve_evar_evar ?(force=false) f g env evd (evk1,args1 as ev1) (evk2,args2 as ev2) =
  if are_canonical_instances args1 args2 env then
    (* If instances are canonical, we solve the problem in linear time *)
    let sign = evar_filtered_context (Evd.find evd evk2) in
    let id_inst = list_map_to_array (fun (id,_,_) -> mkVar id) sign in
    Evd.define evk2 (mkEvar(evk1,id_inst)) evd
  else
    let evd,ev1,ev2 =
      (* If an evar occurs in the instance of the other evar and the
         use of an heuristic is forced, we restrict *)
      if force then ensure_evar_independent g env evd ev1 ev2 else (evd,ev1,ev2) in
    let aliases = make_alias_map env in
    try solve_evar_evar_l2r f g env evd aliases ev1 ev2
    with CannotProject filter1 ->
    try solve_evar_evar_l2r f g env evd aliases ev2 ev1
    with CannotProject filter2 ->
    postpone_evar_evar f env evd filter1 ev1 filter2 ev2

type conv_fun =
  env ->  evar_map -> conv_pb -> constr -> constr -> evar_map * bool

let check_evar_instance evd evk1 body conv_algo =
  let evi = Evd.find evd evk1 in
  let evenv = evar_unfiltered_env evi in
  (* FIXME: The body might be ill-typed when this is called from w_merge *)
  let ty =
    try Retyping.get_type_of evenv evd body
    with _ -> error "Ill-typed evar instance"
  in
  let evd,b = conv_algo evenv evd Reduction.CUMUL ty evi.evar_concl in
  if b then evd else
    user_err_loc (fst (evar_source evk1 evd),"",
		  str "Unable to find a well-typed instantiation")

(* Solve pbs ?e[t1..tn] = ?e[u1..un] which arise often in fixpoint
 * definitions. We try to unify the ti with the ui pairwise. The pairs
 * that don't unify are discarded (i.e. ?e is redefined so that it does not
 * depend on these args). *)

let solve_refl ?(can_drop=false) conv_algo env evd evk argsv1 argsv2 =
  if array_equal eq_constr argsv1 argsv2 then evd else
  (* Filter and restrict if needed *)
  let untypedfilter =
    restrict_upon_filter evd evk
      (fun (a1,a2) -> snd (conv_algo env evd Reduction.CONV a1 a2))
      (List.combine (Array.to_list argsv1) (Array.to_list argsv2)) in
  let candidates = filter_candidates evd evk untypedfilter None in
  let filter = match untypedfilter with
    | None -> None
    | Some filter -> closure_of_filter evd evk filter in
  let evd,ev1 = restrict_applied_evar evd (evk,argsv1) filter candidates in
  if fst ev1 = evk & can_drop then (* No refinement *) evd else
    (* either progress, or not allowed to drop, e.g. to preserve possibly *)
    (* informative equations such as ?e[x:=?y]=?e[x:=?y'] where we don't know *)
    (* if e can depend on x until ?y is not resolved, or, conversely, we *)
    (* don't know if ?y has to be unified with ?y, until e is resolved *)
  let argsv2 = restrict_instance evd evk filter argsv2 in
  let ev2 = (fst ev1,argsv2) in
  (* Leave a unification problem *)
  Evd.add_conv_pb (Reduction.CONV,env,mkEvar ev1,mkEvar ev2) evd

(* If the evar can be instantiated by a finite set of candidates known
   in advance, we check which of them apply *)

exception NoCandidates

let solve_candidates conv_algo env evd (evk,argsv as ev) rhs =
  let evi = Evd.find evd evk in
  let args = Array.to_list argsv in
  match evi.evar_candidates with
  | None -> raise NoCandidates
  | Some l ->
      let l' =
        list_map_filter
          (filter_compatible_candidates conv_algo env evd evi args rhs) l in
      match l' with
      | [] -> error_cannot_unify env evd (mkEvar ev, rhs)
      | [c,evd] -> Evd.define evk c evd
      | l when List.length l < List.length l' ->
          let candidates = List.map fst l in
          restrict_evar evd evk None (Some candidates)
      | l -> evd

(* We try to instantiate the evar assuming the body won't depend
 * on arguments that are not Rels or Vars, or appearing several times
 * (i.e. we tackle a generalization of Miller-Pfenning patterns unification)
 *
 * 1) Let "env |- ?ev[hyps:=args] = rhs" be the unification problem
 * 2) We limit it to a patterns unification problem "env |- ev[subst] = rhs"
 *    where only Rel's and Var's are relevant in subst
 * 3) We recur on rhs, "imitating" the term, and failing if some Rel/Var is
 *    not in the scope of ?ev. For instance, the problem
 *    "y:nat |- ?x[] = y" where "|- ?1:nat" is not satisfiable because
 *    ?1 would be instantiated by y which is not in the scope of ?1.
 * 4) We try to "project" the term if the process of imitation fails
 *    and that only one projection is possible
 *
 * Note: we don't assume rhs in normal form, it may fail while it would
 * have succeeded after some reductions.
 *
 * This is the work of [invert_definition Γ Σ ?ev[hyps:=args] c]
 * Precondition:  Σ; Γ, y1..yk |- c /\ Σ; Γ |- u1..un
 * Postcondition: if φ(x1..xn) is returned then
 *                Σ; Γ, y1..yk |- φ(u1..un) = c /\ x1..xn |- φ(x1..xn)
 *)

exception NotInvertibleUsingOurAlgorithm of constr
exception NotEnoughInformationToProgress of (identifier * evar_projection) list
exception OccurCheckIn of evar_map * constr

let rec invert_definition conv_algo choose env evd (evk,argsv as ev) rhs =
  let aliases = make_alias_map env in
  let evdref = ref evd in
  let progress = ref false in
  let evi = Evd.find evd evk in
  let subst,cstr_subst = make_projectable_subst aliases evd evi argsv in

  (* Projection *)
  let project_variable t =
    (* Evar/Var problem: unifiable iff variable projectable from ev subst *)
    try
      let sols = find_projectable_vars true aliases !evdref t subst in
      let c, p = match sols with
	| [] -> raise Not_found
	| [id,p] -> (mkVar id, p)
	| (id,p)::_::_ ->
	    if choose then (mkVar id, p) else raise (NotUniqueInType sols)
      in
      let ty = lazy (Retyping.get_type_of env !evdref t) in
      let evd = do_projection_effects (evar_define conv_algo) env ty !evdref p in
      evdref := evd;
      c
    with
      | Not_found -> raise (NotInvertibleUsingOurAlgorithm t)
      | NotUniqueInType sols ->
	  if not !progress then
            raise (NotEnoughInformationToProgress sols);
	  (* No unique projection but still restrict to where it is possible *)
          (* materializing is necessary, but is restricting useful? *)
          let ty = find_solution_type (evar_env evi) sols in
          let sign = evar_filtered_context evi in
          let ty' = instantiate_evar sign ty (Array.to_list argsv) in
	  let (evd,evar,(evk',argsv' as ev')) =
            materialize_evar (evar_define conv_algo) env !evdref 0 ev ty' in
	  let ts = expansions_of_var aliases t in
	  let test c = isEvar c or List.mem c ts in
	  let filter = array_map_to_list test argsv' in
          let filter = apply_subfilter (evar_filter (Evd.find_undefined evd evk)) filter in

          let filter = closure_of_filter evd evk' filter in
          let candidates = extract_candidates sols in
          let evd =
            if candidates <> None then restrict_evar evd evk' filter candidates
            else
              let evd,ev'' = restrict_applied_evar evd ev' filter None in
              Evd.add_conv_pb (Reduction.CONV,env,mkEvar ev'',t) evd in
          evdref := evd;
	  evar in

  let rec imitate (env',k as envk) t =
    let t = whd_evar !evdref t in
    match kind_of_term t with
    | Rel i when i>k ->
        (match pi2 (Environ.lookup_rel (i-k) env') with
        | None -> project_variable (mkRel (i-k))
        | Some b ->
          try project_variable (mkRel (i-k))
          with NotInvertibleUsingOurAlgorithm _ -> imitate envk (lift i b))
    | Var id ->
        (match pi2 (Environ.lookup_named id env') with
        | None -> project_variable t
        | Some b ->
          try project_variable t
          with NotInvertibleUsingOurAlgorithm _ -> imitate envk b)
    | Evar (evk',args' as ev') ->
        if evk = evk' then raise (OccurCheckIn (evd,rhs));
	(* Evar/Evar problem (but left evar is virtual) *)
        let aliases = lift_aliases k aliases in
        (try
          let ev = (evk,Array.map (lift k) argsv) in
          let evd,body = project_evar_on_evar conv_algo env !evdref aliases k ev'  ev in
	  evdref := evd;
          body
        with
        | EvarSolvedOnTheFly (evd,t) -> evdref:=evd; imitate envk t
        | CannotProject filter' ->
	  assert !progress;
	  (* Make the virtual left evar real *)
	  let ty = get_type_of env' !evdref t in
	  let (evd,evar'',ev'') =
             materialize_evar (evar_define conv_algo) env' !evdref k ev ty in
	  let evd =
	     (* Try to project (a restriction of) the left evar ... *)
	    try
              let evd,body = project_evar_on_evar conv_algo env' evd aliases 0 ev'' ev' in
              Evd.define evk' body evd
	    with
            | EvarSolvedOnTheFly _ -> assert false (* ev has no candidates *)
            | CannotProject filter'' ->
	      (* ... or postpone the problem *)
	      postpone_evar_evar (evar_define conv_algo) env' evd filter'' ev'' filter' ev' in
	  evdref := evd;
	  evar'')
    | _ ->
        progress := true;
	match
	  let c,args = decompose_app_vect t in
	  match kind_of_term c with
	  | Construct cstr when noccur_between 1 k t ->
	    (* This is common case when inferring the return clause of match *)
	    (* (currently rudimentary: we do not treat the case of multiple *)
            (*  possible inversions; we do not treat overlap with a possible *)
            (*  alternative inversion of the subterms of the constructor, etc)*)
	    (match find_projectable_constructor env evd cstr k args cstr_subst with
	     | _::_ as l -> Some (List.map mkVar l)
	     | _ -> None)
	  | _ -> None
	with
	| Some l ->
            let ty = get_type_of env' !evdref t in
            let candidates =
              try
                let t =
                  map_constr_with_full_binders (fun d (env,k) -> push_rel d env, k+1)
	            imitate envk t in
                t::l
              with _ -> l in
            (match candidates with
            | [x] -> x
            | _ ->
	      let (evd,evar'',ev'') =
                materialize_evar (evar_define conv_algo) env' !evdref k ev ty in
              evdref := restrict_evar evd (fst ev'') None (Some candidates);
              evar'')
	| None ->
	  (* Evar/Rigid problem (or assimilated if not normal): we "imitate" *)
	    map_constr_with_full_binders (fun d (env,k) -> push_rel d env, k+1)
	      imitate envk t in

  let rhs = whd_beta evd rhs (* heuristic *) in
  let body = imitate (env,0) rhs in
  (!evdref,body)

(* [define] tries to solve the problem "?ev[args] = rhs" when "?ev" is
 * an (uninstantiated) evar such that "hyps |- ?ev : typ". Otherwise said,
 * [define] tries to find an instance lhs such that
 * "lhs [hyps:=args]" unifies to rhs. The term "lhs" must be closed in
 * context "hyps" and not referring to itself.
 *)

and evar_define conv_algo ?(choose=false) env evd (evk,argsv as ev) rhs =
  match kind_of_term rhs with
  | Evar (evk2,argsv2 as ev2) ->
      if evk = evk2 then
        solve_refl ~can_drop:choose conv_algo env evd evk argsv argsv2
      else
        solve_evar_evar ~force:choose
          (evar_define conv_algo) conv_algo env evd ev ev2
  | _ ->
  try solve_candidates conv_algo env evd ev rhs
  with NoCandidates ->
  try
    let (evd',body) = invert_definition conv_algo choose env evd ev rhs in
    if occur_meta body then error "Meta cannot occur in evar body.";
    (* invert_definition may have instantiate some evars of rhs with evk *)
    (* so we recheck acyclicity *)
    if occur_evar evk body then raise (OccurCheckIn (evd',body));
    (* needed only if an inferred type *)
    let body = refresh_universes body in
(* Cannot strictly type instantiations since the unification algorithm
 * does not unify applications from left to right.
 * e.g problem f x == g y yields x==y and f==g (in that order)
 * Another problem is that type variables are evars of type Type
   let _ =
      try
        let env = evar_env evi in
        let ty = evi.evar_concl in
        Typing.check env evd' body ty
      with e ->
        pperrnl
          (str "Ill-typed evar instantiation: " ++ fnl() ++
           pr_evar_map evd' ++ fnl() ++
           str "----> " ++ int ev ++ str " := " ++
           print_constr body);
        raise e in*)
    let evd' = Evd.define evk body evd' in
    check_evar_instance evd' evk body conv_algo
  with
    | NotEnoughInformationToProgress sols ->
	postpone_non_unique_projection env evd ev sols rhs
    | NotInvertibleUsingOurAlgorithm t ->
	error_not_clean env evd evk t (evar_source evk evd)
    | OccurCheckIn (evd,rhs) ->
	(* last chance: rhs actually reduces to ev *)
	let c = whd_betadeltaiota env evd rhs in
	match kind_of_term c with
	| Evar (evk',argsv2) when evk = evk' ->
	    solve_refl
	      (fun env sigma pb c c' -> (evd,is_fconv pb env sigma c c'))
	      env evd evk argsv argsv2
	| _ ->
	    error_occur_check env evd evk rhs

(* This code (i.e. solve_pb, etc.) takes a unification
 * problem, and tries to solve it. If it solves it, then it removes
 * all the conversion problems, and re-runs conversion on each one, in
 * the hopes that the new solution will aid in solving them.
 *
 * The kinds of problems it knows how to solve are those in which
 * the usable arguments of an existential var are all themselves
 * universal variables.
 * The solution to this problem is to do renaming for the Var's,
 * to make them match up with the Var's which are found in the
 * hyps of the existential, to do a "pop" for each Rel which is
 * not an argument of the existential, and a subst1 for each which
 * is, again, with the corresponding variable. This is done by
 * define
 *
 * Thus, we take the arguments of the existential which we are about
 * to assign, and zip them with the identifiers in the hypotheses.
 * Then, we process all the Var's in the arguments, and sort the
 * Rel's into ascending order.  Then, we just march up, doing
 * subst1's and pop's.
 *
 * NOTE: We can do this more efficiently for the relative arguments,
 * by building a long substituend by hand, but this is a pain in the
 * ass.
 *)

let status_changed lev (pbty,_,t1,t2) =
  (try ExistentialSet.mem (head_evar t1) lev with NoHeadEvar -> false) or
  (try ExistentialSet.mem (head_evar t2) lev with NoHeadEvar -> false)

let reconsider_conv_pbs conv_algo evd =
  let (evd,pbs) = extract_changed_conv_pbs evd status_changed in
  List.fold_left
    (fun (evd,b as p) (pbty,env,t1,t2) ->
      if b then conv_algo env evd pbty t1 t2 else p) (evd,true)
    pbs

(* Tries to solve problem t1 = t2.
 * Precondition: t1 is an uninstantiated evar
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved. *)

(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let solve_simple_eqn conv_algo ?(choose=false) env evd (pbty,(evk1,args1 as ev1),t2) =
  try
    let t2 = whd_betaiota evd t2 in (* includes whd_evar *)
    let evd =
      match pbty with
      | Some true when isEvar t2 ->
          add_conv_pb (Reduction.CUMUL,env,mkEvar ev1,t2) evd
      | Some false when isEvar t2 ->
          add_conv_pb (Reduction.CUMUL,env,t2,mkEvar ev1) evd
      | _ ->
          evar_define conv_algo ~choose env evd ev1 t2 in
    reconsider_conv_pbs conv_algo evd
  with e when precatchable_exception e ->
    (evd,false)

(** The following functions return the set of evars immediately
    contained in the object, including defined evars *)

let evars_of_term c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, l) -> Intset.add n (Array.fold_left evrec acc l)
    | _ -> fold_constr evrec acc c
  in
  evrec Intset.empty c

(* spiwack: a few functions to gather the existential variables
   that occur in the types of goals present or past. *)
let add_evars_of_evars_of_term acc evm c =
  let evars = evars_of_term c in
  Intset.fold begin fun e r ->
    let body = (Evd.find evm e).evar_body in
    let subevars =
      match body with
      | Evar_empty -> None
      | Evar_defined c' -> Some (evars_of_term c')
    in
    Intmap.add e subevars r
  end evars acc

let evars_of_evars_of_term = add_evars_of_evars_of_term Intmap.empty

let add_evars_of_evars_in_type acc evm e =
  let evi = Evd.find evm e in
  let acc_with_concl = add_evars_of_evars_of_term acc evm evi.evar_concl in
  let hyps = Environ.named_context_of_val evi.evar_hyps in
  List.fold_left begin fun r (_,b,t) ->
    let r = add_evars_of_evars_of_term r evm t in
    match b with
    | None -> r
    | Some b -> add_evars_of_evars_of_term r evm b
  end acc_with_concl hyps

let rec add_evars_of_evars_in_types_of_set acc evm s =
  Intset.fold begin fun e r ->
    let r = add_evars_of_evars_in_type r evm e in
    match (Evd.find evm e).evar_body with
    | Evar_empty -> r
    | Evar_defined b -> add_evars_of_evars_in_types_of_set r evm (evars_of_term b)
  end s acc

let evars_of_evars_in_types_of_list evm l =
  let set_of_l = List.fold_left (fun x y -> Intset.add y x) Intset.empty l in
  add_evars_of_evars_in_types_of_set Intmap.empty evm set_of_l

(* /spiwack *)

let evars_of_named_context nc =
  List.fold_right (fun (_, b, t) s ->
    Option.fold_left (fun s t ->
      Intset.union s (evars_of_term t))
      (Intset.union s (evars_of_term t)) b)
    nc Intset.empty

let evars_of_evar_info evi =
  Intset.union (evars_of_term evi.evar_concl)
    (Intset.union
	(match evi.evar_body with
	| Evar_empty -> Intset.empty
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
	  | Evar_empty -> Intset.add n acc
	  | Evar_defined c -> evrec acc c
	 with Not_found -> anomaly "undefined_evars_of_term: evar not found")
      | _ -> fold_constr evrec acc c
  in
  evrec Intset.empty t

let undefined_evars_of_named_context evd nc =
  List.fold_right (fun (_, b, t) s ->
    Option.fold_left (fun s t ->
      Intset.union s (undefined_evars_of_term evd t))
      (Intset.union s (undefined_evars_of_term evd t)) b)
    nc Intset.empty

let undefined_evars_of_evar_info evd evi =
  Intset.union (undefined_evars_of_term evd evi.evar_concl)
    (Intset.union
       (match evi.evar_body with
	 | Evar_empty -> Intset.empty
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
	      | ImplicitArg (gr, (i, id), false) -> ()
	      | _ ->
		  let evi = nf_evar_info sigma (Evd.find_undefined sigma evk) in
		    error_unsolvable_implicit loc env sigma evi k None)
      | _ -> iter_constr proc_rec c
  in proc_rec c

open Glob_term

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

let idx = id_of_string "x"

(* Refining an evar to a product *)

let define_pure_evar_as_product evd evk =
  let evi = Evd.find_undefined evd evk in
  let evenv = evar_unfiltered_env evi in
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
  let evrngargs = array_cons (mkRel 1) (Array.map (lift 1) args) in
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
  let evenv = evar_unfiltered_env evi in
  let typ = whd_betadeltaiota env evd (evar_concl evi) in
  let evd1,(na,dom,rng) = match kind_of_term typ with
  | Prod (na,dom,rng) -> (evd,(na,dom,rng))
  | Evar ev' -> let evd,typ = define_evar_as_product evd ev' in evd,destProd typ
  | _ -> error_not_product_loc dummy_loc env evd typ in
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
  let evbodyargs = array_cons (mkRel 1) (Array.map (lift 1) args) in
  let evbody = mkEvar (fst (destEvar body), evbodyargs) in
  evd,mkLambda (na, dom, evbody)

let rec evar_absorb_arguments env evd (evk,args as ev) = function
  | [] -> evd,ev
  | a::l ->
      (* TODO: optimize and avoid introducing intermediate evars *)
      let evd,lam = define_pure_evar_as_lambda env evd evk in
      let _,_,body = destLambda lam in
      let evk = fst (destEvar body) in
      evar_absorb_arguments env evd (evk, array_cons a args) l

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
