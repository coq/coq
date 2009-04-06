(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Nameops
open Univ
open Term
open Termops
open Sign
open Pre_env
open Environ
open Evd
open Reductionops
open Pretype_errors
open Retyping

(* Expanding existential variables (pretyping.ml) *)
(* 1- whd_ise fails if an existential is undefined *)

exception Uninstantiated_evar of existential_key

let rec whd_ise sigma c =
  match kind_of_term c with
    | Evar (evk,args as ev) when Evd.mem sigma evk ->
	if Evd.is_defined sigma evk then
          whd_ise sigma (existential_value sigma ev)
	else raise (Uninstantiated_evar evk)
  | _ -> c


(* Expand evars, possibly in the head of an application *)
let whd_castappevar_stack sigma c = 
  let rec whrec (c, l as s) =
    match kind_of_term c with
      | Evar (evk,args as ev) when Evd.mem sigma evk & Evd.is_defined sigma evk
	  -> whrec (existential_value sigma ev, l)
      | Cast (c,_,_) -> whrec (c, l)
      | App (f,args) -> whrec (f, Array.fold_right (fun a l -> a::l) args l)
      | _ -> s
  in 
  whrec (c, [])

let whd_castappevar sigma c = applist (whd_castappevar_stack sigma c)

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
    evar_hyps = map_named_val (Reductionops.nf_evar evc) info.evar_hyps}

let nf_evars evm = Evd.fold (fun ev evi evm' -> Evd.add evm' ev (nf_evar_info evm evi))
		     evm Evd.empty

let nf_evar_defs evd = Evd.evars_reset_evd (nf_evars (Evd.evars_of evd)) evd

let nf_isevar evd = nf_evar (Evd.evars_of evd)
let j_nf_isevar evd = j_nf_evar (Evd.evars_of evd)
let jl_nf_isevar evd = jl_nf_evar (Evd.evars_of evd)
let jv_nf_isevar evd = jv_nf_evar (Evd.evars_of evd)
let tj_nf_isevar evd = tj_nf_evar (Evd.evars_of evd)

(**********************)
(* Creating new metas *)
(**********************)

(* Generator of metavariables *)
let new_meta =
  let meta_ctr = ref 0 in
  fun () -> incr meta_ctr; !meta_ctr

let mk_new_meta () = mkMeta(new_meta())

let collect_evars emap c =
  let rec collrec acc c =
    match kind_of_term c with
      | Evar (evk,_) ->
	  if Evd.mem emap evk & not (Evd.is_defined emap evk) then evk::acc
	  else (* No recursion on the evar instantiation *) acc
      | _         ->
	  fold_constr collrec acc c in
  list_uniquize (collrec [] c)

let push_dependent_evars sigma emap =
  Evd.fold (fun ev {evar_concl = ccl} (sigma',emap') ->
    List.fold_left 
      (fun (sigma',emap') ev -> 
	(Evd.add sigma' ev (Evd.find emap' ev),Evd.remove emap' ev))
      (sigma',emap') (collect_evars emap' ccl))
    emap (sigma,emap)

(* replaces a mapping of existentials into a mapping of metas.
   Problem if an evar appears in the type of another one (pops anomaly) *)
let evars_to_metas sigma (emap, c) =
  let emap = nf_evars emap in
  let sigma',emap' = push_dependent_evars sigma emap in
  let change_exist evar =
    let ty = nf_betaiota emap (existential_type emap evar) in
    let n = new_meta() in
    mkCast (mkMeta n, DEFAULTcast, ty) in
  let rec replace c =
    match kind_of_term c with
      | Evar (evk,_ as ev) when Evd.mem emap' evk -> change_exist ev
      | _ -> map_constr replace c in
  (sigma', replace c)

(* The list of non-instantiated existential declarations *)

let non_instantiated sigma = 
  let listev = to_list sigma in
  List.fold_left 
    (fun l (ev,evi) -> 
       if evi.evar_body = Evar_empty then 
	 ((ev,nf_evar_info sigma evi)::l) else l)
    [] listev

(**********************)
(* Creating new evars *)
(**********************)

(* Generator of existential names *)
let new_untyped_evar =
  let evar_ctr = ref 0 in
  fun () -> incr evar_ctr; existential_of_int !evar_ctr

(*------------------------------------*
 * functional operations on evar sets *
 *------------------------------------*)

let new_evar_instance sign evd typ ?(src=(dummy_loc,InternalHole)) ?filter instance =
  let instance =
    match filter with
    | None -> instance
    | Some filter -> snd (list_filter2 (fun b c -> b) (filter,instance)) in
  assert
    (let ctxt = named_context_of_val sign in
     list_distinct (ids_of_named_context ctxt));
  let newevk = new_untyped_evar() in
  let evd = evar_declare sign newevk typ ~src:src ?filter evd in
  (evd,mkEvar (newevk,Array.of_list instance))

(* Knowing that [Gamma |- ev : T] and that [ev] is applied to [args],
 * [make_projectable_subst ev args] builds the substitution [Gamma:=args].
 * If a variable and an alias of it are bound to the same instance, we skip
 * the alias (we just use eq_constr -- instead of conv --, since anyway,
 * only instances that are variables -- or evars -- are later considered;
 * morever, we can bet that similar instances came at some time from
 * the very same substitution. The removal of aliased duplicates is
 * useful to ensure the uniqueness of a projection.
*)

let make_projectable_subst sigma evi args =
  let sign = evar_filtered_context evi in
  let rec alias_of_var id = 
    match pi2 (Sign.lookup_named id sign) with
    | Some t when isVar t -> alias_of_var (destVar t)
    | _ -> id in
  snd (List.fold_right
    (fun (id,b,c) (args,l) ->
      match b,args with
	| Some c, a::rest when
	    isVar c & (try eq_constr a (snd (List.assoc (destVar c) l)) with Not_found -> false) -> (rest,l)
	| _, a::rest -> (rest, (id, (alias_of_var id,whd_evar sigma a))::l)
	| _ -> anomaly "Instance does not match its signature")
    sign (List.rev (Array.to_list args),[]))

let make_pure_subst evi args =
  snd (List.fold_right
    (fun (id,b,c) (args,l) ->
      match args with
	| a::rest -> (rest, (id,a)::l)
	| _ -> anomaly "Instance does not match its signature")
    (evar_filtered_context evi) (List.rev (Array.to_list args),[]))

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
 *   "x:nat; x':=x; f:forall x, x=x -> Prop |- f _ (refl_equal x')"
 *   we want the hole to be instantiated by x', not by x (which would have the
 *   case in [invert_instance] if x' had disappear of the instance).
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
  (named_context_val env, substl subst typ, inst_rels@inst_vars)
      
(* [new_evar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)

let new_evar evd env ?(src=(dummy_loc,InternalHole)) ?filter typ =
  let sign,typ',instance = push_rel_context_to_named_context env typ in
  new_evar_instance sign evd typ' ~src:src ?filter instance

  (* The same using side-effect *)
let e_new_evar evdref env ?(src=(dummy_loc,InternalHole)) ?filter ty =
  let (evd',ev) = new_evar !evdref env ~src:src ?filter ty in
  evdref := evd';
  ev

(*------------------------------------*
 * operations on the evar constraints *
 *------------------------------------*)

let is_pattern inst =
  array_for_all (fun a -> isRel a || isVar a) inst &&
  array_distinct inst

(* Pb: defined Rels and Vars should not be considered as a pattern... *)
(*
let is_pattern inst =
  let rec is_hopat l = function
      [] -> true
    | t :: tl ->
        (isRel t or isVar t) && not (List.mem t l) && is_hopat (t::l) tl in
  is_hopat [] (Array.to_list inst)
*)

let evar_well_typed_body evd ev evi body =
  try
    let env = evar_unfiltered_env evi in
    let ty = evi.evar_concl in
    Typing.check env (evars_of evd) body ty;
    true
  with e ->
    pperrnl
      (str "Ill-typed evar instantiation: " ++ fnl() ++
       pr_evar_defs evd ++ fnl() ++
       str "----> " ++ int ev ++ str " := " ++
       print_constr body);
    false

(* We have x1..xq |- ?e1 and had to solve something like 
 * Σ; Γ |- ?e1[u1..uq] = (...\y1 ... \yk ... c), where c is typically some 
 * ?e2[v1..vn], hence flexible. We had to go through k binders and now 
 * virtually have x1..xq, y1..yk | ?e1' and the equation
 * Γ, y1..yk |- ?e1'[u1..uq y1..yk] = c.
 * What we do is to formally introduce ?e1' in context x1..xq, Γ, y1..yk,
 * but forbidding it to use the variables of Γ (otherwise said,
 * Γ is here only for ensuring the correct typing of ?e1').
 *
 * In fact, we optimize a little and try to compute a maximum
 * common subpart of x1..xq and Γ. This is done by detecting the
 * longest subcontext x1..xp such that Γ = x1'..xp' z1..zm and 
 * u1..up = x1'..xp'.
 *
 * At the end, we return ?e1'[x1..xn z1..zm y1..yk] so that ?e1 can be 
 * instantiated by (...\y1 ... \yk ... ?e1[x1..xn z1..zm y1..yk]) and the
 * new problem is Σ; Γ, y1..yk |- ?e1'[u1..un z1..zm y1..yk] = c,
 * making the z1..zm unavailable.
 *
 * This is what [extend_evar Γ evd k (?e1[u1..uq]) c] does.
 *)

let shrink_context env subst ty =
  let rev_named_sign = List.rev (named_context env) in
  let rel_sign = rel_context env in
  (* We merge the contexts (optimization) *)
  let rec shrink_rel i subst rel_subst rev_rel_sign =
    match subst,rev_rel_sign with
    | (id,c)::subst,_::rev_rel_sign when c = mkRel i -> 
	shrink_rel (i-1) subst (mkVar id::rel_subst) rev_rel_sign
    | _ ->
	substl_rel_context rel_subst (List.rev rev_rel_sign), 
	substl rel_subst ty
  in
  let rec shrink_named subst named_subst rev_named_sign =
    match subst,rev_named_sign with
    | (id,c)::subst,(id',b',t')::rev_named_sign when c = mkVar id' ->
	shrink_named subst ((id',mkVar id)::named_subst) rev_named_sign
    | _::_, [] ->
	let nrel = List.length rel_sign in
	let rel_sign, ty = shrink_rel nrel subst [] (List.rev rel_sign) in
	[], map_rel_context (replace_vars named_subst) rel_sign,
	replace_vars named_subst ty
    | _ ->
	map_named_context (replace_vars named_subst) (List.rev rev_named_sign),
	rel_sign, ty
  in
  shrink_named subst [] rev_named_sign

let extend_evar env evdref k (evk1,args1) c =
  let ty = get_type_of env (evars_of !evdref) c in
  let overwrite_first v1 v2 =
    let v = Array.copy v1 in
    let n = Array.length v - Array.length v2 in
    for i = 0 to Array.length v2 - 1 do v.(n+i) <- v2.(i) done;
    v in
  let evi1 = Evd.find (evars_of !evdref) evk1 in
  let named_sign',rel_sign',ty =
    if k = 0 then [], [], ty
    else shrink_context env (List.rev (make_pure_subst evi1 args1)) ty in
  let extenv =
    List.fold_right push_rel rel_sign'
      (List.fold_right push_named named_sign' (evar_unfiltered_env evi1)) in
  let nb_to_hide = rel_context_length rel_sign' - k in
  let rel_filter = list_map_i (fun i _ -> i > nb_to_hide) 1 rel_sign' in
  let named_filter1 = List.map (fun _ -> true) (evar_context evi1) in
  let named_filter2 = List.map (fun _ -> false) named_sign' in
  let filter = rel_filter@named_filter2@named_filter1 in
  let evar1' = e_new_evar evdref extenv ~filter:filter ty in
  let evk1',args1'_in_env = destEvar evar1' in
  let args1'_in_extenv = Array.map (lift k) (overwrite_first args1'_in_env args1) in
  (evar1',(evk1',args1'_in_extenv))

let subfilter p filter l =
  let (filter,_,l) =
    List.fold_left (fun (filter,l,newl) b ->
      if b then 
	let a,l' = match l with a::args -> a,args | _ -> assert false in
	if p a then (true::filter,l',a::newl) else (false::filter,l',newl)
      else (false::filter,l,newl))
      ([],l,[]) filter in
  (List.rev filter,List.rev l)

let restrict_upon_filter evd evi evk p args =
  let filter = evar_filter evi in
  let newfilter,newargs = subfilter p filter args in
  if newfilter <> filter then
    let (evd,newev) = new_evar evd (evar_unfiltered_env evi) ~src:(evar_source evk evd)
	~filter:newfilter evi.evar_concl in
    let evd = Evd.evar_define evk newev evd in
    evd,fst (destEvar newev),newargs
  else
    evd,evk,args

let collect_vars c =
  let rec collrec acc c =
    match kind_of_term c with
    | Var id -> list_add_set id acc
    | _      -> fold_constr collrec acc c
  in
  collrec [] c

type clear_dependency_error =
| OccurHypInSimpleClause of identifier option
| EvarTypingBreak of existential

exception ClearDependencyError of identifier * clear_dependency_error

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
	  if Evd.is_defined_evar !evdref ev then
	    (* If evk is already defined we replace it by its definition *)
	    let nc = whd_evar (evars_of !evdref) c in 
	      (check_and_clear_in_constr evdref err ids nc)
	  else 
	    (* We check for dependencies to elements of ids in the
	       evar_info corresponding to e and in the instance of
	       arguments. Concurrently, we build a new evar
	       corresponding to e where hypotheses of ids have been
	       removed *)
	    let evi = Evd.find (evars_of !evdref) evk in
	    let ctxt = Evd.evar_filtered_context evi in
	    let (nhyps,nargs,rids) =
	      List.fold_right2 
		(fun (rid,ob,c as h) a (hy,ar,ri) ->
		  (* Check if some id to clear occurs in the instance
		     a of rid in ev and remember the dependency *)
		  match 
		    List.filter (fun id -> List.mem id ids) (collect_vars a)
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

	    let env = Sign.fold_named_context push_named nhyps ~init:(empty_env) in
	    let ev'= e_new_evar evdref env ~src:(evar_source evk !evdref) nconcl in
	      evdref := Evd.evar_define evk ev' !evdref;
	      let (evk',_) = destEvar ev' in
		mkEvar(evk', Array.of_list nargs)

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


(* Expand rels and vars that are bound to other rels or vars so that 
   dependencies in variables are canonically associated to the most ancient
   variable in its family of aliased variables *)

let expand_var_once env x = match kind_of_term x with
  | Rel n ->
      begin match pi2 (lookup_rel n env) with
      | Some t when isRel t or isVar t -> lift n t
      | _ -> raise Not_found
      end
  | Var id ->
      begin match pi2 (lookup_named id env) with
      | Some t when isVar t -> t
      | _ -> raise Not_found
      end
  | _ ->
      raise Not_found

let rec expand_var_at_least_once env x =
  let t = expand_var_once env x in
  try expand_var_at_least_once env t
  with Not_found -> t

let expand_var env x =
  try expand_var_at_least_once env x with Not_found -> x
  
let expand_var_opt env x =
  try Some (expand_var_at_least_once env x) with Not_found -> None

let rec expand_vars_in_term env t = match kind_of_term t with
  | Rel _ | Var _ -> expand_var env t
  | _ -> map_constr_with_full_binders push_rel expand_vars_in_term env t

let rec expansions_of_var env x =
  try 
    let t = expand_var_once env x in
    t :: expansions_of_var env t
  with Not_found ->
    [x]

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

exception NotUnique

type evar_projection = 
| ProjectVar 
| ProjectEvar of existential * evar_info * identifier * evar_projection

let rec find_projectable_vars with_evars env sigma y subst =
  let is_projectable (id,(idc,y')) =
    let y' = whd_evar sigma y' in
    if y = y' or expand_var env y = expand_var env y'
    then (idc,(y'=y,(id,ProjectVar)))
    else if with_evars & isEvar y' then
      let (evk,argsv as t) = destEvar y' in
      let evi = Evd.find sigma evk in
      let subst = make_projectable_subst sigma evi argsv in
      let l = find_projectable_vars with_evars env sigma y subst in
      match l with 
      | [id',p] -> (idc,(true,(id,ProjectEvar (t,evi,id',p))))
      | _ -> failwith ""
    else failwith "" in
  let l = map_succeed is_projectable subst in
  let l = list_partition_by (fun (idc,_) (idc',_) -> idc = idc') l in
  let l = List.map (List.map snd) l in
  List.map (fun l -> try List.assoc true l with Not_found -> snd (List.hd l)) l

(* [filter_solution] checks if one and only one possible projection exists
 * among a set of solutions to a projection problem *)

let filter_solution = function
  | [] -> raise Not_found
  | (id,p)::_::_ -> raise NotUnique
  | [id,p] -> (mkVar id, p)

let project_with_effects env sigma effects t subst =
  let c, p = filter_solution (find_projectable_vars false env sigma t subst) in
  effects := p :: !effects;
  c

(* In case the solution to a projection problem requires the instantiation of
 * subsidiary evars, [do_projection_effects] performs them; it
 * also try to instantiate the type of those subsidiary evars if their
 * type is an evar too.
 *
 * Note: typing creates new evar problems, which induces a recursive dependency
 * with [evar_define]. To avoid a too large set of recursive functions, we
 * pass [evar_define] to [do_projection_effects] as a parameter.
 *)

let rec do_projection_effects define_fun env ty evd = function
  | ProjectVar -> evd
  | ProjectEvar ((evk,argsv),evi,id,p) ->
      let evd = Evd.evar_define evk (mkVar id) evd in
      (* TODO: simplify constraints involving evk *)
      let evd = do_projection_effects define_fun env ty evd p in
      let ty = whd_betadeltaiota env (evars_of evd) (Lazy.force ty) in
      if not (isSort ty) then
	(* Don't try to instantiate if a sort because if evar_concl is an
           evar it may commit to a univ level which is not the right
           one (however, regarding coercions, because t is obtained by
           unif, we know that no coercion can be inserted) *)
	let subst = make_pure_subst evi argsv in
	let ty' = replace_vars subst evi.evar_concl in
	let ty' = whd_evar (evars_of evd) ty' in
	if isEvar ty' then define_fun env (destEvar ty') ty evd else evd
      else
	evd

(* Assuming Σ; Γ, y1..yk |- c, [invert_subst Γ k Σ [x1:=u1;...;xn:=un] c]
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
 * [invert_subst] is used on instances of evars. Since the evars are flexible,
 * these instances are potentially erasable. This is why we don't investigate
 * whether evars in the instances of evars are unifiable, to the contrary of 
 * [invert_definition].
 *)

type projectibility_kind =
  | NoUniqueProjection
  | UniqueProjection of constr * evar_projection list

type projectibility_status =
  | CannotInvert
  | Invertible of projectibility_kind

let invert_arg_from_subst env k sigma subst_in_env c_in_env_extended_with_k_binders =
  let effects = ref [] in
  let rec aux k t =
    let t = whd_evar sigma t in
    match kind_of_term t with
    | Rel i when i>k ->
	project_with_effects env sigma effects (mkRel (i-k)) subst_in_env
    | Var id ->
	project_with_effects env sigma effects t subst_in_env
    | _ ->
	map_constr_with_binders succ aux k t in
  try 
    let c = aux k c_in_env_extended_with_k_binders in
    Invertible (UniqueProjection (c,!effects))
  with
    | Not_found -> CannotInvert
    | NotUnique -> Invertible NoUniqueProjection

let invert_arg env k sigma (evk,args_in_env) c_in_env_extended_with_k_binders =
  let subst_in_env = make_projectable_subst sigma (Evd.find sigma evk) args_in_env in
  invert_arg_from_subst env k sigma subst_in_env c_in_env_extended_with_k_binders

let effective_projections =
  map_succeed (function Invertible c -> c | _ -> failwith"")

let instance_of_projection f env t evd projs =
  let ty = lazy (Retyping.get_type_of env (evars_of evd) t) in
  match projs with
  | NoUniqueProjection -> raise NotUnique
  | UniqueProjection (c,effects) ->
      (List.fold_left (do_projection_effects f env ty) evd effects, c)

let filter_of_projection = function CannotInvert -> false | _ -> true

let filter_along f projs v =
  let l = Array.to_list v in
  let _,l = list_filter2 (fun b c -> f b) (projs,l) in
  Array.of_list l

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

let do_restrict_hyps_virtual evd evk filter =
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
    let evi = Evd.find (evars_of evd) evk in
    let env = evar_unfiltered_env evi in
    let oldfilter = evar_filter evi in
    let filter,_ = List.fold_right (fun oldb (l,filter) ->
      if oldb then List.hd filter::l,List.tl filter else (false::l,filter))
      oldfilter ([],List.rev filter) in
    new_evar evd env ~src:(evar_source evk evd)
      ~filter:filter evi.evar_concl

let do_restrict_hyps evd evk projs =
  let filter = List.map filter_of_projection projs in
  if List.for_all (fun x -> x) filter then
    evd,evk
  else
    let evd,nc = do_restrict_hyps_virtual evd evk filter in
    let evd = Evd.evar_define evk nc evd in
    let evk',_ = destEvar nc in
    evd,evk'

(* [postpone_evar_term] postpones an equation of the form ?e[σ] = c *)

let postpone_evar_term env evd (evk,argsv) rhs =
  let rhs = expand_vars_in_term env rhs in
  let evi = Evd.find (evars_of evd) evk in
  let evd,evk,args =
    restrict_upon_filter evd evi evk
      (* Keep only variables that depends in rhs *)
      (* This is not safe: is the variable is a local def, its body *)
      (* may contain references to variables that are removed, leading to *)
      (* a ill-formed context. We would actually need a notion of filter *)
      (* that says that the body is hidden. Note that expand_vars_in_term *)
      (* expands only rels and vars aliases, not rels or vars bound to an *)
      (* arbitrary complex term *)
      (fun a -> not (isRel a || isVar a) || dependent a rhs)
      (Array.to_list argsv) in
  let args = Array.of_list args in
  let pb = (Reduction.CONV,env,mkEvar(evk,args),rhs) in
  Evd.add_conv_pb pb evd

(* [postpone_evar_evar] postpones an equation of the form ?e1[σ1] = ?e2[σ2] *)

let postpone_evar_evar env evd projs1 (evk1,args1) projs2 (evk2,args2) =
  (* Leave an equation between (restrictions of) ev1 andv ev2 *)
  let args1' = filter_along filter_of_projection projs1 args1 in
  let evd,evk1' = do_restrict_hyps evd evk1 projs1 in
  let args2' = filter_along filter_of_projection projs2 args2 in
  let evd,evk2' = do_restrict_hyps evd evk2 projs2 in
  let pb = (Reduction.CONV,env,mkEvar(evk1',args1'),mkEvar (evk2',args2')) in
  add_conv_pb pb evd

(* [solve_evar_evar f Γ Σ ?e1[u1..un] ?e2[v1..vp]] applies an heuristic 
 * to solve the equation Σ; Γ ⊢ ?e1[u1..un] = ?e2[v1..vp]:
 * - if there are at most one φj for each vj s.t. vj = φj(u1..un), 
 *   we first restrict ?2 to the subset v_k1..v_kq of the vj that are 
 *   inversible and we set ?1[x1..xn] := ?2[φk1(x1..xn)..φkp(x1..xn)]
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

exception CannotProject of projectibility_status list

let solve_evar_evar_l2r f env evd (evk1,args1) (evk2,_ as ev2) =
  let proj1 = array_map_to_list (invert_arg env 0 (evars_of evd) ev2) args1 in
  try
    (* Instantiate ev2 with (a restriction of) ev1 if uniquely projectable *)
    let proj1' = effective_projections proj1 in
    let evd,args1' =
      list_fold_map (instance_of_projection f env (mkEvar ev2)) evd proj1' in
    let evd,evk1' = do_restrict_hyps evd evk1 proj1 in
    Evd.evar_define evk2 (mkEvar(evk1',Array.of_list args1')) evd
  with NotUnique ->
    raise (CannotProject proj1)

let solve_evar_evar f env evd ev1 ev2 =
  try solve_evar_evar_l2r f env evd ev1 ev2
  with CannotProject projs1 ->
  try solve_evar_evar_l2r f env evd ev2 ev1
  with CannotProject projs2 ->
  postpone_evar_evar env evd projs1 ev1 projs2 ev2

let expand_rhs env sigma subst rhs =
  let d = (named_hd env rhs Anonymous,Some rhs,get_type_of env sigma rhs) in
  let rhs' = lift 1 rhs in
  let f (id,(idc,t)) = (id,(idc,replace_term rhs' (mkRel 1) (lift 1 t))) in
  push_rel d env, List.map f subst, mkRel 1

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
 * This is the work of [invert_definition Γ Σ ?ev[hyps:=args] 
 * Precondition:  Σ; Γ, y1..yk |- c /\ Σ; Γ |- u1..un
 * Postcondition: if φ(x1..xn) is returned then 
 *                Σ; Γ, y1..yk |- φ(u1..un) = c /\ x1..xn |- φ(x1..xn)
 *)

exception NotInvertibleUsingOurAlgorithm of constr
exception NotEnoughInformationToProgress

let rec invert_definition choose env evd (evk,argsv as ev) rhs =
  let evdref = ref evd in
  let progress = ref false in
  let evi = Evd.find (evars_of evd) evk in
  let subst = make_projectable_subst (evars_of evd) evi argsv in

  (* Projection *)
  let project_variable t =
    (* Evar/Var problem: unifiable iff variable projectable from ev subst *)
    try 
      let sols = find_projectable_vars true env (evars_of !evdref) t subst in
      let c, p = match sols with
	| [] -> raise Not_found
	| [id,p] -> (mkVar id, p)
	| (id,p)::_::_ -> if choose then (mkVar id, p) else raise NotUnique
      in
      let ty = lazy (Retyping.get_type_of env (evars_of !evdref) t) in
      let evd = do_projection_effects evar_define env ty !evdref p in
      evdref := evd;
      c
    with
      | Not_found -> raise (NotInvertibleUsingOurAlgorithm t)
      | NotUnique ->
	  if not !progress then raise NotEnoughInformationToProgress;
	  (* No unique projection but still restrict to where it is possible *)
	  let ts = expansions_of_var env t in
	  let test c = isEvar c or List.mem c ts in
	  let filter = array_map_to_list test argsv in
	  let args' = filter_along (fun x -> x) filter argsv in
	  let evd,evar = do_restrict_hyps_virtual !evdref evk filter in
	  let evk',_ = destEvar evar in
	  let pb = (Reduction.CONV,env,mkEvar(evk',args'),t) in
	  evdref := Evd.add_conv_pb pb evd;
	  evar in

  let rec imitate (env',k as envk) t =
    let t = whd_evar (evars_of !evdref) t in
    match kind_of_term t with
    | Rel i when i>k -> project_variable (mkRel (i-k))
    | Var id -> project_variable t
    | Evar (evk',args' as ev') ->
        if evk = evk' then error_occur_check env (evars_of evd) evk rhs;
	(* Evar/Evar problem (but left evar is virtual) *)
	let projs' =
	  array_map_to_list
	    (invert_arg_from_subst env k (evars_of !evdref) subst) args'
	in
	(try
	  (* Try to project (a restriction of) the right evar *)
	  let eprojs' = effective_projections projs' in
	  let evd,args' = 
	    list_fold_map (instance_of_projection evar_define env' t)
	      !evdref eprojs' in
	  let evd,evk' = do_restrict_hyps evd evk' projs' in
	  evdref := evd;
	  mkEvar (evk',Array.of_list args')
	with NotUnique ->
	  assert !progress;
	  (* Make the virtual left evar real *)
	  let (evar'',ev'') = extend_evar env' evdref k ev t in
	  let evd =
	    (* Try to project (a restriction of) the left evar ... *)
	    try solve_evar_evar_l2r evar_define env' !evdref ev'' ev'
	    with CannotProject projs'' ->
	    (* ... or postpone the problem *)
	    postpone_evar_evar env' !evdref projs'' ev'' projs' ev' in
	  evdref := evd;
	  evar'')
    | _ ->
	progress := true;
	(* Evar/Rigid problem (or assimilated if not normal): we "imitate" *)
	map_constr_with_full_binders (fun d (env,k) -> push_rel d env, k+1)
	  imitate envk t in

  let rhs = whd_beta (evars_of evd) rhs (* heuristic *) in
  let body = imitate (env,0) rhs in
  (!evdref,body)

(* [evar_define] tries to solve the problem "?ev[args] = rhs" when "?ev" is
 * an (uninstantiated) evar such that "hyps |- ?ev : typ". Otherwise said,
 * [evar_define] tries to find an instance lhs such that
 * "lhs [hyps:=args]" unifies to rhs. The term "lhs" must be closed in
 * context "hyps" and not referring to itself.
 *)

and occur_existential evm c =
  let rec occrec c = match kind_of_term c with
    | Evar (e, _) -> if not (is_defined evm e) then raise Occur
    | _ -> iter_constr occrec c
  in try occrec c; false with Occur -> true

and evar_define ?(choose=false) env (evk,_ as ev) rhs evd =
  try
    let (evd',body) = invert_definition choose env evd ev rhs in
    if occur_meta body then error "Meta cannot occur in evar body.";
    (* invert_definition may have instantiate some evars of rhs with evk *)
    (* so we recheck acyclicity *)
    if occur_evar evk body then error_occur_check env (evars_of evd) evk body;
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
        Typing.check env (evars_of evd') body ty
      with e ->
        pperrnl
          (str "Ill-typed evar instantiation: " ++ fnl() ++
           pr_evar_defs evd' ++ fnl() ++
           str "----> " ++ int ev ++ str " := " ++
           print_constr body);
        raise e in*)
    Evd.evar_define evk body evd'
  with
    | NotEnoughInformationToProgress ->
	postpone_evar_term env evd ev rhs
    | NotInvertibleUsingOurAlgorithm t -> 
	error_not_clean env (evars_of evd) evk t (evar_source evk evd)

(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

let has_undefined_evars evd t =
  let evm = evars_of evd in
  let rec has_ev t =
    match kind_of_term t with
        Evar (ev,args) ->
          (match evar_body (Evd.find evm ev) with
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
let is_ground_env = memo1_2 is_ground_env

let head_evar = 
  let rec hrec c = match kind_of_term c with
    | Evar (evk,_)   -> evk
    | Case (_,_,c,_) -> hrec c
    | App (c,_)      -> hrec c
    | Cast (c,_,_)   -> hrec c
    | _              -> failwith "headconstant"
  in 
  hrec 

(* Check if an applied evar "?X[args] l" is a Miller's pattern; note
   that we don't care whether args itself contains Rel's or even Rel's
   distinct from the ones in l *)

let rec expand_and_check_vars env = function
  | [] -> []
  | a::l ->
      if isRel a or isVar a then
	let l = expand_and_check_vars env l in
	match expand_var_opt env a with
	| None -> a :: l
	| Some a' when isRel a' or isVar a' -> list_add_set a' l
	| _ -> raise Exit
      else
	raise Exit

let is_unification_pattern_evar env (_,args) l t =
  List.for_all (fun x -> isRel x || isVar x) l (* common failure case *)
  &&
    let l' = Array.to_list args @ l in
    let l'' = try Some (expand_and_check_vars env l') with Exit -> None in
    match l'' with
    | Some l ->
	let deps =
	  if occur_meta_or_existential t then
	    (* Probably no restrictions on allowed vars in presence of evars *)
	    l
	  else
	    (* Probably strong restrictions coming from t being evar-closed *)
	    let t = expand_vars_in_term env t in
	    let fv_rels = free_rels t in
	    let fv_ids = global_vars env t in
	    List.filter (fun c ->
	      match kind_of_term c with
	      | Var id -> List.mem id fv_ids
	      | Rel n -> Intset.mem n fv_rels
	      | _ -> assert false) l in
	list_distinct deps
    | None -> false

let is_unification_pattern (env,nb) f l t =
  match kind_of_term f with
    | Meta _ ->
	array_for_all (fun c -> isRel c && destRel c <= nb) l
	&& array_distinct l
    | Evar ev ->
	is_unification_pattern_evar env ev (Array.to_list l) t
    | _ ->
	false

(* From a unification problem "?X l1 = term1 l2" such that l1 is made
   of distinct rel's, build "\x1...xn.(term1 l2)" (patterns unification) *)

let solve_pattern_eqn env l1 c =
  let l1 = List.map (expand_var env) l1 in
  let c' = List.fold_right (fun a c ->
    let c' = subst_term (lift 1 a) (lift 1 c) in
    match kind_of_term a with
      (* Rem: if [a] links to a let-in, do as if it were an assumption *)
      | Rel n -> let (na,_,t) = lookup_rel n env in mkLambda (na,lift n t,c')
      | Var id -> let (id,_,t) = lookup_named id env in mkNamedLambda id t c'
      | _ -> assert false) 
    l1 c in
  (* Warning: we may miss some opportunity to eta-reduce more since c'
     is not in normal form *)
  whd_eta c'

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
 * evar_define
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
  try 
    List.mem (head_evar t1) lev or List.mem (head_evar t2) lev
  with Failure _ ->
    try List.mem (head_evar t2) lev with Failure _ -> false

(* Solve pbs (?i x1..xn) = (?i y1..yn) which arises often in fixpoint
 * definitions. We try to unify the xi with the yi pairwise. The pairs
 * that don't unify are discarded (i.e. ?i is redefined so that it does not
 * depend on these args). *)

let solve_refl conv_algo env evd evk argsv1 argsv2 =
  if argsv1 = argsv2 then evd else
  let evi = Evd.find (evars_of evd) evk in
  (* Filter and restrict if needed *)
  let evd,evk,args =
    restrict_upon_filter evd evi evk
      (fun (a1,a2) -> snd (conv_algo env evd Reduction.CONV a1 a2))
      (List.combine (Array.to_list argsv1) (Array.to_list argsv2)) in
  (* Leave a unification problem *)
  let args1,args2 = List.split args in
  let argsv1 = Array.of_list args1 and argsv2 = Array.of_list args2 in
  let pb = (Reduction.CONV,env,mkEvar(evk,argsv1),mkEvar(evk,argsv2)) in
  Evd.add_conv_pb pb evd

(* Tries to solve problem t1 = t2.
 * Precondition: t1 is an uninstantiated evar
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved. *)

(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let solve_simple_eqn conv_algo ?(choose=false) env evd (pbty,(evk1,args1 as ev1),t2) =
  try
    let t2 = whd_evar (evars_of evd) t2 in
    let evd = match kind_of_term t2 with
      | Evar (evk2,args2 as ev2) ->
	  if evk1 = evk2 then
	    solve_refl conv_algo env evd evk1 args1 args2
	  else
	    if pbty = Reduction.CONV 
	    then solve_evar_evar evar_define env evd ev1 ev2
	    else add_conv_pb (pbty,env,mkEvar ev1,t2) evd
      | _ ->
	  let evd = evar_define ~choose env ev1 t2 evd in
	  let evm = evars_of evd in
	  let evi = Evd.find evm evk1 in
	    if occur_existential evm evi.evar_concl then
	      let evenv = evar_env evi in
	      let evc = nf_isevar evd evi.evar_concl in
		match evi.evar_body with 
		| Evar_defined body -> 
		    let ty = nf_isevar evd (Retyping.get_type_of_with_meta evenv evm (metas_of evd) body) in
		      add_conv_pb (Reduction.CUMUL,evenv,ty,evc) evd
		| Evar_empty -> (* Resulted in a constraint *) 
		    evd
	    else evd
    in
    let (evd,pbs) = extract_changed_conv_pbs evd status_changed in
      List.fold_left
	(fun (evd,b as p) (pbty,env,t1,t2) ->
	  if b then conv_algo env evd pbty t1 t2 else p) (evd,true)
	pbs
  with e when precatchable_exception e ->
    (evd,false)

let evars_of_term c = 
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, _) -> Intset.add n acc
    | _ -> fold_constr evrec acc c
  in 
    evrec Intset.empty c

let evars_of_named_context nc =
  List.fold_right (fun (_, b, t) s ->
    Option.fold_left (fun s t -> 
      Intset.union s (evars_of_term t))
      s b) nc Intset.empty

let evars_of_evar_info evi =
  Intset.union (evars_of_term evi.evar_concl)
    (Intset.union 
	(match evi.evar_body with 
	| Evar_empty -> Intset.empty
	| Evar_defined b -> evars_of_term b)
	(evars_of_named_context (named_context_of_val evi.evar_hyps)))
    
(* [check_evars] fails if some unresolved evar remains *)
(* it assumes that the defined existentials have already been substituted *)

let check_evars env initial_sigma evd c =
  let sigma = evars_of evd in
  let c = nf_evar sigma c in
  let rec proc_rec c =
    match kind_of_term c with
      | Evar (evk,args) ->
          assert (Evd.mem sigma evk);
	  if not (Evd.mem initial_sigma evk) then
            let (loc,k) = evar_source evk evd in
	    let evi = nf_evar_info sigma (Evd.find sigma evk) in
	    error_unsolvable_implicit loc env sigma evi k None
      | _ -> iter_constr proc_rec c
  in proc_rec c

(* Operations on value/type constraints *)

type type_constraint_type = (int * int) option * constr
type type_constraint = type_constraint_type option

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

let mk_tycon_type c = (None, c)
let mk_abstr_tycon_type n c = (Some (n, n), c) (* First component is initial abstraction, second
						  is current abstraction *)

(* Builds a type constraint *)
let mk_tycon ty = Some (mk_tycon_type ty)

let mk_abstr_tycon n ty = Some (mk_abstr_tycon_type n ty)

(* Constrains the value of a type *)
let empty_valcon = None

(* Builds a value constraint *)
let mk_valcon c = Some c

(* Refining an evar to a product or a sort *)

(* Declaring any type to be in the sort Type shouldn't be harmful since
   cumulativity now includes Prop and Set in Type...
   It is, but that's not too bad *)
let define_evar_as_abstraction abs evd (ev,args) =
  let evi = Evd.find (evars_of evd) ev in
  let evenv = evar_unfiltered_env evi in
  let (evd1,dom) = new_evar evd evenv (new_Type()) ~filter:(evar_filter evi) in
  let nvar =
    next_ident_away (id_of_string "x")
      (ids_of_named_context (evar_context evi)) in
  let newenv = push_named (nvar, None, dom) evenv in
  let (evd2,rng) =
    new_evar evd1 newenv ~src:(evar_source ev evd1) (new_Type()) 
      ~filter:(true::evar_filter evi) in
  let prod = abs (Name nvar, dom, subst_var nvar rng) in
  let evd3 = Evd.evar_define ev prod evd2 in
  let evdom = fst (destEvar dom), args in
  let evrng =
    fst (destEvar rng), array_cons (mkRel 1) (Array.map (lift 1) args) in
  let prod' = abs (Name nvar, mkEvar evdom, mkEvar evrng) in
    (evd3,prod')
      
let define_evar_as_product evd (ev,args) =
  define_evar_as_abstraction (fun t -> mkProd t) evd (ev,args)

let define_evar_as_lambda evd (ev,args) =
  define_evar_as_abstraction (fun t -> mkLambda t) evd (ev,args)

let define_evar_as_sort evd (ev,args) =
  let s = new_Type () in
  Evd.evar_define ev s evd, destSort s

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)

let judge_of_new_Type () = Typeops.judge_of_type (new_univ ())

(* Propagation of constraints through application and abstraction:
   Given a type constraint on a functional term, returns the type
   constraint on its domain and codomain. If the input constraint is
   an evar instantiate it with the product of 2 new evars. *)

let split_tycon loc env evd tycon = 
  let rec real_split evd c = 
    let t = whd_betadeltaiota env (Evd.evars_of evd) c in
      match kind_of_term t with
	| Prod (na,dom,rng) -> evd, (na, dom, rng)
	| Evar ev when not (Evd.is_defined_evar evd ev) ->
	    let (evd',prod) = define_evar_as_product evd ev in
	    let (_,dom,rng) = destProd prod in
	      evd',(Anonymous, dom, rng)
	| _ -> error_not_product_loc loc env (Evd.evars_of evd) c
  in
    match tycon with
      | None -> evd,(Anonymous,None,None)
      | Some (abs, c) ->
	  (match abs with
	       None -> 
		 let evd', (n, dom, rng) = real_split evd c in
		   evd', (n, mk_tycon dom, mk_tycon rng)
	     | Some (init, cur) ->
		 if cur = 0 then 
		   let evd', (x, dom, rng) = real_split evd c in
		     evd, (Anonymous, 
			  Some (None, dom), 
			  Some (None, rng))
		 else
		   evd, (Anonymous, None, 
			Some (if cur = 1 then None,c else Some (init, pred cur), c)))
	    
let valcon_of_tycon x = 
  match x with
    | Some (None, t) -> Some t
    | _ -> None
	
let lift_abstr_tycon_type n (abs, t) =
  match abs with 
      None -> raise (Invalid_argument "lift_abstr_tycon_type: not an abstraction")
    | Some (init, abs) ->
	let abs' = abs + n in 
	  if abs' < 0 then raise (Invalid_argument "lift_abstr_tycon_type")
	  else (Some (init, abs'), t)

let lift_tycon_type n (abs, t) = (abs, lift n t)
let lift_tycon n = Option.map (lift_tycon_type n)

let pr_tycon_type env (abs, t) =
  match abs with 
      None -> Termops.print_constr_env env t
    | Some (init, cur) -> str "Abstract (" ++ int init ++ str ","  ++ int cur ++ str ") " ++ Termops.print_constr_env env t
	
let pr_tycon env = function
    None -> str "None"
  | Some t -> pr_tycon_type env t

