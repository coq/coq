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
open Environ
open Evd
open Reductionops
open Pretype_errors


let rec filter_unique = function
  | [] -> []
  | x::l ->
      if List.mem x l then filter_unique (List.filter (fun y -> x<>y) l)
      else x::filter_unique l

(* Expanding existential variables (pretyping.ml) *)
(* 1- whd_ise fails if an existential is undefined *)

exception Uninstantiated_evar of existential_key

let rec whd_ise sigma c =
  match kind_of_term c with
    | Evar (ev,args) when Evd.in_dom sigma ev ->
	if Evd.is_defined sigma ev then
          whd_ise sigma (existential_value sigma (ev,args))
	else raise (Uninstantiated_evar ev)
  | _ -> c


(* Expand evars, possibly in the head of an application *)
let whd_castappevar_stack sigma c = 
  let rec whrec (c, l as s) =
    match kind_of_term c with
      | Evar (ev,args) when Evd.in_dom sigma ev & Evd.is_defined sigma ev -> 
	  whrec (existential_value sigma (ev,args), l)
      | Cast (c,_) -> whrec (c, l)
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

let nf_evar_info evc info =
  { evar_concl = Reductionops.nf_evar evc info.evar_concl;
    evar_hyps = List.map 
		  (fun (id,body,typ) -> 
		     (id,
		      option_app (Reductionops.nf_evar evc) body,
		      Reductionops.nf_evar evc typ)) info.evar_hyps; 
    evar_body = info.evar_body}

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
      | Evar (k,_) ->
	  if Evd.in_dom emap k & not (Evd.is_defined emap k) then k::acc
	  else (* No recursion on the evar instantiation *) acc
      | _         ->
	  fold_constr collrec acc c in
  list_uniquize (collrec [] c)

let push_dependent_evars sigma emap =
  Evd.fold (fun ev {evar_concl = ccl} (sigma',emap') ->
    List.fold_left 
      (fun (sigma',emap') ev -> 
	(Evd.add sigma' ev (Evd.map emap' ev),Evd.rmv emap' ev))
      (sigma',emap') (collect_evars emap' ccl))
    emap (sigma,emap)
    
(* replaces a mapping of existentials into a mapping of metas.
   Problem if an evar appears in the type of another one (pops anomaly) *)
let evars_to_metas sigma (emap, c) =
  let sigma',emap' = push_dependent_evars sigma emap in
  let change_exist evar =
    let ty = nf_betaiota (nf_evar emap (existential_type emap evar)) in
    let n = new_meta() in
    mkCast (mkMeta n, ty) in
  let rec replace c =
    match kind_of_term c with
        Evar (k,_ as ev) when Evd.in_dom emap' k -> change_exist ev
      | _ -> map_constr replace c in
  (sigma', replace c)

(* The list of non-instantiated existential declarations *)

let non_instantiated sigma = 
  let listev = to_list sigma in
  List.fold_left 
    (fun l (ev,evd) -> 
       if evd.evar_body = Evar_empty then 
	 ((ev,nf_evar_info sigma evd)::l) else l)
    [] listev

(*************************************)
(* Metas *)

let meta_value evd mv = 
  let rec valrec mv =
    try
      let b = meta_fvalue evd mv in
      instance
        (List.map (fun mv' -> (mv',valrec mv')) (Metaset.elements b.freemetas))
        b.rebus
    with Anomaly _ | Not_found -> 
      mkMeta mv
  in 
  valrec mv

let meta_instance env b =
  let c_sigma =
    List.map 
      (fun mv -> (mv,meta_value env mv)) (Metaset.elements b.freemetas)
  in 
  instance c_sigma b.rebus

let nf_meta env c = meta_instance env (mk_freelisted c)

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

(* All ids of sign must be distincts! *)
let new_evar_instance sign evd typ ?(src=(dummy_loc,InternalHole)) instance =
  assert (List.length instance = named_context_length sign); 
  if not (list_distinct (ids_of_named_context sign)) then 
    anomaly "new_evar_instance: two vars have the same name";
  let newev = new_untyped_evar() in
  (evar_declare sign newev typ ~src:src evd,
   mkEvar (newev,Array.of_list instance))

let make_evar_instance_with_rel env =
  let n = rel_context_length (rel_context env) in
  let vars = 
    fold_named_context
      (fun env (id,b,_) l -> (* if b=None then *) mkVar id :: l (*else l*))
      env ~init:[] in
  snd (fold_rel_context
	 (fun env (_,b,_) (i,l) -> 
	    (i-1, (*if b=None then *) mkRel i :: l (*else l*)))
	 env ~init:(n,vars))

let make_subst env args =
  snd (fold_named_context
    (fun env (id,b,c) (args,l as g) ->
       match b, args with
	 | (* None *) _ , a::rest -> (rest, (id,a)::l)
(*	 | Some _, _ -> g*)
	 | _ -> anomaly "Instance does not match its signature")
    env ~init:(List.rev args,[]))

(* [new_isevar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)

let push_rel_context_to_named_context env =
  let sign0 = named_context env in
  let (subst,_,sign) =
  Sign.fold_rel_context
    (fun (na,c,t) (subst,avoid,sign) ->
       let na = if na = Anonymous then Name(id_of_string"_") else na in
       let id = next_name_away na avoid in
       ((mkVar id)::subst,
        id::avoid,
	add_named_decl (id,option_app (substl subst) c,
                        type_app (substl subst) t)
	  sign))
    (rel_context env) ~init:([],ids_of_named_context sign0,sign0)
  in (subst, sign)

let new_evar evd env ?(src=(dummy_loc,InternalHole)) typ =
  let subst,sign = push_rel_context_to_named_context env in
  let typ' = substl subst typ in
  let instance = make_evar_instance_with_rel env in
  new_evar_instance sign evd typ' ~src:src instance

(* The same using side-effect *)
let e_new_evar evd env ?(src=(dummy_loc,InternalHole)) ty =
  let (evd',ev) = new_evar !evd env ~src:src ty in
  evd := evd';
  ev

(*------------------------------------*
 * operations on the evar constraints *
 *------------------------------------*)

(* Pb: defined Rels and Vars should not be considered as a pattern... *)
let is_pattern inst =
  let rec is_hopat l = function
      [] -> true
    | t :: tl ->
        (isRel t or isVar t) && not (List.mem t l) && is_hopat (t::l) tl in
  is_hopat [] (Array.to_list inst)

let evar_well_typed_body evd ev evi body =
  try
    let env = evar_env evi in
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

let strict_inverse = false

let inverse_instance env isevars ev evi inst rhs =
  let subst = make_subst (evar_env evi) (Array.to_list inst) in
  let subst = List.map (fun (x,y) -> (y,mkVar x)) subst in
  let evd = ref isevars in
  let error () = 
    error_not_clean env (evars_of !evd) ev rhs (evar_source ev !evd) in
  let rec subs rigid k t =
    match kind_of_term t with
      | Rel i ->
 	  if i<=k then t
 	  else
            (try List.assoc (mkRel (i-k)) subst
             with Not_found ->
               if rigid then error()
               else if strict_inverse then
                 failwith "cannot solve pb yet"
               else t)
      | Var id ->
          (try List.assoc t subst
           with Not_found ->
             if rigid then error()
             else if
               not strict_inverse &&
               List.exists (fun (id',_,_) -> id=id') evi.evar_hyps
             then
               failwith "cannot solve pb yet"
             else t)
      | Evar (ev,args) ->
          if Evd.is_defined_evar !evd (ev,args) then
            subs rigid k (existential_value (evars_of !evd) (ev,args))
          else
	    let args' = Array.map (subs false k) args in
	    mkEvar (ev,args')
      | _ -> map_constr_with_binders succ (subs rigid) k t in
  let body = subs true 0 (nf_evar (evars_of isevars) rhs) in
  (!evd,body)


let is_defined_equation env evd (ev,inst) rhs =
  is_pattern inst &&
  not (occur_evar ev rhs) &&
  try
    let evi = Evd.map (evars_of evd) ev in
    let (evd',body) = inverse_instance env evd ev evi inst rhs in
    evar_well_typed_body evd' ev evi body
  with Failure _ -> false


(* Redefines an evar with a smaller context (i.e. it may depend on less
 * variables) such that c becomes closed.
 * Example: in [x:?1; y:(list ?2)] <?3>x=y /\ x=(nil bool)
 * ?3 <-- ?1          no pb: env of ?3 is larger than ?1's
 * ?1 <-- (list ?2)   pb: ?2 may depend on x, but not ?1.
 * What we do is that ?2 is defined by a new evar ?4 whose context will be
 * a prefix of ?2's env, included in ?1's env. *)

let do_restrict_hyps evd ev args =
  let args = Array.to_list args in
  let evi = Evd.map (evars_of !evd) ev in
  let env = evar_env evi in
  let hyps = evi.evar_hyps in
  let (sign,ncargs) = list_filter2 (fun _ a -> closed0 a) (hyps,args) in
  (* No care is taken in case the evar type uses vars filtered out!
     Is it important ? *)
  let nc =
    e_new_evar evd (reset_with_named_context sign env)
      ~src:(evar_source ev !evd) evi.evar_concl in
  evd := Evd.evar_define ev nc !evd;
  let (evn,_) = destEvar nc in
  mkEvar(evn,Array.of_list ncargs)


let need_restriction isevars args = not (array_for_all closed0 args)

(* We try to instanciate the evar assuming the body won't depend
 * on arguments that are not Rels or Vars, or appearing several times.
 *)
(* Note: error_not_clean should not be an error: it simply means that the
 * conversion test that lead to the faulty call to [real_clean] should return
 * false. The problem is that we won't get the right error message.
 *)

let real_clean env isevars ev evi args rhs =
  let evd = ref isevars in
  let subst = List.map (fun (x,y) -> (y,mkVar x)) (filter_unique args) in
  let rec subs rigid k t =
    match kind_of_term t with
      | Rel i ->
 	 if i<=k then t
 	 else (try List.assoc (mkRel (i-k)) subst with Not_found -> t)
      | Evar (ev,args) ->
          if Evd.is_defined_evar !evd (ev,args) then
            subs rigid k (existential_value (evars_of !evd) (ev,args))
          else
	    let args' = Array.map (subs false k) args in
	    if need_restriction !evd args' then
              do_restrict_hyps evd ev args'
	    else
	      mkEvar (ev,args')
      | Var id ->
          (try List.assoc t subst
           with Not_found ->
             if
               not rigid or List.exists (fun (id',_,_) -> id=id') evi.evar_hyps
             then t
             else
               error_not_clean env (evars_of !evd) ev rhs
                 (evar_source ev !evd))
      | _ -> map_constr_with_binders succ (subs rigid) k t
  in
  let body = subs true 0 (nf_evar (evars_of isevars) rhs) in
  if not (closed0 body)
  then error_not_clean env (evars_of !evd) ev body (evar_source ev !evd);
  (!evd,body)

(* [evar_define] solves the problem lhs = rhs when lhs is an uninstantiated
 * evar, i.e. tries to find the body ?sp for lhs=mkEvar (sp,args)
 * ?sp [ sp.hyps \ args ]  unifies to rhs
 * ?sp must be a closed term, not referring to itself.
 * Not so trivial because some terms of args may be terms that are not
 * variables. In this case, the non-var-or-Rels arguments are replaced
 * by <implicit>. [clean_rhs] will ignore this part of the subtitution. 
 * This leads to incompleteness (we don't deal with pbs that require
 * inference of dependent types), but it seems sensible.
 *
 * If after cleaning, some free vars still occur, the function [restrict_hyps]
 * tries to narrow the env of the evars that depend on Rels.
 *
 * If after that free Rels still occur it means that the instantiation
 * cannot be done, as in  [x:?1; y:nat; z:(le y y)] x=z
 * ?1 would be instantiated by (le y y) but y is not in the scope of ?1
 *)

(* env needed for error messages... *)
let evar_define env (ev,argsv) rhs isevars =
  if occur_evar ev rhs
  then error_occur_check env (evars_of isevars) ev rhs;
  let args = Array.to_list argsv in 
  let evi = Evd.map (evars_of isevars) ev in
  (* the bindings to invert *)
  let worklist = make_subst (evar_env evi) args in
  let (isevars',body) = real_clean env isevars ev evi worklist rhs in
  if occur_meta body then error "Meta cannot occur in evar body"
  else
    (* needed only if an inferred type *)
    let body = refresh_universes body in
(* Cannot strictly type instantiations since the unification algorithm
 * does not unifies applications from left to right.
 * e.g problem f x == g y yields x==y and f==g (in that order) 
 * Another problem is that type variables are evars of type Type
   let _ =
      try
        let env = evar_env evi in
        let ty = evi.evar_concl in
        Typing.check env (evars_of isevars') body ty
      with e ->
        pperrnl
          (str "Ill-typed evar instantiation: " ++ fnl() ++
           pr_evar_defs isevars' ++ fnl() ++
           str "----> " ++ int ev ++ str " := " ++
           print_constr body);
        raise e in*)
    let isevars'' = Evd.evar_define ev body isevars' in
    isevars'',[ev]



(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

let has_undefined_evars isevars t = 
  try let _ = local_strong (whd_ise (evars_of isevars)) t in false
  with Uninstantiated_evar _ -> true

let is_ground_term isevars t =
  not (has_undefined_evars isevars t)

let head_is_evar isevars = 
  let rec hrec k = match kind_of_term k with
    | Evar n   -> not (Evd.is_defined_evar isevars n)
    | App (f,_) -> hrec f
    | Cast (c,_) -> hrec c
    | _ -> false
  in 
  hrec 

let rec is_eliminator c = match kind_of_term c with
  | App _    -> true
  | Case _ -> true
  | Cast (c,_) -> is_eliminator c
  | _ -> false

let head_is_embedded_evar isevars c =
  (head_is_evar isevars c) & (is_eliminator c)

let head_evar = 
  let rec hrec c = match kind_of_term c with
    | Evar (ev,_)       -> ev
    | Case (_,_,c,_) -> hrec c
    | App (c,_)        -> hrec c
    | Cast (c,_)        -> hrec c
    | _                   -> failwith "headconstant"
  in 
  hrec 

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

let status_changed lev (pbty,t1,t2) =
  try 
    List.mem (head_evar t1) lev or List.mem (head_evar t2) lev
  with Failure _ ->
    try List.mem (head_evar t2) lev with Failure _ -> false

(* Solve pbs (?i x1..xn) = (?i y1..yn) which arises often in fixpoint
 * definitions. We try to unify the xi with the yi pairwise. The pairs
 * that don't unify are discarded (i.e. ?i is redefined so that it does not
 * depend on these args). *)

let solve_refl conv_algo env isevars ev argsv1 argsv2 =
  if argsv1 = argsv2 then (isevars,[]) else
  let evd = Evd.map (evars_of isevars) ev in
  let hyps = evd.evar_hyps in
  let (isevars',_,rsign) = 
    array_fold_left2
      (fun (isevars,sgn,rsgn) a1 a2 ->
        let (isevars',b) = conv_algo env isevars Reduction.CONV a1 a2 in
	 if b then 
	   (isevars',List.tl sgn, add_named_decl (List.hd sgn) rsgn)
	 else 
	   (isevars,List.tl  sgn, rsgn))
      (isevars,hyps,[]) argsv1 argsv2 
  in
  let nsign = List.rev rsign in
  let (evd',newev) =
    new_evar isevars (reset_with_named_context nsign env)
      ~src:(evar_source ev isevars) evd.evar_concl in
  let evd'' = Evd.evar_define ev newev evd' in
  evd'', [ev]


(* Tries to solve problem t1 = t2.
 * Precondition: t1 is an uninstanciated evar
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved. *)

(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let solve_simple_eqn conv_algo env isevars (pbty,(n1,args1 as ev1),t2) =
  try
    let t2 = nf_evar (evars_of isevars) t2 in
    let (isevars,lsp) = match kind_of_term t2 with
      | Evar (n2,args2 as ev2) ->
	  if n1 = n2 then
	    solve_refl conv_algo env isevars n1 args1 args2
	  else
            (try evar_define env ev1 t2 isevars
            with e when precatchable_exception e ->
              evar_define env ev2 (mkEvar ev1) isevars)
(*	    if Array.length args1 < Array.length args2 then
	      evar_define env ev2 (mkEvar ev1) isevars
	    else 
	      evar_define env ev1 t2 isevars*)
      | _ ->
	  evar_define env ev1 t2 isevars in
    let (isevars,pbs) = get_conv_pbs isevars (status_changed lsp) in
    List.fold_left
      (fun (isevars,b as p) (pbty,t1,t2) ->
        if b then conv_algo env isevars pbty t1 t2 else p) (isevars,true)
      pbs
  with e when precatchable_exception e ->
    (isevars,false)

(* Operations on value/type constraints *)

type type_constraint = constr option
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

(* Refining an evar to a product or a sort *)

(* Declaring any type to be in the sort Type shouldn't be harmful since
   cumulativity now includes Prop and Set in Type...
   It is, but that's not too bad *)
let define_evar_as_arrow evd (ev,args) =
  let evi = Evd.map (evars_of evd) ev in
  let evenv = evar_env evi in
  let (evd1,dom) = new_evar evd evenv (new_Type()) in
  let nvar =
    next_ident_away (id_of_string "x") (ids_of_named_context evi.evar_hyps) in
  let newenv = push_named (nvar, None, dom) evenv in
  let (evd2,rng) =
    new_evar evd1 newenv ~src:(evar_source ev evd1) (new_Type()) in
  let prod = mkProd (Name nvar, dom, subst_var nvar rng) in
  let evd3 = Evd.evar_define ev prod evd2 in
  let evdom = fst (destEvar dom), args in
  let evrng =
    fst (destEvar rng), array_cons (mkRel 1) (Array.map (lift 1) args) in
  let prod' = mkProd (Name nvar, mkEvar evdom, mkEvar evrng) in
  (evd3,prod')

let define_evar_as_sort isevars (ev,args) =
  let s = new_Type () in
  Evd.evar_define ev s isevars, destSort s


(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)

let judge_of_new_Type () = Typeops.judge_of_type (new_univ ())

(* Propagation of constraints through application and abstraction:
   Given a type constraint on a functional term, returns the type
   constraint on its domain and codomain. If the input constraint is
   an evar instantiate it with the product of 2 new evars. *)

let split_tycon loc env isevars = function
  | None -> isevars,(Anonymous,None,None)
  | Some c ->
      let sigma = evars_of isevars in
      let t = whd_betadeltaiota env sigma c in
      match kind_of_term t with
        | Prod (na,dom,rng) -> isevars, (na, Some dom, Some rng)
	| Evar ev when not (Evd.is_defined_evar isevars ev) ->
	    let (isevars',prod) = define_evar_as_arrow isevars ev in
            let (_,dom,rng) = destProd prod in
	    isevars',(Anonymous, Some dom, Some rng)
	| _ -> error_not_product_loc loc env sigma c

let valcon_of_tycon x = x

let lift_tycon = option_app (lift 1)

