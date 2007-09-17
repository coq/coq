(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Environ
open Evd
open Reduction
open Reductionops
open Rawterm
open Pattern
open Evarutil
open Pretype_errors
open Retyping

(* if lname_typ is [xn,An;..;x1,A1] and l is a list of terms,
   gives [x1:A1]..[xn:An]c' such that c converts to ([x1:A1]..[xn:An]c' l) *)

let abstract_scheme env c l lname_typ =
  List.fold_left2 
    (fun t (locc,a) (na,_,ta) ->
       let na = match kind_of_term a with Var id -> Name id | _ -> na in
       if occur_meta ta then error "cannot find a type for the generalisation"
       else if occur_meta a then lambda_name env (na,ta,t)
       else lambda_name env (na,ta,subst_term_occ locc a t))
    c
    (List.rev l)
    lname_typ

let abstract_list_all env sigma typ c l =
  let ctxt,_ = decomp_n_prod env sigma (List.length l) typ in
  let p = abstract_scheme env c (List.map (function a -> [],a) l) ctxt in 
  try 
    if is_conv_leq env sigma (Typing.type_of env sigma p) typ then p
    else error "abstract_list_all"
  with UserError _ ->
    raise (PretypeError (env,CannotGeneralize typ))

(**)

(* A refinement of [conv_pb]: the integers tells how many arguments
   were applied in the context of the conversion problem; if the number
   is non zero, steps of eta-expansion will be allowed
*)

type conv_pb_up_to_eta = Cumul | ConvUnderApp of int * int

let topconv = ConvUnderApp (0,0)
let of_conv_pb = function CONV -> topconv | CUMUL -> Cumul
let conv_pb_of = function ConvUnderApp _ -> CONV | Cumul -> CUMUL
let prod_pb = function ConvUnderApp _ -> topconv | pb -> pb

let opp_status = function
  | IsSuperType -> IsSubType
  | IsSubType -> IsSuperType
  | ConvUpToEta _ | UserGiven as x -> x

let add_type_status (x,y) = ((x,TypeNotProcessed),(y,TypeNotProcessed))

let extract_instance_status = function
  | Cumul -> add_type_status (IsSubType, IsSuperType)
  | ConvUnderApp (n1,n2) -> add_type_status (ConvUpToEta n1, ConvUpToEta n2)

let rec assoc_pair x = function
    [] -> raise Not_found
  | (a,b,_)::l -> if compare a x = 0 then b else assoc_pair x l

let rec subst_meta_instances bl c =
  match kind_of_term c with
    | Meta i -> (try assoc_pair i bl with Not_found -> c)
    | _ -> map_constr (subst_meta_instances bl) c

let solve_pattern_eqn_array env f l c (metasubst,evarsubst) =
  match kind_of_term f with
    | Meta k -> 
	let pb = (ConvUpToEta (Array.length l),TypeNotProcessed) in
	(k,solve_pattern_eqn env (Array.to_list l) c,pb)::metasubst,evarsubst
    | Evar ev ->
      (* Currently unused: incompatible with eauto/eassumption backtracking *)
	metasubst,(ev,solve_pattern_eqn env (Array.to_list l) c)::evarsubst
    | _ -> assert false

(*******************************)

(* Unification à l'ordre 0 de m et n: [unify_0 env sigma cv_pb m n]
   renvoie deux listes:

   metasubst:(int*constr)list    récolte les instances des (Meta k)
   evarsubst:(constr*constr)list récolte les instances des (Const "?k")

   Attention : pas d'unification entre les différences instances d'une
   même meta ou evar, il peut rester des doublons *)

(* Unification order: *)
(* Left to right: unifies first argument and then the other arguments *)
(*let unify_l2r x = List.rev x
(* Right to left: unifies last argument and then the other arguments *)
let unify_r2l x = x

let sort_eqns = unify_r2l
*)

let unify_0_with_initial_metas metas env sigma cv_pb mod_delta m n =
  let nb = nb_rel env in
  let trivial_unify pb (metasubst,_ as substn) m n =
    match subst_defined_metas (* too strong: metasubst *) metas m with
      | Some m when
	  (if mod_delta then is_fconv (conv_pb_of pb) env sigma m n
	  else eq_constr m n) -> substn
      | _ -> error_cannot_unify env sigma (m,n) in
  let rec unirec_rec curenv pb ((metasubst,evarsubst) as substn) curm curn =
    let cM = Evarutil.whd_castappevar sigma curm
    and cN = Evarutil.whd_castappevar sigma curn in 
      match (kind_of_term cM,kind_of_term cN) with
	| Meta k1, Meta k2 ->
	    let stM,stN = extract_instance_status pb in
	    if k1 < k2 
	    then (k1,cN,stN)::metasubst,evarsubst
	    else if k1 = k2 then substn
	    else (k2,cM,stM)::metasubst,evarsubst
	| Meta k, _    -> 
	    (* Here we check that [cN] does not contain any local variables *)
	    if (closedn nb cN)
	    then (k,cN,snd (extract_instance_status pb))::metasubst,evarsubst
	    else error_cannot_unify_local curenv sigma (m,n,cN)
	| _, Meta k    -> 
	    (* Here we check that [cM] does not contain any local variables *)
	    if (closedn nb cM)
	    then (k,cM,fst (extract_instance_status pb))::metasubst,evarsubst
	    else error_cannot_unify_local curenv sigma (m,n,cM)
	| Evar ev, _ -> metasubst,((ev,cN)::evarsubst)
	| _, Evar ev -> metasubst,((ev,cM)::evarsubst)
	| Lambda (na,t1,c1), Lambda (_,t2,c2) ->
	    unirec_rec (push_rel_assum (na,t1) curenv) topconv
	      (unirec_rec curenv topconv substn t1 t2) c1 c2
	| Prod (na,t1,c1), Prod (_,t2,c2) ->
	    unirec_rec (push_rel_assum (na,t1) curenv) (prod_pb pb)
	      (unirec_rec curenv topconv substn t1 t2) c1 c2
	| LetIn (_,b,_,c), _ -> unirec_rec curenv pb substn (subst1 b c) cN
	| _, LetIn (_,b,_,c) -> unirec_rec curenv pb substn cM (subst1 b c)
	    
	| App (f1,l1), _ when
	    isMeta f1 & is_unification_pattern f1 l1 & not (dependent f1 cN) ->
	      solve_pattern_eqn_array curenv f1 l1 cN substn

	| _, App (f2,l2) when
	    isMeta f2 & is_unification_pattern f2 l2 & not (dependent f2 cM) ->
	      solve_pattern_eqn_array curenv f2 l2 cM substn

	| App (f1,l1), App (f2,l2) ->
	      let len1 = Array.length l1
	      and len2 = Array.length l2 in
              let (f1,l1,f2,l2) =
		if len1 = len2 then (f1,l1,f2,l2)
		else if len1 < len2 then
		  let extras,restl2 = array_chop (len2-len1) l2 in 
		    (f1, l1, appvect (f2,extras), restl2)
		else 
		  let extras,restl1 = array_chop (len1-len2) l1 in 
		    (appvect (f1,extras), restl1, f2, l2) in
	      let pb = ConvUnderApp (len1,len2) in
		(try
		    array_fold_left2 (unirec_rec curenv topconv)
		      (unirec_rec curenv pb substn f1 f2) l1 l2
		  with ex when precatchable_exception ex ->
		    trivial_unify pb substn cM cN)
	| Case (_,p1,c1,cl1), Case (_,p2,c2,cl2) ->
            array_fold_left2 (unirec_rec curenv topconv)
	      (unirec_rec curenv topconv
		  (unirec_rec curenv topconv substn p1 p2) c1 c2) cl1 cl2
	| _ -> trivial_unify pb substn cM cN
  in
    if (not(occur_meta m)) &&
      (if mod_delta then is_fconv (conv_pb_of cv_pb) env sigma m n
       else eq_constr m n)
    then 
      (metas,[])
    else 
      let (mc,ec) = unirec_rec env cv_pb (metas,[]) m n in
	((*sort_eqns*) mc, (*sort_eqns*) ec)

let unify_0 = unify_0_with_initial_metas []

let left = true
let right = false

let pop k = if k=0 then 0 else k-1

let rec unify_with_eta keptside mod_delta env sigma k1 k2 c1 c2 =
  (* Reason up to limited eta-expansion: ci is allowed to start with ki lam *)
  (* Question: try whd_betadeltaiota on ci if ki>0 ? *)
  match kind_of_term c1, kind_of_term c2 with
  | (Lambda (na,t1,c1'), Lambda (_,t2,c2')) ->
      let env' = push_rel_assum (na,t1) env in
      let metas,evars = unify_0 env sigma topconv mod_delta t1 t2 in
      let side,status,(metas',evars') =
	unify_with_eta keptside mod_delta env' sigma (pop k1) (pop k2) c1' c2'
      in (side,status,(metas@metas',evars@evars'))
  | (Lambda (na,t,c1'),_) when k2 > 0 ->
      let env' = push_rel_assum (na,t) env in
      let side = left in (* expansion on the right: we keep the left side *)
      unify_with_eta side mod_delta env' sigma (pop k1) (k2-1) 
	c1' (mkApp (lift 1 c2,[|mkRel 1|]))
  | (_,Lambda (na,t,c2')) when k1 > 0 ->
      let env' = push_rel_assum (na,t) env in
      let side = right in (* expansion on the left: we keep the right side *)
      unify_with_eta side mod_delta env' sigma (k1-1) (pop k2) 
	(mkApp (lift 1 c1,[|mkRel 1|])) c2'
  | _ ->
      (keptside,ConvUpToEta(min k1 k2),
       unify_0 env sigma topconv mod_delta c1 c2)

(* We solved problems [?n =_pb u] (i.e. [u =_(opp pb) ?n]) and [?n =_pb' u'],
   we now compute the problem on [u =? u'] and decide which of u or u' is kept

   Rem: the upper constraint is lost in case u <= ?n <= u' (and symmetrically
   in the case u' <= ?n <= u)
 *)

let merge_instances env sigma mod_delta st1 st2 c1 c2 =
  match (opp_status st1, st2) with
  | (UserGiven, ConvUpToEta n2) ->
      unify_with_eta left mod_delta env sigma 0 n2 c1 c2
  | (ConvUpToEta n1, UserGiven) ->
      unify_with_eta right mod_delta env sigma n1 0 c1 c2
  | (ConvUpToEta n1, ConvUpToEta n2) ->
      let side = left (* arbitrary choice, but agrees with compatibility *) in
      unify_with_eta side mod_delta env sigma n1 n2 c1 c2
  | ((IsSubType | ConvUpToEta _ | UserGiven as oppst1),
     (IsSubType | ConvUpToEta _ | UserGiven)) ->
      let res = unify_0 env sigma Cumul mod_delta c2 c1 in
      if oppst1=st2 then (* arbitrary choice *) (left, st1, res)
      else if st2=IsSubType or st1=UserGiven then (left, st1, res)
      else (right, st2, res)
  | ((IsSuperType | ConvUpToEta _ | UserGiven as oppst1),
     (IsSuperType | ConvUpToEta _ | UserGiven)) ->
      let res = unify_0 env sigma Cumul mod_delta c1 c2 in
      if oppst1=st2 then (* arbitrary choice *) (left, st1, res)
      else if st2=IsSuperType or st1=UserGiven then (left, st1, res)
      else (right, st2, res)
  | (IsSuperType,IsSubType) ->
      (try (left, IsSubType, unify_0 env sigma Cumul mod_delta c2 c1)
       with _ -> (right, IsSubType, unify_0 env sigma Cumul mod_delta c1 c2))
  | (IsSubType,IsSuperType) ->
      (try (left, IsSuperType, unify_0 env sigma Cumul mod_delta c1 c2)
       with _ -> (right, IsSuperType, unify_0 env sigma Cumul mod_delta c2 c1))

(* Unification
 *
 * Procedure:
 * (1) The function [unify mc wc M N] produces two lists:
 *     (a) a list of bindings Meta->RHS
 *     (b) a list of bindings EVAR->RHS
 *
 * The Meta->RHS bindings cannot themselves contain
 * meta-vars, so they get applied eagerly to the other
 * bindings.  This may or may not close off all RHSs of
 * the EVARs.  For each EVAR whose RHS is closed off,
 * we can just apply it, and go on.  For each which
 * is not closed off, we need to do a mimick step -
 * in general, we have something like:
 *
 *      ?X == (c e1 e2 ... ei[Meta(k)] ... en)
 *
 * so we need to do a mimick step, converting ?X
 * into
 *
 *      ?X -> (c ?z1 ... ?zn)
 *
 * of the proper types.  Then, we can decompose the
 * equation into
 *
 *      ?z1 --> e1
 *          ...
 *      ?zi --> ei[Meta(k)]
 *          ...
 *      ?zn --> en
 *
 * and keep on going.  Whenever we find that a R.H.S.
 * is closed, we can, as before, apply the constraint
 * directly.  Whenever we find an equation of the form:
 *
 *      ?z -> Meta(n)
 *
 * we can reverse the equation, put it into our metavar
 * substitution, and keep going.
 *
 * The most efficient mimick possible is, for each
 * Meta-var remaining in the term, to declare a
 * new EVAR of the same type.  This is supposedly
 * determinable from the clausale form context -
 * we look up the metavar, take its type there,
 * and apply the metavar substitution to it, to
 * close it off.  But this might not always work,
 * since other metavars might also need to be resolved. *)

let applyHead env evd n c  = 
  let rec apprec n c cty evd =
    if n = 0 then 
      (evd, c)
    else 
      match kind_of_term (whd_betadeltaiota env (evars_of evd) cty) with
        | Prod (_,c1,c2) ->
            let (evd',evar) = 
	      Evarutil.new_evar evd env ~src:(dummy_loc,GoalEvar) c1 in
	    apprec (n-1) (mkApp(c,[|evar|])) (subst1 evar c2) evd'
	| _ -> error "Apply_Head_Then"
  in 
  apprec n c (Typing.type_of env (evars_of evd) c) evd

let is_mimick_head f =
  match kind_of_term f with
      (Const _|Var _|Rel _|Construct _|Ind _) -> true
    | _ -> false

let w_coerce env c ctyp target evd =
  try
    let j = make_judge c ctyp in
    let tycon = mk_tycon_type target in
    let (evd',j') = Coercion.Default.inh_conv_coerce_to dummy_loc env evd j tycon in
    (evd',j'.uj_val)
  with e when precatchable_exception e ->
    evd,c

let unify_to_type env evd mod_delta c u =
  let sigma = evars_of evd in
  let c = refresh_universes c in
  let t = get_type_of_with_meta env sigma (metas_of evd) c in
  let t = Tacred.hnf_constr env sigma (nf_betaiota (nf_meta evd t)) in
  let u = Tacred.hnf_constr env sigma u in
  try unify_0 env sigma Cumul mod_delta t u
  with e when precatchable_exception e -> ([],[])

let coerce_to_type env evd c u =
  let c = refresh_universes c in
  let t = get_type_of_with_meta env (evars_of evd) (metas_of evd) c in
  w_coerce env c t u evd

let unify_or_coerce_type env evd mod_delta mv c =
  let mvty = Typing.meta_type evd mv in
  (* nf_betaiota was before in type_of - useful to reduce
     types like (x:A)([x]P u) *)
  if occur_meta mvty then
    (evd,c),unify_to_type env evd mod_delta c mvty
  else
    coerce_to_type env evd c mvty,([],[])

let unify_type env evd mod_delta mv c =
  let mvty = Typing.meta_type evd mv in
  if occur_meta mvty then
    unify_to_type env evd mod_delta c mvty
  else ([],[])

(* Move metas that may need coercion at the end of the list of instances *)

let order_metas metas =
  let rec order latemetas = function
  | [] -> List.rev latemetas
  | (_,_,(status,to_type) as meta)::metas ->
      if to_type = CoerceToType then order (meta::latemetas) metas
      else meta :: order latemetas metas
  in order [] metas

(* [w_merge env sigma b metas evars] merges common instances in metas
   or in evars, possibly generating new unification problems; if [b]
   is true, unification of types of metas is required *)

let w_merge env with_types mod_delta metas evars evd =
  let rec w_merge_rec evd metas evars eqns =

    (* Process evars *)
    match evars with
    | ((evn,_ as ev),rhs)::evars' ->
    	if is_defined_evar evd ev then
	  let v = Evd.existential_value (evars_of evd) ev in
	  let (metas',evars'') =
	    unify_0 env (evars_of evd) topconv mod_delta rhs v in
	  w_merge_rec evd (metas'@metas) (evars''@evars') eqns
    	else begin
          let rhs' = subst_meta_instances metas rhs in
	  if occur_evar evn rhs' then error "w_merge: recursive equation";
          match kind_of_term rhs with
	  | App (f,cl) when is_mimick_head f ->
	      (try 
		  w_merge_rec (evar_define env ev rhs' evd)
                    metas evars' eqns
		with ex when precatchable_exception ex ->
                  let evd' =
                    mimick_evar evd mod_delta f (Array.length cl) evn in
		  w_merge_rec evd' metas evars eqns)
          | _ ->
              (* ensure tail recursion in non-mimickable case! *)
	      w_merge_rec (evar_define env ev rhs' evd) metas evars' eqns
	  end
    | [] -> 

    (* Process metas *)
    match metas with
    | (mv,c,(status,to_type))::metas ->
        let ((evd,c),(metas'',evars'')),eqns =
	  if with_types & to_type <> TypeProcessed then
	    if to_type = CoerceToType then
              (* Some coercion may have to be inserted *)
	      (unify_or_coerce_type env evd mod_delta mv c,[])
	    else
              (* No coercion needed: delay the unification of types *)
	      ((evd,c),([],[])),(mv,c)::eqns
	  else 
	    ((evd,c),([],[])),eqns in
    	if meta_defined evd mv then
	  let {rebus=c'},(status',_) = meta_fvalue evd mv in
          let (take_left,st,(metas',evars')) =
	    merge_instances env (evars_of evd) mod_delta status' status c' c
	  in
	  let evd' = 
            if take_left then evd 
            else meta_reassign mv (c,(st,TypeProcessed)) evd 
	  in
          w_merge_rec evd' (metas'@metas@metas'') (evars'@evars'') eqns
    	else
	  let evd' = meta_assign mv (c,(status,TypeProcessed)) evd in
	  w_merge_rec evd' (metas@metas'') evars'' eqns
    | [] -> 

    (* Process type eqns *)
    match eqns with
    | (mv,c)::eqns ->
        let (metas,evars) = unify_type env evd mod_delta mv c in 
        w_merge_rec evd metas evars eqns
    | [] -> evd
		
  and mimick_evar evd mod_delta hdc nargs sp =
    let ev = Evd.find (evars_of evd) sp in
    let sp_env = Global.env_of_context ev.evar_hyps in
    let (evd', c) = applyHead sp_env evd nargs hdc in
    let (mc,ec) =
      unify_0 sp_env (evars_of evd') Cumul mod_delta
        (Retyping.get_type_of sp_env (evars_of evd') c) ev.evar_concl in
    let evd'' = w_merge_rec evd' mc ec [] in
    if (evars_of evd') == (evars_of evd'')
    then Evd.evar_define sp c evd''
    else Evd.evar_define sp (Evarutil.nf_evar (evars_of evd'') c) evd'' in

  (* merge constraints *)
  w_merge_rec evd (order_metas metas) evars []

let w_unify_meta_types env evd =
  let metas,evd = retract_coercible_metas evd in
  w_merge env true true metas [] evd

(* [w_unify env evd M N]
   performs a unification of M and N, generating a bunch of
   unification constraints in the process.  These constraints
   are processed, one-by-one - they may either generate new
   bindings, or, if there is already a binding, new unifications,
   which themselves generate new constraints.  This continues
   until we get failure, or we run out of constraints.
   [clenv_typed_unify M N clenv] expects in addition that expected
   types of metavars are unifiable with the types of their instances    *)

let w_unify_core_0 env with_types cv_pb mod_delta m n evd =
  let (mc1,evd') = retract_coercible_metas evd in
  let (mc2,ec) = 
    unify_0_with_initial_metas mc1 env (evars_of evd') cv_pb mod_delta m n in 
  w_merge env with_types mod_delta mc2 ec evd'

let w_unify_0 env = w_unify_core_0 env false
let w_typed_unify env = w_unify_core_0 env true


(* takes a substitution s, an open term op and a closed term cl
   try to find a subterm of cl which matches op, if op is just a Meta
   FAIL because we cannot find a binding *)

let iter_fail f a =
  let n = Array.length a in 
  let rec ffail i =
    if i = n then error "iter_fail" 
    else
      try f a.(i) 
      with ex when precatchable_exception ex -> ffail (i+1)
  in ffail 0

(* Tries to find an instance of term [cl] in term [op].
   Unifies [cl] to every subterm of [op] until it finds a match.
   Fails if no match is found *)
let w_unify_to_subterm env ?(mod_delta=true) (op,cl) evd =
  let rec matchrec cl =
    let cl = strip_outer_cast cl in
    (try 
       if closed0 cl 
       then w_unify_0 env topconv mod_delta op cl evd,cl
       else error "Bound 1"
     with ex when precatchable_exception ex ->
       (match kind_of_term cl with 
	  | App (f,args) ->
	      let n = Array.length args in
	      assert (n>0);
	      let c1 = mkApp (f,Array.sub args 0 (n-1)) in
	      let c2 = args.(n-1) in
	      (try 
		 matchrec c1
	       with ex when precatchable_exception ex -> 
		 matchrec c2)
          | Case(_,_,c,lf) -> (* does not search in the predicate *)
	       (try 
		 matchrec c
	       with ex when precatchable_exception ex -> 
		 iter_fail matchrec lf)
	  | LetIn(_,c1,_,c2) -> 
	       (try 
		 matchrec c1
	       with ex when precatchable_exception ex -> 
		 matchrec c2)

	  | Fix(_,(_,types,terms)) -> 
	       (try 
		 iter_fail matchrec types
	       with ex when precatchable_exception ex -> 
		 iter_fail matchrec terms)
	
	  | CoFix(_,(_,types,terms)) -> 
	       (try 
		 iter_fail matchrec types
	       with ex when precatchable_exception ex -> 
		 iter_fail matchrec terms)

          | Prod (_,t,c) ->
	      (try 
		 matchrec t 
	       with ex when precatchable_exception ex -> 
		 matchrec c)
          | Lambda (_,t,c) ->
	      (try 
		 matchrec t 
	       with ex when precatchable_exception ex -> 
		 matchrec c)
          | _ -> error "Match_subterm")) 
  in 
  try matchrec cl
  with ex when precatchable_exception ex ->
    raise (PretypeError (env,NoOccurrenceFound op))

let w_unify_to_subterm_list env mod_delta allow_K oplist t evd = 
  List.fold_right 
    (fun op (evd,l) ->
      if isMeta op then
	if allow_K then (evd,op::l)
	else error "Match_subterm"
      else if occur_meta op then
        let (evd',cl) =
          try 
	    (* This is up to delta for subterms w/o metas ... *)
	    w_unify_to_subterm env ~mod_delta (strip_outer_cast op,t) evd
          with PretypeError (env,NoOccurrenceFound _) when allow_K -> (evd,op)
        in 
	(evd',cl::l)
      else if allow_K or dependent op t then
	(evd,op::l)
      else
	(* This is not up to delta ... *)
	raise (PretypeError (env,NoOccurrenceFound op)))
    oplist 
    (evd,[])

let secondOrderAbstraction env mod_delta allow_K typ (p, oplist) evd =
  let sigma = evars_of evd in
  let (evd',cllist) =
    w_unify_to_subterm_list env mod_delta allow_K oplist typ evd in
  let typp = Typing.meta_type evd' p in
  let pred = abstract_list_all env sigma typp typ cllist in
  w_unify_0 env topconv mod_delta (mkMeta p) pred evd'

let w_unify2 env mod_delta allow_K cv_pb ty1 ty2 evd =
  let c1, oplist1 = whd_stack ty1 in
  let c2, oplist2 = whd_stack ty2 in
  match kind_of_term c1, kind_of_term c2 with
    | Meta p1, _ ->
        (* Find the predicate *)
	let evd' =
          secondOrderAbstraction env mod_delta allow_K ty2 (p1,oplist1) evd in 
        (* Resume first order unification *)
	w_unify_0 env cv_pb mod_delta (nf_meta evd' ty1) ty2 evd'
    | _, Meta p2 ->
        (* Find the predicate *)
	let evd' =
          secondOrderAbstraction env mod_delta allow_K ty1 (p2, oplist2) evd in 
        (* Resume first order unification *)
	w_unify_0 env cv_pb mod_delta ty1 (nf_meta evd' ty2) evd'
    | _ -> error "w_unify2"


(* The unique unification algorithm works like this: If the pattern is
   flexible, and the goal has a lambda-abstraction at the head, then
   we do a first-order unification.

   If the pattern is not flexible, then we do a first-order
   unification, too.

   If the pattern is flexible, and the goal doesn't have a
   lambda-abstraction head, then we second-order unification. *)

(* We decide here if first-order or second-order unif is used for Apply *)
(* We apply a term of type (ai:Ai)C and try to solve a goal C'          *)
(* The type C is in clenv.templtyp.rebus with a lot of Meta to solve    *)

(* 3-4-99 [HH] New fo/so choice heuristic :
   In case we have to unify (Meta(1) args) with ([x:A]t args')
   we first try second-order unification and if it fails first-order.
   Before, second-order was used if the type of Meta(1) and [x:A]t was
   convertible and first-order otherwise. But if failed if e.g. the type of
   Meta(1) had meta-variables in it. *)
let w_unify allow_K env cv_pb ?(mod_delta=true) ty1 ty2 evd =
  let cv_pb = of_conv_pb cv_pb in
  let hd1,l1 = whd_stack ty1 in
  let hd2,l2 = whd_stack ty2 in
    match kind_of_term hd1, l1<>[], kind_of_term hd2, l2<>[] with
      (* Pattern case *)
      | (Meta _, true, Lambda _, _ | Lambda _, _, Meta _, true)
	  when List.length l1 = List.length l2 ->
	  (try 
	      w_typed_unify env cv_pb mod_delta ty1 ty2 evd
	    with ex when precatchable_exception ex -> 
	      try 
		w_unify2 env mod_delta allow_K cv_pb ty1 ty2 evd
	      with PretypeError (env,NoOccurrenceFound c) as e -> raise e
		| ex when precatchable_exception ex -> 
		    error "Cannot solve a second-order unification problem")
	    
      (* Second order case *)
      | (Meta _, true, _, _ | _, _, Meta _, true) -> 
	  (try 
	      w_unify2 env mod_delta allow_K cv_pb ty1 ty2 evd
	    with PretypeError (env,NoOccurrenceFound c) as e -> raise e
	      | ex when precatchable_exception ex -> 
		  try 
		    w_typed_unify env cv_pb mod_delta ty1 ty2 evd
		  with ex when precatchable_exception ex -> 
		    error "Cannot solve a second-order unification problem")
	    
      (* General case: try first order *)
      | _ -> w_typed_unify env cv_pb mod_delta ty1 ty2 evd

