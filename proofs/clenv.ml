(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Instantiate
open Environ
open Evd
open Proof_type
open Proof_trees
open Logic
open Closure
open Reduction
open Reductionops
open Tacmach
open Evar_refiner

(* if lname_typ is [xn,An;..;x1,A1] and l is a list of terms,
   gives [x1:A1]..[xn:An]c' such that c converts to ([x1:A1]..[xn:An]c' l) *)

let abstract_scheme env c l lname_typ =
  List.fold_left2 
    (fun t (locc,a) (na,_,ta) ->
       if occur_meta ta then error "cannot find a type for the generalisation"
       else if occur_meta a then lambda_name env (na,ta,t)
       else lambda_name env (na,ta,subst_term_occ env locc a t))
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
    raise (RefinerError (CannotGeneralize typ))

let rec has_flexible_head env c =
  let (h,l) = whd_stack c in
  match kind_of_term h with
      Const sp ->
        if evaluable_constant sp env then Some (ConstKey sp) else None
    | Var v ->
        if evaluable_named v env then Some (VarKey v) else None
    | Rel n ->
        if evaluable_rel n env then Some (FarRelKey n) else None
    | Case(_,_,i,_) -> has_flexible_head env i
    | Fix ((ri,i),_) ->
        (try has_flexible_head env (List.nth l ri.(i))
         with Invalid_argument _ | Failure _ -> None)
    | _ -> None

let rec reduce_flexible_head env c =
  let (h,l) = whd_stack c in
  match kind_of_term h with
      Const sp -> beta_appvect (constant_value env sp) (Array.of_list l)
    | Var var ->
        (match lookup_named var env with
            (_,Some v,_) -> beta_appvect v (Array.of_list l)
          | _ -> c)
    | Rel n ->
        (match lookup_rel n env with
            (_,Some v,_) -> beta_appvect v (Array.of_list l)
          | _ -> c)
    | Case(ci,p,i,br) ->
        mkApp(mkCase(ci,p,reduce_flexible_head env i,br), Array.of_list l)
    | Fix ((ri,i),_) ->
        let l' =
          list_assign l ri.(i)
            (reduce_flexible_head env (List.nth l ri.(i))) in
        mkApp(h,Array.of_list l')
    | _ -> c

(* Generator of metavariables *)
let meta_ctr=ref 0;;

let new_meta ()=incr meta_ctr;!meta_ctr;;

(* replaces a mapping of existentials into a mapping of metas. *)
let exist_to_meta (emap, c) =
  let subst = ref [] in
  let mmap = ref [] in
  let add_binding (e,ty) =
    let n = new_meta() in
    subst := (e, mkMeta n) :: !subst;
    mmap := (n, ty) :: !mmap in
  List.iter add_binding emap;
  let rec replace c =
    match kind_of_term c with
        Evar k -> List.assoc k !subst
      | _ -> map_constr replace c in
  (!mmap, replace c)

type 'a freelisted = {
  rebus : 'a;
  freemetas : Intset.t }

type clbinding = 
  | Cltyp of constr freelisted
  | Clval of constr freelisted * constr freelisted

type 'a clausenv = {
  templval : constr freelisted;
  templtyp : constr freelisted;
  namenv : identifier Intmap.t;
  env : clbinding Intmap.t;
  hook : 'a }

type wc = named_context sigma

let applyHead n c wc = 
  let rec apprec n c cty wc =
    if n = 0 then 
      (wc,c)
    else 
      match kind_of_term (w_whd_betadeltaiota wc cty) with
        | Prod (_,c1,c2) ->
	    let evar = Evarutil.new_evar_in_sign (w_env wc) in
            let (evar_n, _) = destEvar evar in
	    (compose 
	       (apprec (n-1) (applist(c,[evar])) (subst1 evar c2))
	       (w_Declare evar_n c1))
	    wc
	| _ -> error "Apply_Head_Then"
  in 
  apprec n c (w_type_of wc c) wc

let mimick_evar hdc nargs sp wc =
  let evd = Evd.map wc.sigma sp in
  let wc' = extract_decl sp wc in
  let (wc'', c) = applyHead nargs hdc wc' in
    if wc'==wc''
    then w_Define sp c wc
    else 
      let wc''' = restore_decl sp evd wc'' in
	w_Define sp c {it = wc.it ; sigma = wc'''.sigma}

(*  (w_Focusing_THEN sp
     (applyHead nargs hdc)
     (fun c wc -> w_Define sp c wc)) wc *)


(* Unification à l'ordre 0 de m et n: [unify_0 mc wc m n] renvoie deux listes:

   metasubst:(int*constr)list    récolte les instances des (Meta k)
   evarsubst:(constr*constr)list récolte les instances des (Const "?k")

   Attention : pas d'unification entre les différences instances d'une
   même meta ou evar, il peut rester des doublons *)

let unify_0 allow_red cv_pb wc m n =
  let env = w_env wc
  and sigma = w_Underlying wc in
  let rec unirec_rec pb ((metasubst,evarsubst) as substn) m n =
    let cM = Evarutil.whd_castappevar sigma m
    and cN = Evarutil.whd_castappevar sigma n in 
    try 
      match (kind_of_term cM,kind_of_term cN) with
	| Meta k1, Meta k2 ->
	    if k1 < k2 then (k1,cN)::metasubst,evarsubst
	    else if k1 = k2 then substn
	    else (k2,cM)::metasubst,evarsubst
	| Meta k, _    -> (k,cN)::metasubst,evarsubst
	| _, Meta k    -> (k,cM)::metasubst,evarsubst
	| Evar _, _ -> metasubst,((cM,cN)::evarsubst)
	| _, Evar _ -> metasubst,((cN,cM)::evarsubst)

	| Lambda (_,t1,c1), Lambda (_,t2,c2) ->
	    unirec_rec CONV (unirec_rec CONV substn t1 t2) c1 c2
	| Prod (_,t1,c1), Prod (_,t2,c2) ->
	    unirec_rec pb (unirec_rec CONV substn t1 t2) c1 c2

	| App (f1,l1), App (f2,l2) ->
	    let len1 = Array.length l1
	    and len2 = Array.length l2 in
	    if len1 = len2 then
              array_fold_left2 (unirec_rec CONV)
		(unirec_rec CONV substn f1 f2) l1 l2
	    else if len1 < len2 then
              let extras,restl2 = array_chop (len2-len1) l2 in 
	      array_fold_left2 (unirec_rec CONV)
		(unirec_rec CONV substn f1 (appvect (f2,extras)))
                l1 restl2
	    else 
	      let extras,restl1 = array_chop (len1-len2) l1 in 
	      array_fold_left2 (unirec_rec CONV)
		(unirec_rec CONV substn (appvect (f1,extras)) f2)
                restl1 l2
		
	| Case (_,p1,c1,cl1), Case (_,p2,c2,cl2) ->
            array_fold_left2 (unirec_rec CONV)
	      (unirec_rec CONV (unirec_rec CONV substn p1 p2) c1 c2) cl1 cl2
		
	| _ -> error_cannot_unify (m,n)
	      
    with ex when catchable_exception ex ->
      if (not(occur_meta cM)) & is_fconv pb env sigma cM cN then 
	substn
      else if allow_red then
        match kind_of_term cM, kind_of_term cN with
          | LetIn (_,b,_,c), _ -> unirec_rec pb substn (subst1 b c) cN
	  | _, LetIn (_,b,_,c) -> unirec_rec pb substn cM (subst1 b c)
          | _ ->
              (match (has_flexible_head env cM, has_flexible_head env cN) with
              (None, None) -> raise ex
            | (Some _, None) ->
                unirec_rec pb substn (reduce_flexible_head env cM) cN
            | (None, Some _) ->
                unirec_rec pb substn cM (reduce_flexible_head env cN)
            | (Some k1, Some k2) ->
                if Conv_oracle.oracle_order k1 k2
                then unirec_rec pb substn (reduce_flexible_head env cM) cN
                else unirec_rec pb substn cM (reduce_flexible_head env cN))
      else raise ex

  in
  if (not(occur_meta m)) & is_fconv cv_pb env sigma m n then ([],[])
  else unirec_rec cv_pb ([],[]) m n


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

let rec w_Unify cv_pb m n wc =
  let (mc',ec') = unify_0 true cv_pb wc m n in 
  w_resrec (List.rev mc') (List.rev ec') wc

and w_resrec metas evars wc =
  match evars with
    | [] -> (wc,metas)

    | (lhs,rhs) :: t ->
    match kind_of_term rhs with

      | Meta k -> w_resrec ((k,lhs)::metas) t wc

      | krhs ->
      match kind_of_term lhs with

	| Evar (evn,_) ->
	    if w_defined_evar wc evn then
	      let (wc',metas') = w_Unify CONV rhs lhs wc in 
	      w_resrec (metas@metas') t wc'
	    else
	      (try 
		 w_resrec metas t (w_Define evn rhs wc)
               with ex when catchable_exception ex ->
		 (match krhs with
             	    | App (f,cl) when isConst f ->
			let wc' = mimick_evar f (Array.length cl) evn wc in
			w_resrec metas evars wc'
		    | _ -> error "w_Unify"))
	| _ -> anomaly "w_resrec"


(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

(* let unifyTerms m n = walking (fun wc -> fst (w_Unify CONV m n [] wc)) *)
let unifyTerms m n gls = 
  tclIDTAC {it = gls.it; 
	    sigma = (get_gc (fst (w_Unify CONV m n (Refiner.project_with_focus gls))))}

let unify m gls =
  let n = pf_concl gls in unifyTerms m n gls

(* collects all metavar occurences, in left-to-right order, preserving
 * repetitions and all. *)

let collect_metas c = 
  let rec collrec acc c =
    match kind_of_term c with
      | Meta mv -> mv::acc
      | _         -> fold_constr collrec acc c
  in
  List.rev (collrec [] c)

let metavars_of c =  
  let rec collrec acc c =
    match kind_of_term c with
      | Meta mv -> Intset.add mv acc
      | _         -> fold_constr collrec acc c
  in 
  collrec Intset.empty c

let mk_freelisted c =
  { rebus = c; freemetas = metavars_of c }

(* [mentions clenv mv0 mv1] is true if mv1 is defined and mentions
 * mv0, or if one of the free vars on mv1's freelist mentions
 * mv0 *)

let mentions clenv mv0 = 
  let rec menrec mv1 =
    try
      (match Intmap.find mv1 clenv.env with
	 | Clval (b,_) -> 
	     Intset.mem mv0 b.freemetas || intset_exists menrec b.freemetas
	 | Cltyp _ -> false)
    with Not_found -> 
      false
  in 
  menrec

(* Creates a new clause-environment, whose template has a given
 * type, CTY.  This is not all that useful, since not very often
 * does one know the type of the clause - one usually only has
 * a clause which one wants to backchain thru. *)

let mk_clenv wc cty =
  let mv = new_meta () in
  let cty_fls = mk_freelisted cty in 
  { templval = mk_freelisted (mkMeta mv);
    templtyp = cty_fls;
    namenv = Intmap.empty;
    env =  Intmap.add mv (Cltyp cty_fls) Intmap.empty ;
    hook = wc }
  
let clenv_environments bound c =
  let rec clrec (ne,e,metas) n c =
    match n, kind_of_term c with
      | (0, _) -> (ne, e, List.rev metas, c)
      | (n, Cast (c,_)) -> clrec (ne,e,metas) n c
      | (n, Prod (na,c1,c2)) ->
	  let mv = new_meta () in
	  let dep = dependent (mkRel 1) c2 in
	  let ne' =
	    if dep then
              match na with
		| Anonymous -> ne
		| Name id ->
		    if intmap_in_dom mv ne then begin
		      warning ("Cannot put metavar "^(string_of_int mv)^
			       " in name-environment twice");
		      ne
		    end else 
		      Intmap.add mv id ne
            else 
	      ne 
	  in
	  let e' = Intmap.add mv (Cltyp (mk_freelisted c1)) e in 
	  clrec (ne',e', (mkMeta mv)::metas) (n-1)
	    (if dep then (subst1 (mkMeta mv) c2) else c2)
      | (n, LetIn (na,b,_,c)) -> clrec (ne,e,metas) (n-1) (subst1 b c)
      | (n, _) -> (ne, e, List.rev metas, c)
  in 
  clrec (Intmap.empty,Intmap.empty,[]) bound c

let mk_clenv_from_n wc n (c,cty) =
  let (namenv,env,args,concl) = clenv_environments n cty in
  { templval = mk_freelisted (match args with [] -> c | _ -> applist (c,args));
    templtyp = mk_freelisted concl;
    namenv = namenv;
    env = env;
    hook = wc }

let mk_clenv_from wc (c,cty) =
  let (namenv,env,args,concl) = clenv_environments (-1) cty in
  { templval = mk_freelisted (match args with [] -> c | _ -> applist (c,args));
    templtyp = mk_freelisted concl;
    namenv = namenv;
    env = env;
    hook = wc }

let connect_clenv wc clenv =
  { templval = clenv.templval;
    templtyp = clenv.templtyp;
    namenv = clenv.namenv;
    env = clenv.env;
    hook = wc }

(* Changes the head of a clenv with (templ,templty) *)
let clenv_change_head (templ,templty) clenv =
  { templval = mk_freelisted templ;
    templtyp = mk_freelisted templty;
    namenv   = clenv.namenv;
    env      = clenv.env;
    hook     = clenv.hook }

let mk_clenv_hnf_constr_type_of wc t =
  mk_clenv_from wc (t,w_hnf_constr wc (w_type_of wc t))

let mk_clenv_rename_from wc (c,t) = 
  mk_clenv_from wc (c,rename_bound_var (w_env wc) [] t)

let mk_clenv_rename_from_n wc n (c,t) = 
  mk_clenv_from_n wc n (c,rename_bound_var (w_env wc) [] t)
    
let mk_clenv_rename_type_of wc t =
  mk_clenv_from wc (t,rename_bound_var (w_env wc) [] (w_type_of wc t))
    
let mk_clenv_rename_hnf_constr_type_of wc t =
  mk_clenv_from wc
    (t,rename_bound_var (w_env wc) [] (w_hnf_constr wc (w_type_of wc t)))

let mk_clenv_type_of wc t = mk_clenv_from wc (t,w_type_of wc t)
			      
let mk_clenv_printable_type_of = mk_clenv_type_of
				   
let clenv_assign mv rhs clenv =
  let rhs_fls = mk_freelisted rhs in 
  if intset_exists (mentions clenv mv) rhs_fls.freemetas then
    error "clenv__assign: circularity in unification";
  try
    (match Intmap.find mv clenv.env with
       | Clval (fls,ty) ->
	   if not (eq_constr fls.rebus rhs) then
	     try 
	       (* Streams are lazy, force evaluation of id to catch Not_found*)
	       let id = Intmap.find mv clenv.namenv in
	       errorlabstrm "clenv_assign"
		 (str "An incompatible instantiation has already been found for " ++ 
		    pr_id id)
	     with Not_found ->
	       anomaly "clenv_assign: non dependent metavar already assigned"
	   else
	     clenv
       | Cltyp bty -> 
	   { templval = clenv.templval;
	     templtyp = clenv.templtyp;
	     namenv = clenv.namenv;
	     env = Intmap.add mv (Clval (rhs_fls,bty)) clenv.env;
	     hook = clenv.hook })
  with Not_found -> 
    error "clenv_assign"

let clenv_val_of clenv mv = 
  let rec valrec mv =
    try
      (match Intmap.find mv clenv.env with
	 | Cltyp _ -> mkMeta mv
	 | Clval(b,_) ->
	     instance (List.map (fun mv' -> (mv',valrec mv')) 
			       (Intset.elements b.freemetas)) b.rebus)
    with Not_found -> 
      mkMeta mv
  in 
  valrec mv

let clenv_instance clenv b =
  let c_sigma =
    List.map 
      (fun mv -> (mv,clenv_val_of clenv mv)) (Intset.elements b.freemetas)
  in 
  instance c_sigma b.rebus
    
let clenv_instance_term clenv c =
  clenv_instance clenv (mk_freelisted c)


(* This function put casts around metavariables whose type could not be
 * infered by the refiner, that is head of applications, predicates and
 * subject of Cases.
 * Does check that the casted type is closed. Anyway, the refiner would
 * fail in this case... *)

let clenv_cast_meta clenv = 
  let rec crec u =
    match kind_of_term u with
      | App _ | Case _ -> crec_hd u
      | Cast (c,_) when isMeta c -> u
      | _  -> map_constr crec u
	    
  and crec_hd u =
    match kind_of_term (strip_outer_cast u) with
      | Meta mv ->
	  (try 
	     match Intmap.find mv clenv.env with
               | Cltyp b ->
		   let b' = clenv_instance clenv b in 
		   if occur_meta b' then u else mkCast (mkMeta mv, b')
	       | Clval(_) -> u
	   with Not_found -> 
	     u)
      | App(f,args) -> mkApp (crec_hd f, Array.map crec args)
      | Case(ci,p,c,br) ->
	  mkCase (ci, crec_hd p, crec_hd c, Array.map crec br)
      | _ -> u
  in 
  crec


(* [clenv_pose (na,mv,cty) clenv]
 * returns a new clausenv which has added to it the metavar MV,
 * with type CTY.  the name NA, if it is not ANONYMOUS, will
 * be entered into the name-map, as a way of accessing the new
 * metavar. *)

let clenv_pose (na,mv,cty) clenv =
  { templval = clenv.templval;
    templtyp = clenv.templtyp;
    env = Intmap.add mv (Cltyp (mk_freelisted cty)) clenv.env;
    namenv = (match na with
		| Anonymous -> clenv.namenv
		| Name id -> Intmap.add mv id clenv.namenv);
    hook = clenv.hook }

let clenv_defined clenv mv =
  match Intmap.find mv clenv.env with
    | Clval _ -> true
    | Cltyp _ -> false

let clenv_value clenv mv =
  match Intmap.find mv clenv.env with
    | Clval(b,_) -> b
    | Cltyp _ -> failwith "clenv_value"
	  
let clenv_type clenv mv =
  match Intmap.find mv clenv.env with
    | Cltyp b -> b
    | Clval(_,b) -> b
	  
let clenv_template clenv = clenv.templval

let clenv_template_type clenv = clenv.templtyp

let clenv_instance_value clenv mv =
  clenv_instance clenv (clenv_value clenv mv)
    
let clenv_instance_type clenv mv =
  clenv_instance clenv (clenv_type clenv mv)
    
let clenv_instance_template clenv =
  clenv_instance clenv (clenv_template clenv)
    
let clenv_instance_template_type clenv =
  clenv_instance clenv (clenv_template_type clenv)
    
let clenv_wtactic wt clenv =
  { templval = clenv.templval;
    templtyp = clenv.templtyp;
    namenv = clenv.namenv;
    env = clenv.env;
    hook = wt clenv.hook }

let clenv_type_of ce c =
  let metamap =
    List.map 
      (function
	 | (n,Clval(_,typ)) -> (n,typ.rebus)
         | (n,Cltyp typ)    -> (n,typ.rebus))
      (intmap_to_list ce.env)
  in
    Retyping.get_type_of_with_meta (w_env ce.hook) (w_Underlying ce.hook) metamap c

let clenv_instance_type_of ce c =
  clenv_instance ce (mk_freelisted (clenv_type_of ce c))

(* [clenv_merge b metas evars clenv] merges common instances in metas
   or in evars, possibly generating new unification problems; if [b]
   is true, unification of types of metas is required *)

let clenv_merge with_types =
  let rec clenv_resrec metas evars clenv =
    match (evars,metas) with
      | ([], []) -> clenv

      | ((lhs,rhs)::t, metas) ->
      (match kind_of_term rhs with

	| Meta k -> clenv_resrec ((k,lhs)::metas) t clenv

	| krhs ->
        (match kind_of_term lhs with

	  | Evar (evn,_) ->
    	      if w_defined_evar clenv.hook evn then
		let (metas',evars') = unify_0 true CONV clenv.hook rhs lhs in
		clenv_resrec (List.rev metas'@metas) (List.rev evars'@t) clenv
    	      else begin
		let rhs' = 
		  if occur_meta rhs then subst_meta metas rhs else rhs 
		in
		if occur_evar evn rhs' then error "w_Unify";
		try 
		  clenv_resrec metas t 
		    (clenv_wtactic (w_Define evn rhs') clenv)
		with ex when catchable_exception ex ->
		  (match krhs with
		     | App (f,cl) when isConst f or isConstruct f ->
			 clenv_resrec metas evars 
			   (clenv_wtactic
			      (mimick_evar f (Array.length cl) evn)
			      clenv)
           	     | _ -> error "w_Unify")
	      end

	  | _ -> anomaly "clenv_resrec"))

      | ([], (mv,n)::t) ->
    	  if clenv_defined clenv mv then
            let (metas',evars') =
              unify_0 true CONV clenv.hook (clenv_value clenv mv).rebus n in
            clenv_resrec (List.rev metas'@t) (List.rev evars') clenv
    	  else
	    let mc,ec =
	      let mvty = clenv_instance_type clenv mv in
	      if with_types (* or occur_meta mvty *) then
		(try 
		let nty = clenv_type_of clenv 
			    (clenv_instance clenv (mk_freelisted n)) in
		unify_0 true CUMUL clenv.hook nty mvty
		with e when Logic.catchable_exception e -> ([],[]))
	      else ([],[]) in
	    clenv_resrec (List.rev mc@t) (List.rev ec)
              (clenv_assign mv n clenv)

  in clenv_resrec

(* [clenv_unify M N clenv]
   performs a unification of M and N, generating a bunch of
   unification constraints in the process.  These constraints
   are processed, one-by-one - they may either generate new
   bindings, or, if there is already a binding, new unifications,
   which themselves generate new constraints.  This continues
   until we get failure, or we run out of constraints.
   [clenv_typed_unify M N clenv] expects in addition that expected
   types of metavars are unifiable with the types of their instances    *)

let clenv_unify_core_0 allow_red with_types cv_pb m n clenv =
  let (mc,ec) = unify_0 allow_red cv_pb clenv.hook m n in 
  clenv_merge with_types (List.rev mc) (List.rev ec) clenv

let clenv_unify_0 allow_red = clenv_unify_core_0 allow_red false
let clenv_typed_unify = clenv_unify_core_0 false true


(* takes a substitution s, an open term op and a closed term cl
   try to find a subterm of cl which matches op, if op is just a Meta
   FAIL because we cannot find a binding *)

let iter_fail f a =
  let n = Array.length a in 
  let rec ffail i =
    if i = n then error "iter_fail" 
    else
      try f a.(i) 
      with ex when catchable_exception ex -> ffail (i+1)
  in ffail 0

(* Tries to find an instance of term [cl] in term [op].
   Unifies [cl] to every subterm of [op] until it finds a match.
   Fails if no match is found *)
let unify_to_subterm clause (op,cl) =
  let rec matchrec cl =
    let cl = strip_outer_cast cl in
    (try 
       if closed0 cl 
       then clenv_unify_0 false CONV op cl clause,cl
       else error "Bound 1"
     with ex when catchable_exception ex ->
       (match kind_of_term cl with 
	  | App (f,args) ->
	      let n = Array.length args in
	      assert (n>0);
	      let c1 = mkApp (f,Array.sub args 0 (n-1)) in
	      let c2 = args.(n-1) in
	      (try 
		 matchrec c1
	       with ex when catchable_exception ex -> 
		 matchrec c2)
          | Case(_,_,c,lf) -> (* does not search in the predicate *)
	       (try 
		 matchrec c
	       with ex when catchable_exception ex -> 
		 iter_fail matchrec lf)
	  | LetIn(_,c1,_,c2) -> 
	       (try 
		 matchrec c1
	       with ex when catchable_exception ex -> 
		 matchrec c2)

	  | Fix(_,(_,types,terms)) -> 
	       (try 
		 iter_fail matchrec types
	       with ex when catchable_exception ex -> 
		 iter_fail matchrec terms)
	
	  | CoFix(_,(_,types,terms)) -> 
	       (try 
		 iter_fail matchrec types
	       with ex when catchable_exception ex -> 
		 iter_fail matchrec terms)

          | Prod (_,t,c) ->
	      (try 
		 matchrec t 
	       with ex when catchable_exception ex -> 
		 matchrec c)
          | Lambda (_,t,c) ->
	      (try 
		 matchrec t 
	       with ex when catchable_exception ex -> 
		 matchrec c)
          | _ -> error "Match_subterm")) 
  in 
  if isMeta op then error "Match_subterm";
  matchrec cl

(* Possibly gives K-terms in case the operator does not contain 
   a meta : BUG ?? *)
let unify_to_subterm_list allow_K clause oplist t = 
  List.fold_right 
    (fun op (clause,l) -> 
       if occur_meta op then 
         let (clause',cl) =
           (try 
	      unify_to_subterm clause (strip_outer_cast op,t)
            with e when catchable_exception e ->
              if allow_K then (clause,op) else raise e)
         in 
	 (clause',cl::l)
       else 
	 (clause,op::l)) 
    oplist 
    (clause,[])

let secondOrderAbstraction allow_K typ (p, oplist) clause =
  let env = w_env clause.hook in
  let sigma = w_Underlying clause.hook in
  let (clause',cllist) = unify_to_subterm_list allow_K clause oplist typ in
  let typp = clenv_instance_type clause' p in 
  let pred = abstract_list_all env sigma typp typ cllist in
  clenv_unify_0 false CONV (mkMeta p) pred clause'

let clenv_unify_2 allow_K cv_pb ty1 ty2 clause =
  let c1, oplist1 = whd_stack ty1 in
  let c2, oplist2 = whd_stack ty2 in
  match kind_of_term c1, kind_of_term c2 with
    | Meta p1, _ ->
        (* Find the predicate *)
	let clause' =
          secondOrderAbstraction allow_K ty2 (p1,oplist1) clause in 
        (* Resume first order unification *)
	clenv_unify_0 false cv_pb (clenv_instance_term clause' ty1) ty2 clause'
    | _, Meta p2 ->
        (* Find the predicate *)
	let clause' =
          secondOrderAbstraction allow_K ty1 (p2, oplist2) clause in 
        (* Resume first order unification *)
	clenv_unify_0 false cv_pb ty1 (clenv_instance_term clause' ty2) clause'
    | _ -> error "clenv_unify_2"


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
let clenv_unify allow_K cv_pb ty1 ty2 clenv =
  let hd1,l1 = whd_stack ty1 in
  let hd2,l2 = whd_stack ty2 in
  match kind_of_term hd1, l1<>[], kind_of_term hd2, l2<>[] with
    | (Meta _, true, Lambda _, _ | Lambda _, _, Meta _, true) ->
	(try 
	   clenv_typed_unify cv_pb ty1 ty2 clenv
	 with ex when catchable_exception ex -> 
	   try 
	     clenv_unify_2 allow_K cv_pb ty1 ty2 clenv
	   with ex when catchable_exception ex -> 
	     error "Cannot solve a second-order unification problem")

     | (Meta _, true, _, _ | _, _, Meta _, true) -> 
	(try 
	   clenv_unify_2 allow_K cv_pb ty1 ty2 clenv
         with ex when catchable_exception ex -> 
           try 
	     clenv_typed_unify cv_pb ty1 ty2 clenv
           with ex when catchable_exception ex -> 
             error "Cannot solve a second-order unification problem")

     | _ -> clenv_unify_0 false cv_pb ty1 ty2 clenv


(* [clenv_bchain mv clenv' clenv]
 *
 * Resolves the value of "mv" (which must be undefined) in clenv to be
 * the template of clenv' be the value "c", applied to "n" fresh
 * metavars, whose types are chosen by destructing "clf", which should
 * be a clausale forme generated from the type of "c".  The process of
 * resolution can cause unification of already-existing metavars, and
 * of the fresh ones which get created.  This operation is a composite
 * of operations which pose new metavars, perform unification on
 * terms, and make bindings.  *)

let clenv_bchain mv subclenv clenv =
  (* Add the metavars of [subclenv] to [clenv], with their name-environment *)
  let clenv' =
    { templval = clenv.templval;
      templtyp = clenv.templtyp;
      namenv =
	List.fold_left (fun ne (mv,id) ->
			  if clenv_defined subclenv mv then 
			    ne
			  else if intmap_in_dom mv ne then begin
			    warning ("Cannot put metavar "^(string_of_int mv)^
				     " in name-environment twice");
			    ne
			  end else 
			    Intmap.add mv id ne)
          clenv.namenv (intmap_to_list subclenv.namenv);
      env = List.fold_left (fun m (n,v) -> Intmap.add n v m) 
	       clenv.env (intmap_to_list subclenv.env);
      hook = clenv.hook } 
  in
  (* unify the type of the template of [subclenv] with the type of [mv] *)
  let clenv'' =
    clenv_unify true CUMUL
      (clenv_instance clenv' (clenv_template_type subclenv))
      (clenv_instance_type clenv' mv)
      clenv' 
  in
  (* assign the metavar *)
  let clenv''' =
    clenv_assign mv (clenv_instance clenv' (clenv_template subclenv)) clenv''
  in 
  clenv'''


(* swaps the "hooks" in [clenv1] and [clenv2], so we can then use
   backchain to hook them together *)

let clenv_swap clenv1 clenv2 =
  let clenv1' = { templval = clenv1.templval;
		  templtyp = clenv1.templtyp;
		  namenv = clenv1.namenv;
		  env = clenv1.env;
		  hook = clenv2.hook} 
  and clenv2' = { templval = clenv2.templval;
		  templtyp = clenv2.templtyp;
		  namenv = clenv2.namenv;
		  env = clenv2.env;
		  hook = clenv1.hook}
  in 
  (clenv1',clenv2')

let clenv_fchain mv nextclenv clenv =
  let (clenv',nextclenv') = clenv_swap clenv nextclenv in 
  clenv_bchain mv clenv' nextclenv'

let clenv_refine kONT clenv gls =
  tclTHEN
    (kONT clenv.hook) 
    (refine (clenv_instance_template clenv)) gls

let clenv_refine_cast kONT clenv gls =
  tclTHEN
    (kONT clenv.hook) 
    (refine (clenv_cast_meta clenv (clenv_instance_template clenv)))
    gls

(* [clenv_metavars clenv mv]
 * returns a list of the metavars which appear in the type of
 * the metavar mv.  The list is unordered. *)

let clenv_metavars clenv mv =
  match Intmap.find mv clenv.env with
    | Clval(_,b) -> b.freemetas
    | Cltyp b -> b.freemetas

let clenv_template_metavars clenv = clenv.templval.freemetas

(* [clenv_dependent clenv cval ctyp]
 * returns a list of the metavariables which appear in the term cval,
 * and which are dependent, This is computed by taking the metavars in cval,
 * in right-to-left order, and collecting the metavars which appear
 * in their types, and adding in all the metavars appearing in ctyp, the
 * type of cval. *)

let dependent_metas clenv mvs conclmetas =
  List.fold_right
    (fun mv deps ->
       Intset.union deps (clenv_metavars clenv mv))
    mvs conclmetas

let clenv_dependent clenv =
  let mvs = collect_metas (clenv_instance_template clenv) in
  let ctyp_mvs = metavars_of (clenv_instance_template_type clenv) in
  let deps = dependent_metas clenv mvs ctyp_mvs in
  List.filter (fun mv -> Intset.mem mv deps) mvs


(* [clenv_independent clenv]
 * returns a list of metavariables which appear in the term cval,
 * and which are not dependent.  That is, they do not appear in
 * the types of other metavars which are in cval, nor in the type
 * of cval, ctyp. *)

let clenv_independent clenv =
  let mvs = collect_metas (clenv_instance_template clenv) in
  let ctyp_mvs = metavars_of (clenv_instance_template_type clenv) in
  let deps = dependent_metas clenv mvs ctyp_mvs in
  List.filter (fun mv -> not (Intset.mem mv deps)) mvs


(* [clenv_missing clenv]
 * returns a list of the metavariables which appear in the term cval,
 * and which are dependent, and do NOT appear in ctyp. *)

let clenv_missing clenv =
  let mvs = collect_metas (clenv_instance_template clenv) in
  let ctyp_mvs = metavars_of (clenv_instance_template_type clenv) in
  let deps = dependent_metas clenv mvs ctyp_mvs in
  List.filter 
    (fun n -> Intset.mem n deps && not (Intset.mem n ctyp_mvs))
    mvs

let clenv_constrain_missing_args mlist clause =
  if mlist = [] then 
    clause 
  else
    let occlist = clenv_missing clause in
    if List.length occlist = List.length mlist then
      List.fold_left2
        (fun clenv occ m -> clenv_unify true CONV (mkMeta occ) m clenv)
        clause occlist mlist
    else 
      error ("Not the right number of missing arguments (expected "
	     ^(string_of_int (List.length occlist))^")")

let clenv_constrain_dep_args mlist clause =
  if mlist = [] then 
    clause 
  else
    let occlist = clenv_dependent clause in
    if List.length occlist = List.length mlist then
      List.fold_left2
        (fun clenv occ m -> clenv_unify true CONV (mkMeta occ) m clenv)
        clause occlist mlist
    else 
      error ("Not the right number of missing arguments (expected "
	     ^(string_of_int (List.length occlist))^")")

let clenv_constrain_dep_args_of mv mlist clause =
  if mlist = [] then 
    clause 
  else
    let occlist = clenv_dependent clause in
    if List.length occlist = List.length mlist then
      List.fold_left2
        (fun clenv occ m -> clenv_unify true CONV (mkMeta occ) m clenv)
        clause occlist mlist
    else 
      error ("clenv_constrain_dep_args_of: Not the right number " ^ 
	     "of dependent arguments")

let clenv_lookup_name clenv id =
  match intmap_inv clenv.namenv id with
    | []  -> 
	errorlabstrm "clenv_lookup_name"
          (str"No such bound variable " ++ pr_id id)
    | [n] -> 
	n
    |  _  -> 
	 anomaly "clenv_lookup_name: a name occurs more than once in clause"

let clenv_match_args s clause =
  let mvs = clenv_independent clause in 
  let rec matchrec clause = function
    | [] -> clause
    | (b,c)::t ->
	let k =
	  (match b with
             | Dep s ->
		 if List.mem_assoc b t then 
		   errorlabstrm "clenv_match_args" 
		     (str "The variable " ++ pr_id s ++ 
			str " occurs more than once in binding")
		 else
		   clenv_lookup_name clause s
	     | NoDep n ->
		 if List.mem_assoc b t then errorlabstrm "clenv_match_args"
		   (str "The position " ++ int n ++
		      str " occurs more than once in binding");
		 (try 
		    List.nth mvs (n-1)
		  with (Failure _|Invalid_argument _) ->
                    errorlabstrm "clenv_match_args" (str "No such binder"))
	     | Com -> anomaly "No free term in clenv_match_args")
	in
	let k_typ = w_hnf_constr clause.hook (clenv_instance_type clause k)
	and c_typ = w_hnf_constr clause.hook (w_type_of clause.hook c) in
	matchrec
          (clenv_assign k c (clenv_unify true CUMUL c_typ k_typ clause)) t
  in 
  matchrec clause s


(* [clenv_pose_dependent_evars clenv]
 * For each dependent evar in the clause-env which does not have a value,
 * pose a value for it by constructing a fresh evar.  We do this in
 * left-to-right order, so that every evar's type is always closed w.r.t.
 * metas. *)

let clenv_pose_dependent_evars clenv =
  let dep_mvs = clenv_dependent clenv in
  List.fold_left
    (fun clenv mv ->
       let evar = Evarutil.new_evar_in_sign (w_env clenv.hook) in
       let (evar_n,_) = destEvar evar in
       let tY = clenv_instance_type clenv mv in
       let clenv' = clenv_wtactic (w_Declare evar_n tY) clenv in
       clenv_assign mv evar clenv')
    clenv
    dep_mvs

let clenv_add_sign (id,sign) clenv =
  { templval = clenv.templval;
    templtyp = clenv.templtyp;
    namenv = clenv.namenv;
    env = clenv.env;
    hook = w_add_sign (id,sign) clenv.hook}

(***************************)

let clenv_unique_resolver allow_K clause gl =
  clenv_unify allow_K CUMUL
    (clenv_instance_template_type clause) (pf_concl gl) clause 

let res_pf kONT clenv gls =
  clenv_refine kONT (clenv_unique_resolver false clenv gls) gls
    
let res_pf_cast kONT clenv gls =
  clenv_refine_cast kONT (clenv_unique_resolver false clenv gls) gls

let elim_res_pf kONT clenv gls =
  clenv_refine_cast kONT (clenv_unique_resolver true clenv gls) gls

let e_res_pf kONT clenv gls =
  clenv_refine kONT
    (clenv_pose_dependent_evars (clenv_unique_resolver false clenv gls)) gls

(* Clausal environment for an application *)

let collect_com lbind = 
  map_succeed (function (Com,c)->c | _ -> failwith "Com") lbind

let make_clenv_binding_apply wc n (c,t) lbind = 
  let largs = collect_com lbind in
  let lcomargs = List.length largs in
  if lcomargs = List.length lbind then 
    let clause = mk_clenv_from_n wc n (c,t) in
    clenv_constrain_missing_args largs clause
  else if lcomargs = 0 then 
    let clause = mk_clenv_rename_from_n wc n (c,t) in
    clenv_match_args lbind clause
  else 
    errorlabstrm "make_clenv_bindings"
      (str "Cannot mix bindings and free associations")

let make_clenv_binding wc (c,t) lbind = 
  let largs    = collect_com lbind in
  let lcomargs = List.length largs in 
  if lcomargs = List.length lbind then 
    let clause = mk_clenv_from wc (c,t) in  
    clenv_constrain_dep_args largs clause
  else if lcomargs = 0 then 
    let clause = mk_clenv_rename_from wc (c,t) in  
    clenv_match_args lbind clause
  else 
    errorlabstrm "make_clenv_bindings"
      (str "Cannot mix bindings and free associations")

open Printer

let pr_clenv clenv =
  let pr_name mv =
    try 
      let id = Intmap.find mv clenv.namenv in
      (str"[" ++ pr_id id ++ str"]")
    with Not_found -> (mt ())
  in
  let pr_meta_binding = function
    | (mv,Cltyp b) ->
      	hov 0 (int mv ++ pr_name mv ++ str " : " ++ prterm b.rebus ++ fnl ())
    | (mv,Clval(b,_)) ->
      	hov 0 (int mv ++ pr_name mv ++ str " := " ++ prterm b.rebus ++ fnl ())
  in
  (str"TEMPL: " ++ prterm clenv.templval.rebus ++
     str" : " ++ prterm clenv.templtyp.rebus ++ fnl () ++
     (prlist pr_meta_binding (intmap_to_list clenv.env)))
