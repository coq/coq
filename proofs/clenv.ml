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
open Refiner
open Proof_trees
open Logic
open Reductionops
open Tacmach
open Evar_refiner
open Rawterm
open Pattern
open Tacexpr

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
    raise (RefinerError (CannotGeneralize typ))

(* Generator of metavariables *)
let new_meta =
  let meta_ctr = ref 0 in
  fun () -> incr meta_ctr; !meta_ctr

(* replaces a mapping of existentials into a mapping of metas.
   Problem if an evar appears in the type of another one (pops anomaly) *)
let exist_to_meta sigma (emap, c) =
  let metamap = ref [] in
  let change_exist evar =
    let ty = nf_betaiota (nf_evar emap (existential_type emap evar)) in
    let n = new_meta() in
    metamap := (n, ty) :: !metamap;
    mkMeta n in
  let rec replace c =
    match kind_of_term c with
        Evar (k,_ as ev) when not (Evd.in_dom sigma k) -> change_exist ev
      | _ -> map_constr replace c in
  (!metamap, replace c)

module Metaset = Intset

module Metamap = Intmap

let meta_exists p s = Metaset.fold (fun x b -> (p x) || b) s false

let metamap_in_dom x m =
  try let _ = Metamap.find x m in true with Not_found -> false

let metamap_to_list m =
  Metamap.fold (fun n v l -> (n,v)::l) m []

let metamap_inv m b = 
  Metamap.fold (fun n v l -> if v = b then n::l else l) m []

type 'a freelisted = {
  rebus : 'a;
  freemetas : Metaset.t }

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
      | Meta mv -> Metaset.add mv acc
      | _         -> fold_constr collrec acc c
  in 
  collrec Metaset.empty c

let mk_freelisted c =
  { rebus = c; freemetas = metavars_of c }


(* Clausal environments *)

type clbinding = 
  | Cltyp of constr freelisted
  | Clval of constr freelisted * constr freelisted

type 'a clausenv = {
  templval : constr freelisted;
  templtyp : constr freelisted;
  namenv : identifier Metamap.t;
  env : clbinding Metamap.t;
  hook : 'a }

type wc = named_context sigma


(* [mentions clenv mv0 mv1] is true if mv1 is defined and mentions
 * mv0, or if one of the free vars on mv1's freelist mentions
 * mv0 *)

let mentions clenv mv0 = 
  let rec menrec mv1 =
    try
     (match Metamap.find mv1 clenv.env with
	 | Clval (b,_) -> 
	     Metaset.mem mv0 b.freemetas || meta_exists menrec b.freemetas
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
    namenv = Metamap.empty;
    env =  Metamap.add mv (Cltyp cty_fls) Metamap.empty ;
    hook = wc }
  
let clenv_environments bound c =
  let rec clrec (ne,e,metas) n c =
    match n, kind_of_term c with
      | (Some 0, _) -> (ne, e, List.rev metas, c)
      | (n, Cast (c,_)) -> clrec (ne,e,metas) n c
      | (n, Prod (na,c1,c2)) ->
	  let mv = new_meta () in
	  let dep = dependent (mkRel 1) c2 in
	  let ne' =
	    if dep then
              match na with
		| Anonymous -> ne
		| Name id ->
		    if metamap_in_dom mv ne then begin
		      warning ("Cannot put metavar "^(string_of_meta mv)^
			       " in name-environment twice");
		      ne
		    end else 
		      Metamap.add mv id ne
            else 
	      ne 
	  in
	  let e' = Metamap.add mv (Cltyp (mk_freelisted c1)) e in 
	  clrec (ne',e', (mkMeta mv)::metas) (option_app ((+) (-1)) n)
	    (if dep then (subst1 (mkMeta mv) c2) else c2)
      | (n, LetIn (na,b,_,c)) ->
	  clrec (ne,e,metas) (option_app ((+) (-1)) n) (subst1 b c)
      | (n, _) -> (ne, e, List.rev metas, c)
  in 
  clrec (Metamap.empty,Metamap.empty,[]) bound c

let mk_clenv_from_n wc n (c,cty) =
  let (namenv,env,args,concl) = clenv_environments n cty in
  { templval = mk_freelisted (match args with [] -> c | _ -> applist (c,args));
    templtyp = mk_freelisted concl;
    namenv = namenv;
    env = env;
    hook = wc }

let mk_clenv_from wc = mk_clenv_from_n wc None

let map_fl f cfl = { cfl with rebus=f cfl.rebus }

let map_clb f = function
  | Cltyp cfl -> Cltyp (map_fl f cfl)
  | Clval (cfl1,cfl2) -> Clval (map_fl f cfl1,map_fl f cfl2)

let subst_clenv f sub clenv = 
  { templval = map_fl (subst_mps sub) clenv.templval;
    templtyp = map_fl (subst_mps sub) clenv.templtyp;
    namenv = clenv.namenv;
    env = Metamap.map (map_clb (subst_mps sub)) clenv.env;
    hook = f sub clenv.hook }

let connect_clenv wc clenv = { clenv with hook = wc }

(* Was used in wcclausenv.ml
(* Changes the head of a clenv with (templ,templty) *)
let clenv_change_head (templ,templty) clenv =
  { templval = mk_freelisted templ;
    templtyp = mk_freelisted templty;
    namenv   = clenv.namenv;
    env      = clenv.env;
    hook     = clenv.hook }
*)

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
			      
let clenv_assign mv rhs clenv =
  let rhs_fls = mk_freelisted rhs in 
  if meta_exists (mentions clenv mv) rhs_fls.freemetas then
    error "clenv__assign: circularity in unification";
  try
    (match Metamap.find mv clenv.env with
       | Clval (fls,ty) ->
	   if not (eq_constr fls.rebus rhs) then
	     try 
	       (* Streams are lazy, force evaluation of id to catch Not_found*)
	       let id = Metamap.find mv clenv.namenv in
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
	     env = Metamap.add mv (Clval (rhs_fls,bty)) clenv.env;
	     hook = clenv.hook })
  with Not_found -> 
    error "clenv_assign"

let clenv_val_of clenv mv = 
  let rec valrec mv =
    try
      (match Metamap.find mv clenv.env with
	 | Cltyp _ -> mkMeta mv
	 | Clval(b,_) ->
	     instance (List.map (fun mv' -> (mv',valrec mv')) 
			       (Metaset.elements b.freemetas)) b.rebus)
    with Not_found -> 
      mkMeta mv
  in 
  valrec mv

let clenv_instance clenv b =
  let c_sigma =
    List.map 
      (fun mv -> (mv,clenv_val_of clenv mv)) (Metaset.elements b.freemetas)
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
	     match Metamap.find mv clenv.env with
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
    env = Metamap.add mv (Cltyp (mk_freelisted cty)) clenv.env;
    namenv = (match na with
		| Anonymous -> clenv.namenv
		| Name id -> Metamap.add mv id clenv.namenv);
    hook = clenv.hook }

let clenv_defined clenv mv =
  match Metamap.find mv clenv.env with
    | Clval _ -> true
    | Cltyp _ -> false

let clenv_value clenv mv =
  match Metamap.find mv clenv.env with
    | Clval(b,_) -> b
    | Cltyp _ -> failwith "clenv_value"
	  
let clenv_type clenv mv =
  match Metamap.find mv clenv.env with
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
      (metamap_to_list ce.env)
  in
    Retyping.get_type_of_with_meta (w_env ce.hook) (w_Underlying ce.hook) metamap c

let clenv_instance_type_of ce c =
  clenv_instance ce (mk_freelisted (clenv_type_of ce c))



(* Unification à l'ordre 0 de m et n: [unify_0 mc wc m n] renvoie deux listes:

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

let unify_0 cv_pb wc m n =
  let env = w_env wc
  and sigma = w_Underlying wc in
  let trivial_unify pb substn m n =
    if (not(occur_meta m)) & is_fconv pb env sigma m n then substn
    else error_cannot_unify (m,n) in
  let rec unirec_rec pb ((metasubst,evarsubst) as substn) m n =
    let cM = Evarutil.whd_castappevar sigma m
    and cN = Evarutil.whd_castappevar sigma n in 
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
      | LetIn (_,b,_,c), _ -> unirec_rec pb substn (subst1 b c) cN
      | _, LetIn (_,b,_,c) -> unirec_rec pb substn cM (subst1 b c)

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
          (try
            array_fold_left2 (unirec_rec CONV)
	      (unirec_rec CONV substn f1 f2) l1 l2
	  with ex when catchable_exception ex ->
            trivial_unify pb substn cM cN)
      | Case (_,p1,c1,cl1), Case (_,p2,c2,cl2) ->
          array_fold_left2 (unirec_rec CONV)
	    (unirec_rec CONV (unirec_rec CONV substn p1 p2) c1 c2) cl1 cl2

      | _ -> trivial_unify pb substn cM cN

  in
  if (not(occur_meta m)) & is_fconv cv_pb env sigma m n then 
    ([],[])
  else 
    let (mc,ec) = unirec_rec cv_pb ([],[]) m n in
    ((*sort_eqns*) mc, (*sort_eqns*) ec)


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

let rec mimick_evar hdc nargs sp wc =
  let evd = Evd.map wc.sigma sp in
  let wc' = extract_decl sp wc in
  let (wc'', c) = applyHead nargs hdc wc' in
  let (mc,ec) = unify_0 CONV wc'' (w_type_of wc'' c) (evd.evar_concl) in
  let (wc''',_) = w_resrec mc ec wc'' in
    if wc'== wc'''
    then w_Define sp c wc
    else  
      let wc'''' = restore_decl sp evd wc''' in
	w_Define sp (Evarutil.nf_evar wc''''.sigma c) {it = wc.it ; sigma = wc''''.sigma}

and w_Unify cv_pb m n wc =
  let (mc',ec') = unify_0 cv_pb wc m n in 
  w_resrec mc' ec' wc

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
		    | _ -> raise ex (* error "w_Unify" *)))
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

(* [clenv_merge b metas evars clenv] merges common instances in metas
   or in evars, possibly generating new unification problems; if [b]
   is true, unification of types of metas is required *)

let clenv_merge with_types metas evars clenv =
  let ty_metas = ref [] in
  let ty_evars = ref [] in
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
		let (metas',evars') = unify_0 CONV clenv.hook rhs lhs in
		clenv_resrec (metas'@metas) (evars'@t) clenv
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
              unify_0 CONV clenv.hook (clenv_value clenv mv).rebus n in
            clenv_resrec (metas'@t) evars' clenv
    	  else
            begin
	      if with_types (* or occur_meta mvty *) then
	        (let mvty = clenv_instance_type clenv mv in
		try 
		  let nty = clenv_type_of clenv 
			      (clenv_instance clenv (mk_freelisted n)) in
		  let (mc,ec) = unify_0 CUMUL clenv.hook nty mvty in
                  ty_metas := mc @ !ty_metas;
                  ty_evars := ec @ !ty_evars
		with e when Logic.catchable_exception e -> ());
	      clenv_resrec t [] (clenv_assign mv n clenv)
            end in
  (* merge constraints *)
  let clenv' = clenv_resrec metas evars clenv in
  if with_types then
    (* merge constraints about types: if they fail, don't worry *)
    try clenv_resrec !ty_metas !ty_evars clenv'
    with e when Logic.catchable_exception e -> clenv'
  else clenv'

(* [clenv_unify M N clenv]
   performs a unification of M and N, generating a bunch of
   unification constraints in the process.  These constraints
   are processed, one-by-one - they may either generate new
   bindings, or, if there is already a binding, new unifications,
   which themselves generate new constraints.  This continues
   until we get failure, or we run out of constraints.
   [clenv_typed_unify M N clenv] expects in addition that expected
   types of metavars are unifiable with the types of their instances    *)

let clenv_unify_core_0 with_types cv_pb m n clenv =
  let (mc,ec) = unify_0 cv_pb clenv.hook m n in 
  clenv_merge with_types mc ec clenv

let clenv_unify_0 = clenv_unify_core_0 false
let clenv_typed_unify = clenv_unify_core_0 true


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
       then clenv_unify_0 CONV op cl clause,cl
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
  try matchrec cl
  with ex when catchable_exception ex ->
    raise (RefinerError (NoOccurrenceFound op))

let unify_to_subterm_list allow_K clause oplist t = 
  List.fold_right 
    (fun op (clause,l) ->
      if isMeta op then
	if allow_K then (clause,op::l)
	else error "Match_subterm"
      else if occur_meta op then
        let (clause',cl) =
          try 
	    (* This is up to delta for subterms w/o metas ... *)
	    unify_to_subterm clause (strip_outer_cast op,t)
          with RefinerError (NoOccurrenceFound _) when allow_K -> (clause,op)
        in 
	(clause',cl::l)
      else if not allow_K & not (dependent op t) then
	(* This is not up to delta ... *)
	raise (RefinerError (NoOccurrenceFound op))
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
  clenv_unify_0 CONV (mkMeta p) pred clause'

let clenv_unify2 allow_K cv_pb ty1 ty2 clause =
  let c1, oplist1 = whd_stack ty1 in
  let c2, oplist2 = whd_stack ty2 in
  match kind_of_term c1, kind_of_term c2 with
    | Meta p1, _ ->
        (* Find the predicate *)
	let clause' =
          secondOrderAbstraction allow_K ty2 (p1,oplist1) clause in 
        (* Resume first order unification *)
	clenv_unify_0 cv_pb (clenv_instance_term clause' ty1) ty2 clause'
    | _, Meta p2 ->
        (* Find the predicate *)
	let clause' =
          secondOrderAbstraction allow_K ty1 (p2, oplist2) clause in 
        (* Resume first order unification *)
	clenv_unify_0 cv_pb ty1 (clenv_instance_term clause' ty2) clause'
    | _ -> error "clenv_unify2"


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
    (* Pattern case *)
    | (Meta _, true, Lambda _, _ | Lambda _, _, Meta _, true)
      when List.length l1 = List.length l2 ->
	(try 
	   clenv_typed_unify cv_pb ty1 ty2 clenv
	 with ex when catchable_exception ex -> 
	   try 
	     clenv_unify2 allow_K cv_pb ty1 ty2 clenv
	   with RefinerError (NoOccurrenceFound c) as e -> raise e
	     | ex when catchable_exception ex -> 
	     error "Cannot solve a second-order unification problem")

     (* Second order case *)
     | (Meta _, true, _, _ | _, _, Meta _, true) -> 
	(try 
	   clenv_unify2 allow_K cv_pb ty1 ty2 clenv
	with RefinerError (NoOccurrenceFound c) as e -> raise e
	  | ex when catchable_exception ex -> 
          try 
	     clenv_typed_unify cv_pb ty1 ty2 clenv
          with ex when catchable_exception ex -> 
             error "Cannot solve a second-order unification problem")

     (* General case: try first order *)
     | _ -> clenv_unify_0 cv_pb ty1 ty2 clenv


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
			  else if metamap_in_dom mv ne then begin
			    warning ("Cannot put metavar "^(string_of_meta mv)^
				     " in name-environment twice");
			    ne
			  end else 
			    Metamap.add mv id ne)
          clenv.namenv (metamap_to_list subclenv.namenv);
      env = List.fold_left (fun m (n,v) -> Metamap.add n v m) 
	       clenv.env (metamap_to_list subclenv.env);
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
  match Metamap.find mv clenv.env with
    | Clval(_,b) -> b.freemetas
    | Cltyp b -> b.freemetas

let clenv_template_metavars clenv = clenv.templval.freemetas

(* [clenv_dependent hyps_only clenv]
 * returns a list of the metavars which appear in the template of clenv,
 * and which are dependent, This is computed by taking the metavars in cval,
 * in right-to-left order, and collecting the metavars which appear
 * in their types, and adding in all the metavars appearing in the
 * type of clenv.
 * If [hyps_only] then metavariables occurring in the type are _excluded_ *)

let dependent_metas clenv mvs conclmetas =
  List.fold_right
    (fun mv deps ->
       Metaset.union deps (clenv_metavars clenv mv))
    mvs conclmetas

let clenv_dependent hyps_only clenv =
  let mvs = collect_metas (clenv_instance_template clenv) in
  let ctyp_mvs = metavars_of (clenv_instance_template_type clenv) in
  let deps = dependent_metas clenv mvs ctyp_mvs in
  List.filter
    (fun mv -> Metaset.mem mv deps && not (hyps_only && Metaset.mem mv ctyp_mvs))
    mvs

let clenv_missing c = clenv_dependent true c

(* [clenv_independent clenv]
 * returns a list of metavariables which appear in the term cval,
 * and which are not dependent.  That is, they do not appear in
 * the types of other metavars which are in cval, nor in the type
 * of cval, ctyp. *)

let clenv_independent clenv =
  let mvs = collect_metas (clenv_instance_template clenv) in
  let ctyp_mvs = metavars_of (clenv_instance_template_type clenv) in
  let deps = dependent_metas clenv mvs ctyp_mvs in
  List.filter (fun mv -> not (Metaset.mem mv deps)) mvs

let w_coerce wc c ctyp target =
  let j = make_judge c ctyp in
  let env = w_env wc in
  let isevars = Evarutil.create_evar_defs (w_Underlying wc) in
  let j' = Coercion.inh_conv_coerce_to dummy_loc env isevars j target in
  (* faire quelque chose avec isevars ? *)
  j'.uj_val

let clenv_constrain_dep_args hyps_only clause = function
  | [] -> clause 
  | mlist ->
      let occlist = clenv_dependent hyps_only clause in
      if List.length occlist = List.length mlist then
	List.fold_left2
          (fun clenv k c ->
	    let wc = clause.hook in
	    try
	      let k_typ = w_hnf_constr wc (clenv_instance_type clause k) in
	      let c_typ = w_hnf_constr wc (w_type_of wc c) in
	      let c' = w_coerce wc c c_typ k_typ in
	      clenv_unify true CONV (mkMeta k) c' clenv
	    with _ ->
              clenv_unify true CONV (mkMeta k) c clenv)
          clause occlist mlist
      else 
	error ("Not the right number of missing arguments (expected "
	       ^(string_of_int (List.length occlist))^")")

let clenv_constrain_missing_args mlist clause =
  clenv_constrain_dep_args true clause mlist

let clenv_lookup_name clenv id =
  match metamap_inv clenv.namenv id with
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
    | (loc,b,c)::t ->
	let k =
	  match b with
            | NamedHyp s ->
		if List.exists (fun (_,b',_) -> b=b') t then 
		  errorlabstrm "clenv_match_args" 
		    (str "The variable " ++ pr_id s ++ 
		    str " occurs more than once in binding")
		else
		  clenv_lookup_name clause s
	    | AnonHyp n ->
		if List.exists (fun (_,b',_) -> b=b') t then
		  errorlabstrm "clenv_match_args"
		    (str "The position " ++ int n ++
		    str " occurs more than once in binding");
		try 
		  List.nth mvs (n-1)
		with (Failure _|Invalid_argument _) ->
                  errorlabstrm "clenv_match_args" (str "No such binder")
	in
	let k_typ = w_hnf_constr clause.hook (clenv_instance_type clause k)
	(* nf_betaiota was before in type_of - useful to reduce types like *)
	(* (x:A)([x]P u) *)
	and c_typ = w_hnf_constr clause.hook
          (nf_betaiota (w_type_of clause.hook c)) in
	let cl =
	  (* Try to infer some Meta/Evar from the type of [c] *)
	  try 
            clenv_assign k c (clenv_unify true CUMUL c_typ k_typ clause)
	  with _ ->
	  (* Try to coerce to the type of [k]; cannot merge with the
	     previous case because Coercion does not handle Meta *)
          let c' = w_coerce clause.hook c c_typ k_typ in
	  try clenv_unify true CONV (mkMeta k) c' clause
	  with RefinerError (CannotUnify (m,n)) ->
	    Stdpp.raise_with_loc loc
 	      (RefinerError (CannotUnifyBindingType (m,n)))
	in matchrec cl t
  in 
  matchrec clause s

type arg_bindings = (int * constr) list

let clenv_constrain_with_bindings bl clause =
  if bl = [] then 
    clause 
  else 
    let all_mvs = collect_metas (clenv_template clause).rebus in
    let rec matchrec clause = function
      | []       -> clause
      | (n,c)::t ->
          let k = 
            (try
              if n > 0 then 
		List.nth all_mvs (n-1)
              else if n < 0 then 
		List.nth (List.rev all_mvs) (-n-1)
              else error "clenv_constrain_with_bindings" 
            with Failure _ ->
              errorlabstrm "clenv_constrain_with_bindings"
                (str"Clause did not have " ++ int n ++ str"-th" ++
                str" absolute argument")) in
	  let env = Global.env () in
	  let sigma = Evd.empty in
	  let k_typ = nf_betaiota (clenv_instance_type clause k) in
	  let c_typ = nf_betaiota (w_type_of clause.hook c) in 
	  matchrec
            (clenv_assign k c (clenv_unify true CUMUL c_typ k_typ clause)) t
    in 
    matchrec clause bl


(* [clenv_pose_dependent_evars clenv]
 * For each dependent evar in the clause-env which does not have a value,
 * pose a value for it by constructing a fresh evar.  We do this in
 * left-to-right order, so that every evar's type is always closed w.r.t.
 * metas. *)

let clenv_pose_dependent_evars clenv =
  let dep_mvs = clenv_dependent false clenv in
  List.fold_left
    (fun clenv mv ->
       let evar = Evarutil.new_evar_in_sign (w_env clenv.hook) in
       let (evar_n,_) = destEvar evar in
       let tY = clenv_instance_type clenv mv in
       let clenv' = clenv_wtactic (w_Declare evar_n tY) clenv in
       clenv_assign mv evar clenv')
    clenv
    dep_mvs

(***************************)

let clenv_unique_resolver allow_K clause gl =
  clenv_unify allow_K CUMUL
    (clenv_instance_template_type clause) (pf_concl gl) clause 

let res_pf kONT clenv gls =
  clenv_refine kONT (clenv_unique_resolver false clenv gls) gls
    
let res_pf_cast kONT clenv gls =
  clenv_refine_cast kONT (clenv_unique_resolver false clenv gls) gls

let elim_res_pf kONT clenv allow_K gls =
  clenv_refine_cast kONT (clenv_unique_resolver allow_K clenv gls) gls

let elim_res_pf_THEN_i kONT clenv tac gls =  
  let clenv' = (clenv_unique_resolver true clenv gls) in
  tclTHENLASTn (clenv_refine kONT clenv') (tac clenv') gls

let e_res_pf kONT clenv gls =
  clenv_refine kONT
    (clenv_pose_dependent_evars (clenv_unique_resolver false clenv gls)) gls

(* Clausal environment for an application *)

let make_clenv_binding_gen n wc (c,t) = function
  | ImplicitBindings largs ->
      let clause = mk_clenv_from_n wc n (c,t) in
      clenv_constrain_dep_args (n <> None) clause largs
  | ExplicitBindings lbind ->
      let clause = mk_clenv_rename_from_n wc n (c,t) in
      clenv_match_args lbind clause
  | NoBindings ->
      mk_clenv_from_n wc n (c,t)

let make_clenv_binding_apply wc n = make_clenv_binding_gen (Some n) wc
let make_clenv_binding = make_clenv_binding_gen None

open Printer

let pr_clenv clenv =
  let pr_name mv =
    try 
      let id = Metamap.find mv clenv.namenv in
      (str"[" ++ pr_id id ++ str"]")
    with Not_found -> (mt ())
  in
  let pr_meta_binding = function
    | (mv,Cltyp b) ->
      	hov 0 
	  (pr_meta mv ++ pr_name mv ++ str " : " ++ prterm b.rebus ++ fnl ())
    | (mv,Clval(b,_)) ->
      	hov 0 
	  (pr_meta mv ++ pr_name mv ++ str " := " ++ prterm b.rebus ++ fnl ())
  in
  (str"TEMPL: " ++ prterm clenv.templval.rebus ++
     str" : " ++ prterm clenv.templtyp.rebus ++ fnl () ++
     (prlist pr_meta_binding (metamap_to_list clenv.env)))
