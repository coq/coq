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
open Reductionops
open Rawterm
open Pattern
open Evarutil
open Pretype_errors

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


(*******************************)

type maps = evar_map * meta_map

(* [w_Define evd sp c]
 *
 * Defines evar [sp] with term [c] in evar context [evd].
 * [c] is typed in the context of [sp] and evar context [evd] with
 * [sp] removed to avoid circular definitions.
 * No unification is performed in order to assert that [c] has the
 * correct type.
 *)
let w_Define sp c evd =
  let sigma = evars_of evd in
  if Evd.is_defined sigma sp then
    error "Unify.w_Define: cannot define evar twice";
  let spdecl = Evd.map sigma sp in
  let env = evar_env spdecl in
  let _ =
    try Typing.check env (Evd.rmv sigma sp) c spdecl.evar_concl
    with Not_found ->
      error "Instantiation contains unlegal variables" in
  let spdecl' = { spdecl with evar_body = Evar_defined c } in
  evars_reset_evd (Evd.add sigma sp spdecl') evd


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

let unify_0 env sigma cv_pb m n =
  let trivial_unify pb substn m n =
    if (not(occur_meta m)) & is_fconv pb env sigma m n then substn
    else error_cannot_unify env sigma (m,n) in
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
	  with ex when precatchable_exception ex ->
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

let applyHead env sigma n c  = 
  let evd = create_evar_defs sigma in
  let rec apprec n c cty =
    if n = 0 then 
      (evars_of evd, c)
    else 
      match kind_of_term (whd_betadeltaiota env (evars_of evd) cty) with
        | Prod (_,c1,c2) ->
            let evar =
              Evarutil.new_isevar evd env
                (dummy_loc,Rawterm.InternalHole) c1 in
	    apprec (n-1) (mkApp(c,[|evar|])) (subst1 evar c2)
	| _ -> error "Apply_Head_Then"
  in 
  apprec n c (Typing.type_of env (evars_of evd) c)

let is_mimick_head f =
  match kind_of_term f with
      (Const _|Var _|Rel _|Construct _|Ind _) -> true
    | _ -> false
 
(* [w_merge env sigma b metas evars] merges common instances in metas
   or in evars, possibly generating new unification problems; if [b]
   is true, unification of types of metas is required *)

let w_merge env with_types metas evars (sigma,metamap) =
  let evd = create_evar_defs sigma in
  let mmap = ref metamap in
  let ty_metas = ref [] in
  let ty_evars = ref [] in
  let rec w_merge_rec metas evars =
    match (evars,metas) with
      | ([], []) -> ()

      | ((lhs,rhs)::t, metas) ->
      (match kind_of_term rhs with

	| Meta k -> w_merge_rec ((k,lhs)::metas) t

	| krhs ->
        (match kind_of_term lhs with

	  | Evar (evn,_ as ev) ->
    	      if is_defined_evar evd ev then
		let (metas',evars') =
                  unify_0 env (evars_of evd) CONV rhs lhs in
		w_merge_rec (metas'@metas) (evars'@t)
    	      else begin
		let rhs' = 
		  if occur_meta rhs then subst_meta metas rhs else rhs 
		in
		if occur_evar evn rhs' then
                  error "w_merge: recursive equation";
                match krhs with
		  | App (f,cl) when is_mimick_head f ->
		      (try 
                        w_Define evn rhs' evd; 
		        w_merge_rec metas t
		      with ex when precatchable_exception ex ->
                        mimick_evar f (Array.length cl) evn;
			w_merge_rec metas evars)
                  | _ ->
                      (* ensure tail recursion in non-mimickable case! *)
                      w_Define evn rhs' evd; 
		      w_merge_rec metas t
	      end

	  | _ -> anomaly "w_merge_rec"))

      | ([], (mv,n)::t) ->
    	  if meta_defined !mmap mv then
            let (metas',evars') =
              unify_0 env (evars_of evd) CONV (meta_fvalue !mmap mv).rebus n in
            w_merge_rec (metas'@t) evars'
    	  else
            begin
	      if with_types (* or occur_meta mvty *) then
	        (let mvty = meta_type !mmap mv in
		try 
                  let sigma = evars_of evd in
                  (* why not typing with the metamap ? *)
		  let nty = Typing.type_of env sigma (nf_meta !mmap n) in
		  let (mc,ec) = unify_0 env sigma CUMUL nty mvty in
                  ty_metas := mc @ !ty_metas;
                  ty_evars := ec @ !ty_evars
		with e when precatchable_exception e -> ());
              mmap := meta_assign mv n !mmap;
	      w_merge_rec t []
            end
  and mimick_evar hdc nargs sp =
    let ev = Evd.map (evars_of evd) sp in
    let sp_env = Global.env_of_context ev.evar_hyps in
    let (sigma', c) = applyHead sp_env (evars_of evd) nargs hdc in
    evars_reset_evd sigma' evd;
    let (mc,ec) =
      unify_0 sp_env (evars_of evd) CUMUL
        (Retyping.get_type_of sp_env (evars_of evd) c) ev.evar_concl in
    w_merge_rec mc ec;
    if sigma'== (evars_of evd)
    then w_Define sp c evd
    else w_Define sp (Evarutil.nf_evar (evars_of evd) c) evd in

  (* merge constraints *)
  w_merge_rec metas evars;
  (if with_types then
    (* merge constraints about types: if they fail, don't worry *)
    try w_merge_rec !ty_metas !ty_evars
(* TODO: should backtrack *)
    with e when precatchable_exception e -> ());
  (evars_of evd, !mmap)

(* [w_unify env evd M N]
   performs a unification of M and N, generating a bunch of
   unification constraints in the process.  These constraints
   are processed, one-by-one - they may either generate new
   bindings, or, if there is already a binding, new unifications,
   which themselves generate new constraints.  This continues
   until we get failure, or we run out of constraints.
   [clenv_typed_unify M N clenv] expects in addition that expected
   types of metavars are unifiable with the types of their instances    *)

let w_unify_core_0 env with_types cv_pb m n evd =
  let (mc,ec) = unify_0 env (fst evd) cv_pb m n in 
  w_merge env with_types mc ec evd

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
let w_unify_to_subterm env (op,cl) evd =
  let rec matchrec cl =
    let cl = strip_outer_cast cl in
    (try 
       if closed0 cl 
       then w_unify_0 env CONV op cl evd,cl
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

let w_unify_to_subterm_list env allow_K oplist t evd = 
  List.fold_right 
    (fun op (evd,l) ->
      if isMeta op then
	if allow_K then (evd,op::l)
	else error "Match_subterm"
      else if occur_meta op then
        let (evd',cl) =
          try 
	    (* This is up to delta for subterms w/o metas ... *)
	    w_unify_to_subterm env (strip_outer_cast op,t) evd
          with PretypeError (env,NoOccurrenceFound _) when allow_K -> (evd,op)
        in 
	(evd',cl::l)
      else if not allow_K & not (dependent op t) then
	(* This is not up to delta ... *)
	raise (PretypeError (env,NoOccurrenceFound op))
      else
	(evd,op::l))
    oplist 
    (evd,[])

let secondOrderAbstraction env allow_K typ (p, oplist) evd =
  let sigma = fst evd in
  let (evd',cllist) =
    w_unify_to_subterm_list env allow_K oplist typ evd in
  let typp = meta_type (snd evd') p in
  let pred = abstract_list_all env sigma typp typ cllist in
  w_unify_0 env CONV (mkMeta p) pred evd'

let w_unify2 env allow_K cv_pb ty1 ty2 evd =
  let c1, oplist1 = whd_stack ty1 in
  let c2, oplist2 = whd_stack ty2 in
  match kind_of_term c1, kind_of_term c2 with
    | Meta p1, _ ->
        (* Find the predicate *)
	let evd' =
          secondOrderAbstraction env allow_K ty2 (p1,oplist1) evd in 
        (* Resume first order unification *)
	w_unify_0 env cv_pb (nf_meta (snd evd') ty1) ty2 evd'
    | _, Meta p2 ->
        (* Find the predicate *)
	let evd' =
          secondOrderAbstraction env allow_K ty1 (p2, oplist2) evd in 
        (* Resume first order unification *)
	w_unify_0 env cv_pb ty1 (nf_meta (snd evd') ty2) evd'
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
let w_unify allow_K env cv_pb ty1 ty2 evd =
  let hd1,l1 = whd_stack ty1 in
  let hd2,l2 = whd_stack ty2 in
  match kind_of_term hd1, l1<>[], kind_of_term hd2, l2<>[] with
    (* Pattern case *)
    | (Meta _, true, Lambda _, _ | Lambda _, _, Meta _, true)
      when List.length l1 = List.length l2 ->
	(try 
	   w_typed_unify env cv_pb ty1 ty2 evd
	 with ex when precatchable_exception ex -> 
	   try 
	     w_unify2 env allow_K cv_pb ty1 ty2 evd
	   with PretypeError (env,NoOccurrenceFound c) as e -> raise e
	     | ex when precatchable_exception ex -> 
	     error "Cannot solve a second-order unification problem")

     (* Second order case *)
     | (Meta _, true, _, _ | _, _, Meta _, true) -> 
	(try 
	   w_unify2 env allow_K cv_pb ty1 ty2 evd
	with PretypeError (env,NoOccurrenceFound c) as e -> raise e
	  | ex when precatchable_exception ex -> 
          try 
	     w_typed_unify env cv_pb ty1 ty2 evd
          with ex when precatchable_exception ex -> 
             error "Cannot solve a second-order unification problem")

     (* General case: try first order *)
     | _ -> w_unify_0 env cv_pb ty1 ty2 evd

