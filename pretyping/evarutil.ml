(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Univ
open Term
open Sign
open Environ
open Evd
open Instantiate
open Reduction
open Indrec
open Pretype_errors


let rec filter_unique = function
  | [] -> []
  | x::l ->
      if List.mem x l then filter_unique (List.filter (fun y -> x<>y) l)
      else x::filter_unique l

(*
let distinct_id_list = 
  let rec drec fresh = function
      [] -> List.rev fresh 
    | id::rest ->
 	let id' = next_ident_away_from id fresh in drec (id'::fresh) rest
  in drec []
*)

(*
let filter_sign p sign x =
  sign_it
    (fun id ty (v,ids,sgn) ->
      let (disc,v') = p v (id,ty) in
      if disc then (v', id::ids, sgn) else (v', ids, add_sign (id,ty) sgn))
    sign
    (x,[],nil_sign)
*)

let evar_env evd = Global.env_of_context evd.evar_hyps

(* Generator of existential names *)
let new_evar =
  let evar_ctr = ref 0 in
  fun () -> incr evar_ctr; !evar_ctr

let make_evar_instance env =
  fold_named_context
    (fun env (id, b, _) l -> (*if b=None then*) mkVar id :: l (*else l*))
    env []

(* create an untyped existential variable *)
let new_evar_in_sign env =
  let ev = new_evar () in
  mkEvar (ev, Array.of_list (make_evar_instance env))

(*------------------------------------*
 * functional operations on evar sets *
 *------------------------------------*)

(* All ids of sign must be distincts! *)
let new_isevar_sign env sigma typ instance =
  let sign = named_context env in
  if not (list_distinct (ids_of_named_context sign)) then 
    error "new_isevar_sign: two vars have the same name";
  let newev = new_evar() in
  let info = { evar_concl = typ; evar_hyps = sign; 
	       evar_body = Evar_empty; evar_info = None } in
  (Evd.add sigma newev info, mkEvar (newev,Array.of_list instance))

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)
let dummy_sort = mkType dummy_univ

(* Declaring any type to be in the sort Type shouldn't be harmful since
   cumulativity now includes Prop and Set in Type. *)
let new_type_var env sigma =
  let instance = make_evar_instance env in
  let (sigma',c) = new_isevar_sign env sigma dummy_sort instance in
  (sigma', c)

let split_evar_to_arrow sigma c =
  let (ev,args) = destEvar c in
  let evd = Evd.map sigma ev in
  let evenv = evar_env evd in
  let (sigma1,dom) = new_type_var evenv sigma in
  let hyps = evd.evar_hyps in
  let nvar = next_ident_away (id_of_string "x") (ids_of_named_context hyps) in
  let newenv = push_named_assum (nvar, dom) evenv in
  let (sigma2,rng) = new_type_var newenv sigma1 in
  let prod = mkProd (named_hd newenv dom Anonymous, dom, subst_var nvar rng) in
  let sigma3 = Evd.define sigma2 ev prod in
  let dsp = num_of_evar dom in
  let rsp = num_of_evar rng in
  (sigma3,
   mkEvar (dsp,args),
   mkEvar (rsp, array_cons (mkRel 1) (Array.map (lift 1) args)))


(* Redefines an evar with a smaller context (i.e. it may depend on less
 * variables) such that c becomes closed.
 * Example: in [x:?1; y:(list ?2)] <?3>x=y /\ x=(nil bool)
 * ?3 <-- ?1          no pb: env of ?3 is larger than ?1's
 * ?1 <-- (list ?2)   pb: ?2 may depend on x, but not ?1.
 * What we do is that ?2 is defined by a new evar ?4 whose context will be
 * a prefix of ?2's env, included in ?1's env. *)

let do_restrict_hyps sigma ev args =
  let args = Array.to_list args in
  let evd = Evd.map sigma ev in
  let env = evar_env evd in
  let hyps = evd.evar_hyps in
  let (_,(rsign,ncargs)) =
    List.fold_left 
      (fun (sign,(rs,na)) a ->
	 (List.tl sign,
	  if not(closed0 a) then 
	    (rs,na)
	  else 
	    (add_named_decl (List.hd sign) rs, a::na)))
      (hyps,([],[])) args 
  in
  let sign' = List.rev rsign in
  let env' = change_hyps (fun _ -> sign') env in
  let instance = make_evar_instance env' in
  let (sigma',nc) = new_isevar_sign env' sigma evd.evar_concl instance in
  let sigma'' = Evd.define sigma' ev nc in
  (sigma'', nc)




(*------------------------------------*
 * operations on the evar constraints *
 *------------------------------------*)

type evar_constraint = conv_pb * constr * constr
type 'a evar_defs =
    { mutable evars : 'a Evd.evar_map;
      mutable conv_pbs : evar_constraint list }

let create_evar_defs evd = { evars=evd; conv_pbs=[] }
let evars_of d = d.evars
let evars_reset_evd evd d = d.evars <- evd
let add_conv_pb d pb = d.conv_pbs <- pb::d.conv_pbs

(* ise_try [f1;...;fn] tries fi() for i=1..n, restoring the evar constraints
 * when fi returns false or an exception. Returns true if one of the fi
 * returns true, and false if every fi return false (in the latter case,
 * the evar constraints are restored).
 *)
let ise_try isevars l =
  let u = isevars.evars in
  let rec test = function
      [] -> isevars.evars <- u; false
    | f::l ->
 	  (try f() with reraise -> isevars.evars <- u; raise reraise)
       or (isevars.evars <- u; test l)
  in test l



(* say if the section path sp corresponds to an existential *)
let ise_in_dom isevars sp = Evd.in_dom isevars.evars sp

(* map the given section path to the enamed_declaration *)
let ise_map isevars sp = Evd.map isevars.evars sp

(* define the existential of section path sp as the constr body *)
let ise_define isevars sp body =
  isevars.evars <- Evd.define isevars.evars sp body

(* Does k corresponds to an (un)defined existential ? *)
let ise_undefined isevars c = match kind_of_term c with
  | IsEvar (n,_) -> not (Evd.is_defined isevars.evars n)
  | _ -> false

let ise_defined isevars c = match kind_of_term c with
  | IsEvar (n,_) -> Evd.is_defined isevars.evars n
  | _ -> false

let need_restriction isevars args = not (array_for_all closed0 args)
    

(* We try to instanciate the evar assuming the body won't depend
 * on arguments that are not Rels or Vars, or appearing several times.
 *)
(* Note: error_not_clean should not be an error: it simply means that the
 * conversion test that lead to the faulty call to [real_clean] should return
 * false. The problem is that we won't get the right error message.
 *)

let real_clean isevars sp args rhs =
  let subst = List.map (fun (x,y) -> (y,mkVar x)) (filter_unique args) in
  let rec subs k t =
    match kind_of_term t with
      | IsRel i ->
 	 if i<=k then t
 	 else (try List.assoc (mkRel (i-k)) subst with Not_found -> t)
      | IsEvar (ev,args) ->
	  let args' = Array.map (subs k) args in
	  if need_restriction isevars args' then
	    if Evd.is_defined isevars.evars ev then 
	      subs k (existential_value isevars.evars (ev,args'))
	    else begin
	      let (sigma,rc) = do_restrict_hyps isevars.evars ev args' in
	      isevars.evars <- sigma;

	      rc
	    end
	  else
	    mkEvar (ev,args')
      | IsVar _ -> (try List.assoc t subst with Not_found -> t)
      | _ -> map_constr_with_binders succ subs k t
  in
  let body = subs 0 rhs in
  if not (closed0 body) then error_not_clean empty_env sp body;
  body

let make_evar_instance_with_rel env =
  let n = rel_context_length (rel_context env) in
  let vars = 
    fold_named_context
      (fun env (id,b,_) l -> (* if b=None then *) mkVar id :: l (*else l*))
      env [] in
  snd (fold_rel_context
    (fun env (_,b,_) (i,l) -> (i-1, (*if b=None then *) mkRel i :: l (*else l*)))
    env (n,vars))

let make_subst env args =
  snd (fold_named_context
    (fun env (id,b,c) (args,l as g) ->
       match b, args with
	 | (* None *) _ , a::rest -> (rest, (id,a)::l)
(*	 | Some _, _ -> g*)
	 | _ -> anomaly "Instance does not match its signature")
    env (List.rev args,[]))

(* [new_isevar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)

let new_isevar isevars env typ k =
  let subst,env' = push_rel_context_to_named_context env in
  let typ' = substl subst typ in
  let instance = make_evar_instance_with_rel env in
  let (sigma',evar) = new_isevar_sign env' isevars.evars typ' instance in
  isevars.evars <- sigma';
  evar

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

let keep_rels_and_vars c = match kind_of_term c with
  | IsVar _ | IsRel _ -> c
  | _ -> mkImplicit   (* Mettre mkMeta ?? *)

let evar_define isevars (ev,argsv) rhs =
  if occur_evar ev rhs then error_occur_check empty_env ev rhs;
  let args = List.map keep_rels_and_vars (Array.to_list argsv) in 
  let evd = ise_map isevars ev in
  (* the substitution to invert *)
  let worklist = make_subst (evar_env evd) args in
  let body = real_clean isevars ev worklist rhs in
  ise_define isevars ev body;
  [ev]

(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

let has_undefined_isevars isevars t = 
  try let _ = whd_ise isevars.evars t in false
  with Uninstantiated_evar _ -> true

let head_is_evar isevars = 
  let rec hrec k = match kind_of_term k with
    | IsEvar (n,_)   -> not (Evd.is_defined isevars.evars n)
    | IsApp (f,_) -> hrec f
    | IsCast (c,_) -> hrec c
    | _ -> false
  in 
  hrec 

let rec is_eliminator c = match kind_of_term c with
  | IsApp _    -> true
  | IsMutCase _ -> true
  | IsCast (c,_) -> is_eliminator c
  | _ -> false

let head_is_embedded_evar isevars c =
  (head_is_evar isevars c) & (is_eliminator c)

let head_evar = 
  let rec hrec c = match kind_of_term c with
    | IsEvar (ev,_)       -> ev
    | IsMutCase (_,_,c,_) -> hrec c
    | IsApp (c,_)        -> hrec c
    | IsCast (c,_)        -> hrec c
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
 * Tradevar.evar_define
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

let get_changed_pb isevars lev =
  let (pbs,pbs1) = 
    List.fold_left
      (fun (pbs,pbs1) pb ->
    	 if status_changed lev pb then 
	   (pb::pbs,pbs1)
         else 
	   (pbs,pb::pbs1))
      ([],[])
      isevars.conv_pbs
  in
  isevars.conv_pbs <- pbs1;
  pbs

(* Solve pbs (?i x1..xn) = (?i y1..yn) which arises often in fixpoint
 * definitions. We try to unify the xi with the yi pairwise. The pairs
 * that don't unify are discarded (i.e. ?i is redefined so that it does not
 * depend on these args). *)

let solve_refl conv_algo env isevars ev argsv1 argsv2 =
  if argsv1 = argsv2 then [] else
  let evd = Evd.map isevars.evars ev in
  let env = evar_env evd in
  let hyps = evd.evar_hyps in
  let (_,rsign) = 
    array_fold_left2
      (fun (sgn,rsgn) a1 a2 ->
	 if conv_algo env isevars CONV a1 a2 then 
	   (List.tl sgn, add_named_decl (List.hd sgn) rsgn)
	 else 
	   (List.tl  sgn, rsgn))
      (hyps,[]) argsv1 argsv2 
  in
  let nsign = List.rev rsign in
  let nargs = (Array.of_list (List.map mkVar (ids_of_named_context nsign))) in
  let newev = new_evar () in
  let info = { evar_concl = evd.evar_concl; evar_hyps = nsign;
	       evar_body = Evar_empty; evar_info = None } in
  isevars.evars <-
    Evd.define (Evd.add isevars.evars newev info) ev (mkEvar (newev,nargs));
  [ev]


(* Tries to solve problem t1 = t2.
 * Precondition: t1 is an uninstanciated evar
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved. *)

(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let solve_simple_eqn conv_algo env isevars (pbty,(n1,args1 as ev1),t2) =
  let t2 = nf_ise1 isevars.evars t2 in
  let lsp = match kind_of_term t2 with
    | IsEvar (n2,args2 as ev2)
        when not (Evd.is_defined isevars.evars n2) ->
	if n1 = n2 then
	  solve_refl conv_algo env isevars n1 args1 args2
	else
	  if Array.length args1 < Array.length args2 then 
	    evar_define isevars ev2 (mkEvar ev1)
	  else 
	    evar_define isevars ev1 t2
    | _ ->
	evar_define isevars ev1 t2 in
  let pbs = get_changed_pb isevars lsp in
  List.for_all (fun (pbty,t1,t2) -> conv_algo env isevars pbty t1 t2) pbs

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

(* Propagation of constraints through application and abstraction:
   Given a type constraint on a functional term, returns the type
   constraint on its domain and codomain. If the input constraint is
   an evar instantiate it with the product of 2 new evars. *)

let split_tycon loc env isevars = function
  | None -> None,None
  | Some c ->
      let t = whd_betadeltaiota env isevars.evars c in
      match kind_of_term t with
        | IsProd (na,dom,rng) -> Some dom, Some rng
	| _ ->
	    if ise_undefined isevars t then
	      let (sigma,dom,rng) = split_evar_to_arrow isevars.evars t in
	      isevars.evars <- sigma;
	      Some dom, Some rng
	    else
	      error_not_product_loc loc env c

let valcon_of_tycon x = x

