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
open Instantiate
open Reductionops
open Indrec
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

(**********************)
(* Creating new evars *)
(**********************)

let evar_env evd = Global.env_of_context evd.evar_hyps

(* Generator of existential names *)
let new_evar =
  let evar_ctr = ref 0 in
  fun () -> incr evar_ctr; existential_of_int !evar_ctr

let make_evar_instance env =
  fold_named_context
    (fun env (id, b, _) l -> (*if b=None then*) mkVar id :: l (*else l*))
    env ~init:[]

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
	       evar_body = Evar_empty } in
  (Evd.add sigma newev info, mkEvar (newev,Array.of_list instance))

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)
let new_Type () = mkType (new_univ ())

let new_Type_sort () = Type (new_univ ())

let judge_of_new_Type () = Typeops.judge_of_type (new_univ ())
(*
let new_Type () = mkType dummy_univ

let new_Type_sort () = Type dummy_univ

let judge_of_new_Type () = 
  { uj_val = mkSort (Type dummy_univ);
    uj_type = mkSort (Type dummy_univ) }
*)

(* This refreshes universes in types; works only for inferred types (i.e. for
   types of the form (x1:A1)...(xn:An)B with B a sort or an atom in
   head normal form) *)
let refresh_universes t =
  let modified = ref false in
  let rec refresh t = match kind_of_term t with
    | Sort (Type _) -> modified := true; new_Type ()
    | Prod (na,u,v) -> mkProd (na,u,refresh v)
    | _ -> t in
  let t' = refresh t in
  if !modified then t' else t

(* Declaring any type to be in the sort Type shouldn't be harmful since
   cumulativity now includes Prop and Set in Type. *)
let new_type_var env sigma =
  let instance = make_evar_instance env in
  new_isevar_sign env sigma (new_Type ()) instance

let split_evar_to_arrow sigma (ev,args) =
  let evd = Evd.map sigma ev in
  let evenv = evar_env evd in
  let (sigma1,dom) = new_type_var evenv sigma in
  let hyps = evd.evar_hyps in
  let nvar = next_ident_away (id_of_string "x") (ids_of_named_context hyps) in
  let newenv = push_named (nvar, None, dom) evenv in
  let (sigma2,rng) = new_type_var newenv sigma1 in
  let x = named_hd newenv dom Anonymous in
  let prod = mkProd (x, dom, subst_var nvar rng) in
  let sigma3 = Evd.define sigma2 ev prod in
  let evdom = fst (destEvar dom), args in
  let evrng =
    fst (destEvar rng), array_cons (mkRel 1) (Array.map (lift 1) args) in
  let prod' = mkProd (x, mkEvar evdom, mkEvar evrng) in
  (sigma3,prod', evdom, evrng)

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
  let env' = reset_with_named_context sign' env in
  let (sigma',nc) = new_isevar_sign env' sigma evd.evar_concl ncargs in
  let nc = refresh_universes nc in (* needed only if nc is an inferred type *)
  let sigma'' = Evd.define sigma' ev nc in
  (sigma'', nc)




(*------------------------------------*
 * operations on the evar constraints *
 *------------------------------------*)

type evar_constraint = conv_pb * constr * constr
type evar_defs =
    { mutable evars : Evd.evar_map;
      mutable conv_pbs : evar_constraint list;
      mutable history : (existential_key * (loc * Rawterm.hole_kind)) list }

let create_evar_defs evd = { evars=evd; conv_pbs=[]; history=[] }
let evars_of d = d.evars
let evars_reset_evd evd d = d.evars <- evd
let add_conv_pb d pb = d.conv_pbs <- pb::d.conv_pbs
let evar_source ev d =
  try List.assoc ev d.history
  with Failure _ -> (dummy_loc, Rawterm.InternalHole)

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
  let body = refresh_universes body in (* needed only if an inferred type *)
  isevars.evars <- Evd.define isevars.evars sp body

let is_defined_evar isevars (n,_) = Evd.is_defined isevars.evars n

(* Does k corresponds to an (un)defined existential ? *)
let ise_undefined isevars c = match kind_of_term c with
  | Evar ev -> not (is_defined_evar isevars ev)
  | _ -> false

let need_restriction isevars args = not (array_for_all closed0 args)
    

(* We try to instanciate the evar assuming the body won't depend
 * on arguments that are not Rels or Vars, or appearing several times.
 *)
(* Note: error_not_clean should not be an error: it simply means that the
 * conversion test that lead to the faulty call to [real_clean] should return
 * false. The problem is that we won't get the right error message.
 *)

let real_clean env isevars ev args rhs =
  let subst = List.map (fun (x,y) -> (y,mkVar x)) (filter_unique args) in
  let rec subs k t =
    match kind_of_term t with
      | Rel i ->
 	 if i<=k then t
 	 else (try List.assoc (mkRel (i-k)) subst with Not_found -> t)
      | Evar (ev,args) ->
	  let args' = Array.map (subs k) args in
	  if need_restriction isevars args' then
	    if Evd.is_defined isevars.evars ev then 
	      subs k (existential_value isevars.evars (ev,args'))
	    else begin
	      let (sigma,rc) = do_restrict_hyps isevars.evars ev args' in
	      isevars.evars <- sigma;
              isevars.history <- 
                (fst (destEvar rc),evar_source ev isevars)::isevars.history;
	      rc
	    end
	  else
	    mkEvar (ev,args')
      | Var _ -> (try List.assoc t subst with Not_found -> t)
      | _ -> map_constr_with_binders succ subs k t
  in
  let body = subs 0 rhs in
  if not (closed0 body)
  then error_not_clean env isevars.evars ev body (evar_source ev isevars);
  body

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
  in (subst, reset_with_named_context sign env)

let new_isevar isevars env src typ =
  let subst,env' = push_rel_context_to_named_context env in
  let typ' = substl subst typ in
  let instance = make_evar_instance_with_rel env in
  let (sigma',evar) = new_isevar_sign env' isevars.evars typ' instance in
  isevars.evars <- sigma';
  isevars.history <- (fst (destEvar evar),src)::isevars.history;
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

let evar_define env isevars (ev,argsv) rhs =
  if occur_evar ev rhs
  then error_occur_check env (evars_of isevars) ev rhs;
  let args = Array.to_list argsv in 
  let evd = ise_map isevars ev in
  (* the bindings to invert *)
  let worklist = make_subst (evar_env evd) args in
  let body = real_clean env isevars ev worklist rhs in
  ise_define isevars ev body;
  [ev]

(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

let has_undefined_isevars isevars t = 
  try let _ = local_strong (whd_ise isevars.evars) t in false
  with Uninstantiated_evar _ -> true

let head_is_evar isevars = 
  let rec hrec k = match kind_of_term k with
    | Evar (n,_)   -> not (Evd.is_defined isevars.evars n)
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
	       evar_body = Evar_empty } in
  isevars.evars <-
    Evd.define (Evd.add isevars.evars newev info) ev (mkEvar (newev,nargs));
  isevars.history <- (newev,evar_source ev isevars)::isevars.history;
  [ev]


(* Tries to solve problem t1 = t2.
 * Precondition: t1 is an uninstanciated evar
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved. *)

(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let solve_simple_eqn conv_algo env isevars (pbty,(n1,args1 as ev1),t2) =
  let t2 = nf_evar isevars.evars t2 in
  let lsp = match kind_of_term t2 with
    | Evar (n2,args2 as ev2)
        when not (Evd.is_defined isevars.evars n2) ->
	if n1 = n2 then
	  solve_refl conv_algo env isevars n1 args1 args2
	else
	  if Array.length args1 < Array.length args2 then 
	    evar_define env isevars ev2 (mkEvar ev1)
	  else 
	    evar_define env isevars ev1 t2
    | _ ->
	evar_define env isevars ev1 t2 in
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

(* Refining an evar to a product or a sort *)

let refine_evar_as_arrow isevars ev =
  let (sigma,prod,evdom,evrng) = split_evar_to_arrow isevars.evars ev in
  evars_reset_evd sigma isevars;
  let hst = evar_source (fst ev) isevars in
  isevars.history <- (fst evrng,hst)::(fst evdom, hst)::isevars.history;
  (prod,evdom,evrng)

let define_evar_as_arrow isevars ev =
  let (prod,_,_) = refine_evar_as_arrow isevars ev in
  prod

let define_evar_as_sort isevars (ev,args) =
  let s = new_Type () in
  let sigma' = Evd.define isevars.evars ev s in
  evars_reset_evd sigma' isevars;
  destSort s


(* Propagation of constraints through application and abstraction:
   Given a type constraint on a functional term, returns the type
   constraint on its domain and codomain. If the input constraint is
   an evar instantiate it with the product of 2 new evars. *)

let split_tycon loc env isevars = function
  | None -> Anonymous,None,None
  | Some c ->
      let sigma = evars_of isevars in
      let t = whd_betadeltaiota env sigma c in
      match kind_of_term t with
        | Prod (na,dom,rng) -> na, Some dom, Some rng
	| Evar (n,_ as ev) when not (Evd.is_defined isevars.evars n) ->
	    let (_,evdom,evrng) = refine_evar_as_arrow isevars ev in
	    Anonymous, Some (mkEvar evdom), Some (mkEvar evrng)
	| _ -> error_not_product_loc loc env sigma c

let valcon_of_tycon x = x

let lift_tycon = option_app (lift 1)
