
(* $Id$ *)

open Util
open Pp
open Names
open Univ
(*i open Generic i*)
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

let distinct_id_list = 
  let rec drec fresh = function
      [] -> List.rev fresh 
    | id::rest ->
 	let id' = next_ident_away_from id fresh in drec (id'::fresh) rest
  in drec []


(*
let filter_sign p sign x =
  sign_it
    (fun id ty (v,ids,sgn) ->
      let (disc,v') = p v (id,ty) in
      if disc then (v', id::ids, sgn) else (v', ids, add_sign (id,ty) sgn))
    sign
    (x,[],nil_sign)
*)

(*------------------------------------*
 * functional operations on evar sets *
 *------------------------------------*)

(* All ids of sign must be distincts! *)
let new_isevar_sign env sigma typ instance =
  let sign = var_context env in
  if not (list_distinct (ids_of_var_context sign)) then 
    error "new_isevar_sign: two vars have the same name";
  let newev = Evd.new_evar() in
  let info = { evar_concl = typ; evar_env = env; 
	       evar_body = Evar_empty; evar_info = None } in
  (Evd.add sigma newev info, mkEvar (newev,Array.of_list instance))

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)
let dummy_sort = mkType dummy_univ

let make_instance env =
  fold_var_context
    (fun env (id, b, _) l -> if b=None then mkVar id :: l else l)
    env []

(* Declaring any type to be in the sort Type shouldn't be harmful since
   cumulativity now includes Prop and Set in Type. *)
let new_type_var env sigma =
  let instance = make_instance env in
  let (sigma',c) = new_isevar_sign env sigma dummy_sort instance in
  (sigma', c)

let split_evar_to_arrow sigma c =
  let (ev,args) = destEvar c in
  let evd = Evd.map sigma ev in
  let evenv = evd.evar_env in
  let (sigma1,dom) = new_type_var evenv sigma in
  let hyps = var_context evenv in
  let nvar = next_ident_away (id_of_string "x") (ids_of_var_context hyps) in
  let newenv = push_var_decl (nvar,make_typed dom (Type dummy_univ)) evenv in
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

let do_restrict_hyps sigma c =
  let (ev,args) = destEvar c in
  let args = Array.to_list args in
  let evd = Evd.map sigma ev in
  let env = evd.evar_env in
  let hyps = var_context env in
  let (_,(rsign,ncargs)) =
    List.fold_left 
      (fun (sign,(rs,na)) a ->
	 (List.tl sign,
	  if not(closed0 a) then 
	    (rs,na)
	  else 
	    (add_var (List.hd sign) rs, a::na)))
      (hyps,([],[])) args 
  in
  let sign' = List.rev rsign in
  let env' = change_hyps (fun _ -> sign') env in
  let instance = make_instance env' in
  let (sigma',nc) = new_isevar_sign env' sigma evd.evar_concl instance in
  let sigma'' = Evd.define sigma' ev nc in
  (sigma'', nc)




(*------------------------------------*
 * operations on the evar constraints *
 *------------------------------------*)

type 'a evar_defs = 'a Evd.evar_map ref

(* ise_try [f1;...;fn] tries fi() for i=1..n, restoring the evar constraints
 * when fi returns false or an exception. Returns true if one of the fi
 * returns true, and false if every fi return false (in the latter case,
 * the evar constraints are restored).
 *)
let ise_try isevars l =
  let u = !isevars in
  let rec test = function
      [] -> isevars := u; false
    | f::l ->
 	  (try f() with reraise -> isevars := u; raise reraise)
       or (isevars := u; test l)
  in test l



(* say if the section path sp corresponds to an existential *)
let ise_in_dom isevars sp = Evd.in_dom !isevars sp

(* map the given section path to the evar_declaration *)
let ise_map isevars sp = Evd.map !isevars sp

(* define the existential of section path sp as the constr body *)
let ise_define isevars sp body = isevars := Evd.define !isevars sp body

(* Does k corresponds to an (un)defined existential ? *)
let ise_undefined isevars = function
  | DOPN(Evar n,_) -> not (Evd.is_defined !isevars n)
  | _ -> false

let ise_defined isevars = function
  | DOPN(Evar n,_) -> Evd.is_defined !isevars n
  | _ -> false

let restrict_hyps isevars c =
  if ise_undefined isevars c & not (closed0 c) then begin
    let (sigma,rc) = do_restrict_hyps !isevars c in
    isevars := sigma;
    rc
  end else 
    c

let has_ise sigma t = 
  try let _ = whd_ise sigma t in false
  with Uninstantiated_evar _ -> true

(* We try to instanciate the evar assuming the body won't depend
 * on arguments that are not Rels or VARs, or appearing several times.
 *)
(* Note: error_not_clean should not be an error: it simply means that the
 * conversion test that lead to the faulty call to [real_clean] should return
 * false. The problem is that we won't get the right error message.
 *)
let real_clean isevars sp args rhs =
  let subst = List.map (fun (x,y) -> (y,VAR x)) (filter_unique args) in
  let rec subs k t =
    match t with
      Rel i ->
 	if i<=k then t
 	else (try List.assoc (Rel (i-k)) subst with Not_found -> t)
    | VAR _ -> (try List.assoc t subst with Not_found -> t)
    | DOP0 _ -> t
    | DOP1(o,a) -> DOP1(o, subs k a)
    | DOP2(o,a,b) -> DOP2(o, subs k a, subs k b)
    | DOPN(o,v) -> restrict_hyps isevars (DOPN(o, Array.map (subs k) v))
    | DLAM(n,a) -> DLAM(n, subs (k+1) a)
    | DLAMV(n,v) -> DLAMV(n, Array.map (subs (k+1)) v)
    | CLam (n,t,c)   -> CLam (n, typed_app (subs k) t, subs (k+1) c)  
    | CPrd (n,t,c)   -> CPrd (n, typed_app (subs k) t, subs (k+1) c)
    | CLet (n,b,t,c) -> CLet (n, subs k b, typed_app (subs k) t, subs (k+1) c)
  in
  let body = subs 0 rhs in
  (* if not (closed0 body) then error_not_clean CCI empty_env sp body; *)
  body

let make_instance_with_rel env =
  let n = rel_context_length (rel_context env) in
  let vars = 
    fold_var_context
      (fun env (id,b,_) l -> if b=None then mkVar id :: l else l)
      env [] in
  snd (fold_rel_context
    (fun env (_,b,_) (i,l) -> (i-1, if b=None then mkRel i :: l else l))
    env (n+1,vars))

let make_subst env args =
  snd (fold_var_context
    (fun env (id,b,c) (args,l as g) ->
       match b, args with
	 | None, a::rest -> (rest, (id,a)::l)
	 | Some _, _ -> g
	 | _ -> anomaly "Instance does not match its signature")
    env (List.rev args,[]))

(* [new_isevar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)

let new_isevar isevars env typ k =
  let subst,env' = push_rels_to_vars env in
  let typ' = substl subst typ in
  let instance = make_instance_with_rel env in
  let (sigma',evar) = new_isevar_sign env' !isevars typ' instance in
  isevars := sigma';
  evar

(* [evar_define] solves the problem lhs = rhs when lhs is an uninstantiated
 * evar, i.e. tries to find the body ?sp for lhs=DOPN(Const sp,args)
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
let evar_define isevars lhs rhs =
  let (ev,argsv) = destEvar lhs in
  if occur_evar ev rhs then error_occur_check CCI empty_env ev rhs;
  let args = List.map (function (VAR _ | Rel _) as t -> t | _ -> mkImplicit)
      (Array.to_list argsv) in 
  let evd = ise_map isevars ev in
  (* the substitution to invert *)
  let worklist = make_subst evd.evar_env args in
  let body = real_clean isevars ev worklist rhs in
  ise_define isevars ev body;
  [ev]



(* Solve pbs (?i x1..xn) = (?i y1..yn) which arises often in fixpoint
 * definitions. We try to unify the xi with the yi pairwise. The pairs
 * that don't unify are discarded (i.e. ?i is redefined so that it does not
 * depend on these args). *)

let solve_refl conv_algo isevars c1 c2 =
  let (ev,argsv1) = destEvar c1
  and (_,argsv2) = destEvar c2 in
  let evd = Evd.map !isevars ev in
  let env = evd.evar_env in
  let hyps = var_context env in
  let (_,rsign) = 
    array_fold_left2
      (fun (sgn,rsgn) a1 a2 ->
	 if conv_algo a1 a2 then 
	   (List.tl sgn, add_var (List.hd sgn) rsgn)
	 else 
	   (List.tl  sgn, rsgn))
      (hyps,[]) argsv1 argsv2 
  in
  let nsign = List.rev rsign in
  let nenv = change_hyps (fun _ -> nsign) env in
  let nargs = (Array.of_list (List.map mkVar (ids_of_var_context nsign))) in
  let newev = Evd.new_evar () in
  let info = { evar_concl = evd.evar_concl; evar_env = nenv;
	       evar_body = Evar_empty; evar_info = None } in
  isevars :=
    Evd.define (Evd.add !isevars newev info) ev (mkEvar (newev,nargs));
  Some [ev]


(* Tries to solve problem t1 = t2.
 * Precondition: one of t1,t2 is an uninstanciated evar, possibly
 * applied to arguments.
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved. *)

(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let rec solve_simple_eqn conv_algo isevars ((pbty,t1,t2) as pb) =
  let t1 = nf_ise1 !isevars t1 in
  let t2 = nf_ise1 !isevars t2 in
  if eq_constr t1 t2 then 
    Some []
  else 
    match (ise_undefined isevars t1, ise_undefined isevars t2) with
      | (true,true) ->
	  if num_of_evar t1 = num_of_evar t2 then 
	    solve_refl conv_algo isevars t1 t2
	  else if Array.length(snd (destEvar t1)) < 
	          Array.length(snd (destEvar t2)) then 
	    Some (evar_define isevars t2 t1)
	  else 
	    Some (evar_define isevars t1 t2)
      | (true,false) -> Some (evar_define isevars t1 t2)
      | (false,true) -> Some (evar_define isevars t2 t1)
      | _ -> None

(*-------------------*)
(* Now several auxiliary functions for the conversion algorithms modulo
 * evars. used in trad and progmach
 *)


let has_undefined_isevars isevars c =
  let rec hasrec k = match splay_constr k with
    | OpEvar ev, cl when ise_in_dom isevars ev ->
	if ise_defined isevars k then 
	  hasrec (existential_value !isevars (ev,cl))
	else
	  failwith "caught"
    | _, cl -> Array.iter hasrec cl
  in 
  (try (hasrec c ; false) with Failure "caught" -> true)

let head_is_exist isevars = 
  let rec hrec k = match kind_of_term k with
    | IsEvar _     -> ise_undefined isevars k
    | IsAppL (f,l) -> hrec f
    | IsCast (c,_) -> hrec c
    | _ -> false
  in 
  hrec 

let rec is_eliminator = function
  | DOPN (AppL,_)      -> true
  | DOPN (MutCase _,_) -> true
  | DOP2 (Cast,c,_)    -> is_eliminator c
  | _ -> false

let head_is_embedded_exist isevars c =
  (head_is_exist isevars c) & (is_eliminator c)

let head_evar = 
  let rec hrec = function
    | DOPN(Evar ev,_)       -> ev
    | DOPN(MutCase _,_) as mc -> 
	let (_,_,c,_) = destCase mc in hrec c
    | DOPN(AppL,cl)          -> hrec (array_hd cl)
    | DOP2(Cast,c,_)         -> hrec c
    | _                      -> failwith "headconstant"
  in 
  hrec 
    
let status_changed lev (pbty,t1,t2) =
  try 
    List.mem (head_evar t1) lev or List.mem (head_evar t2) lev
  with Failure _ ->
    try List.mem (head_evar t2) lev with Failure _ -> false

(* Operations on value/type constraints used in trad and progmach *)

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
      let t = whd_betadeltaiota env !isevars c in
      match kind_of_term t with
        | IsProd (na,dom,rng) -> Some dom, Some rng
	| _ ->
	    if ise_undefined isevars t then
	      let (sigma,dom,rng) = split_evar_to_arrow !isevars t in
	      isevars := sigma;
	      Some dom, Some rng
	    else
	      Stdpp.raise_with_loc loc
		(Type_errors.TypeError (CCI,env,Type_errors.NotProduct c))

let valcon_of_tycon x = x

