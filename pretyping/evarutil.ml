(* $Id$ *)

open Util;;
open Pp;;
open Names;;
open Impuniv;;
open Generic;;
open Term;;
open Printer;;
open Termenv;;
open Evd;;
open Reduction;;


let rec filter_unique = function
    [] -> []
  | x::l ->
      if List.mem x l then filter_unique (filter (fun y -> x<>y) l)
      else x::filter_unique l
;;

let distinct_id_list = 
  let rec drec fresh = function
      [] -> List.rev fresh 
    | id::rest ->
 	let id' = next_ident_away_from id fresh in drec (id'::fresh) rest
  in drec []
;;

let filter_sign p sign x =
  sign_it
    (fun id ty (v,ids,sgn) ->
      let (disc,v') = p v (id,ty) in
      if disc then (v', id::ids, sgn) else (v', ids, add_sign (id,ty) sgn))
    sign
    (x,[],nil_sign)
;;


(*------------------------------------*
 * functional operations on evar sets *
 *------------------------------------*)

(* All ids of sign must be distincts! *)
let new_isevar_sign env sigma typ args k =
  let sign = context env in
  (if not (distinct (ids_of_sign sign))
  then error "new_isevar_sign: two vars have the same name");
  let newsp = new_isevar_path k in
  (Evd.add_noinfo sigma newsp sign typ, mkConst newsp args)
;;

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)
let dummy_sort = mkType dummy_univ;;

(* Declaring any type to be in the sort Type shouldn't be harmful since
   cumulativity now includes Prop and Set in Type. *)
let new_type_var sigma sign k =
  let args = (Array.of_list (List.map mkVar (ids_of_sign sign))) in
  let (sigma',c) = new_isevar_sign sigma sign dummy_sort args k in
  (sigma', make_type c (Type dummy_univ))
;;

let split_evar_to_arrow sigma c =
  let (sp,args) = destConst c in
  let k = kind_of_path sp in
  let evd = Evd.map sigma sp in
  let hyps= evd.hyps in
  let (sigma1,dom) = new_type_var sigma hyps k in
  let nvar = next_ident_away (id_of_string "x") (ids_of_sign hyps) in
  let nhyps = add_sign (nvar,dom) hyps in
  let (sigma2,rng) = new_type_var sigma1 nhyps k in
  let prod = Environ.prod_create (incast_type dom, 
				  subst_var nvar (body_of_type rng)) in
  let sigma3 = Evd.define sigma2 sp prod in
  let dsp = path_of_const (body_of_type dom) in
  let rsp = path_of_const (body_of_type rng) in
  (sigma3,
   mkCast (mkConst dsp args) dummy_sort,
   mkCast (mkConst rsp (cons_vect (mkRel 1) args)) dummy_sort)
;;

(* Redefines an evar with a smaller context (i.e. it may depend on less
 * variables) such that c becomes closed.
 * Example: in [x:?1; y:(list ?2)] <?3>x=y /\ x=(nil bool)
 * ?3 <-- ?1          no pb: env of ?3 is larger than ?1's
 * ?1 <-- (list ?2)   pb: ?2 may depend on x, but not ?1.
 * What we do is that ?2 is defined by a new evar ?4 whose context will be
 * a prefix of ?2's env, included in ?1's env.
 *)
let do_restrict_hyps sigma c =
  let (sp,argsv) = destConst c in
  let k = kind_of_path sp in
  let args = Array.to_list argsv in
  let evd = Evd.map sigma sp in
  let hyps= evd.hyps in
  let (_,(rsign,ncargs)) =
    List.fold_left (fun (sign,(rs,na)) a ->
      (tl_sign sign,
       if not(closed0 a) then (rs,na)
       else (add_sign (hd_sign sign) rs, a::na)))
      (hyps,(nil_sign,[])) args in
(*  let (_,(rsign,ncargs)) =
    List.fold_left (fun (sign,(rs,na)) a ->
      (tl_sign sign,
       if not(closed0 a) then (nil_sign,[])
       else (add_sign (hd_sign sign) rs, a::na)))
      (hyps,(nil_sign,[])) args in *)
  let nsign = rev_sign rsign in
  let nargs = (Array.of_list (List.map mkVar (ids_of_sign nsign))) in
  let (sigma',nc) = new_isevar_sign sigma nsign evd.concl nargs k in
  let sigma'' = Evd.define sigma' sp nc in
  (sigma'', mkConst (path_of_const nc) (Array.of_list (List.rev ncargs)))
;;



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
;;


(* say if the section path sp corresponds to an existential *)
let ise_in_dom isevars sp = Evd.in_dom !isevars sp;;

(* map the given section path to the evar_declaration *)
let ise_map isevars sp = Evd.map !isevars sp;;

(* define the existential of section path sp as the constr body *)
let ise_define isevars sp body = isevars := Evd.define !isevars sp body;;

(* Does k corresponds to an (un)defined existential ? *)
let ise_undefined isevars k =
  match k with
    DOPN(Const _,_) ->
      ise_in_dom isevars (path_of_const k) &
      not (defined_const !isevars k)
  | _ -> false
;;

let ise_defined isevars k =
  match k with
    DOPN(Const _,_) -> Termenv.defined_existential !isevars k
  | _ -> false
;;

let restrict_hyps isevars c =
  if ise_undefined isevars c & not (closed0 c)
  then
    (let (sigma,rc) = do_restrict_hyps !isevars c in
    isevars := sigma;
    rc)
  else c
;;


let error_occur_check sp rhs =
  let id = string_of_id (Names.basename sp) in
  let pt = prterm rhs in
  errorlabstrm "Trad.occur_check"
    [< 'sTR"Occur check failed: tried to define "; 'sTR id;
      'sTR" with term"; 'bRK(1,1); pt >]
;;

(* We need the environment here *)
let error_not_clean sp t =
  let c = Rel (List.hd (Listset.elements(free_rels t))) in
  let id = string_of_id (Names.basename sp) in
  let var = pTERM(c) in
  errorlabstrm "Trad.not_clean"
    [< 'sTR"Tried to define "; 'sTR id;
       'sTR" with a term using variable "; var; 'sPC;
       'sTR"which is not in its scope." >]
;;

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
    | DOPL(o,l) -> DOPL(o, List.map (subs k) l)
    | DLAM(n,a) -> DLAM(n, subs (k+1) a)
    | DLAMV(n,v) -> DLAMV(n, Array.map (subs (k+1)) v) in
  let body = subs 0 rhs in
  if not (closed0 body) then error_not_clean sp body;
  body
;;


(* [new_isevar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)
let new_isevar isevars env typ k =
  let (ENVIRON(sign,dbenv)) = env in
  let t =
    List.fold_left (fun b (na,d)-> mkLambda na (incast_type d) b) typ dbenv in
  let rec aux sign = function
      (0, t) -> (sign,t)
    | (n, (DOP2(Lambda,d,(DLAM(na,b))))) ->
	let na = if na = Anonymous then Name(id_of_string"_") else na in
       	let id = next_name_away na (ids_of_sign sign) in
       	aux (add_sign (id,(outcast_type d)) sign) (n-1, subst1 (VAR id) b)
    | (_, _) -> anomaly "Trad.new_isevar" in
  let (sign',typ') = aux sign (List.length dbenv, t) in
  let newargs =
    (List.rev(rel_list 0 (List.length dbenv)))
    @(List.map (fun id -> VAR id) (ids_of_sign sign)) in
  let (sigma',evar) =
    new_isevar_sign !isevars sign' typ' (Array.of_list newargs) k in
  isevars := sigma';
  (evar,typ')
;;


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
  let (sp,argsv) = destConst lhs in
  let _ = if occur_opern (Const sp) rhs then error_occur_check sp rhs in
  let args = List.map (function (VAR _ | Rel _) as t -> t | _ -> mkImplicit)
      (Array.to_list argsv) in 
  let evd = ise_map isevars sp in
  let hyps= evd.hyps in
  (* the substitution to invert *)
  let worklist = List.combine (ids_of_sign hyps) args in
  let body = real_clean isevars sp worklist rhs in
  ise_define isevars sp body;
  [sp]
;;


(* Solve pbs (?i x1..xn) = (?i y1..yn) which arises often in fixpoint
 * definitions. We try to unify the xi with the yi pairwise. The pairs
 * that don't unify are discarded (i.e. ?i is redefined so that it does not
 * depend on these args).
 *)
let solve_refl conv_algo isevars c1 c2 =
  let (sp,argsv1) = destConst c1
  and (_,argsv2) = destConst c2 in
  let evd = Evd.map !isevars sp in
  let hyps = evd.Evd.hyps in
  let (_,rsign) = it_vect2
      (fun (sgn,rsgn) a1 a2 ->
	if conv_algo a1 a2
 	then (tl_sign sgn, add_sign (hd_sign sgn) rsgn)
	else (tl_sign sgn, rsgn))
      (hyps,nil_sign) argsv1 argsv2 in
  let nsign = rev_sign rsign in
  let nargs = (Array.of_list (List.map mkVar (ids_of_sign nsign))) in
  let newsp = new_isevar_path CCI in
  isevars :=
    Evd.define (Evd.add_noinfo !isevars newsp nsign evd.Evd.concl)
      sp (mkConst newsp nargs);
  Some [sp]


(* Tries to solve problem t1 = t2.
 * Precondition: one of t1,t2 is an uninstanciated evar, possibly
 * applied to arguments.
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved.
 *)
(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let rec solve_simple_eqn conv_algo isevars ((pbty,t1,t2) as pb) =
  let t1 = nf_ise1 !isevars t1 in
  let t2 = nf_ise1 !isevars t2 in
  if eq_constr t1 t2 then Some []
  else match (ise_undefined isevars t1, ise_undefined isevars t2) with
    (true,true) ->
      if path_of_const t1 = path_of_const t2
      then solve_refl conv_algo isevars t1 t2
      else if Array.length(args_of_const t1) < Array.length(args_of_const t2)
      then Some (evar_define isevars t2 t1)
      else Some (evar_define isevars t1 t2)
  | (true,false) -> Some (evar_define isevars t1 t2)
  | (false,true) -> Some (evar_define isevars t2 t1)
  | _ -> None
;;

(*-------------------*)
(* Now several auxiliary functions for the conversion algorithms modulo
 * evars. used in trad and progmach
 *)


let has_undefined_isevars isevars c =
  let rec hasrec = function
    DOPN(Const sp,cl) as k ->
    if ise_in_dom isevars sp then 
       if defined_const !isevars k
       then hasrec (const_value !isevars k)
       else failwith "caught"
    else Array.iter hasrec cl

  | DOP1(_,c) -> hasrec c
  | DOP2(_,c1,c2) -> (hasrec c1; hasrec c2)
  | DOPL(_,l) -> List.iter hasrec l
  | DOPN(_,cl) -> Array.iter hasrec cl
  | DLAM(_,c) -> hasrec c
  | DLAMV(_,cl) -> Array.iter hasrec cl
  | (VAR _|Rel _|DOP0 _) -> ()
 in (try (hasrec c ; false) with Failure "caught" -> true)
    
;;

let head_is_exist isevars = 
 let rec hrec = function
    DOPN(Const _,_) as k -> ise_undefined isevars k
  | DOPN(AppL,cl) -> hrec (hd_vect cl)
  | DOP2(Cast,c,_) -> hrec c
  | _ -> false
 in hrec 
;;


let rec is_eliminator = function
    DOPN (AppL,_)          -> true
  | DOPN(MutCase _,_) -> true
  | DOP2 (Cast,c,_)        -> is_eliminator c
  | _ -> false
;;

let head_is_embedded_exist isevars c =
    (head_is_exist isevars c) & (is_eliminator c)
;;

let headconstant = 
 let rec hrec = function
    DOPN(Const sp,_)       -> sp
  | DOPN(MutCase _,_) as mc -> 
       let (_,_,c,_) = destCase mc in
       hrec c
  | DOPN(AppL,cl)          -> hrec (hd_vect cl)
  | DOP2(Cast,c,_)         -> hrec c
  | _                      -> failwith "headconstant"
 in hrec 
;;

let status_changed lsp (pbty,t1,t2) =
    try List.mem (headconstant t1) lsp or List.mem (headconstant t2) lsp
    with Failure _ ->
    try List.mem (headconstant t2) lsp
    with Failure _ -> false
;;



(* Operations on value/type constraints used in trad and progmach *)

type trad_constraint = bool * (constr option * constr option)
(* Basically, we have the following kind of constraints (in increasing
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



(* The empty constraint *)
let mt_tycon = (false,(None,None));;

(* The default constraints for types. *)
let def_vty_con = (true,(None,None));;

(* Constrain only the type *)
let mk_tycon ty = (false,(None,Some ty));;
let mk_tycon2 (is_ass,_) ty = (is_ass,(None,Some ty))


(* Propagation of constraints through application and abstraction *)

(* Given a type constraint on a term, returns the type constraint on its first
 * argument. If the input constraint is an evar instantiate it with the product
 * of 2 new evars.
 *)
let prod_dom_tycon_unif isevars = function
    None -> None
  | Some c ->
      (match whd_betadeltaiota !isevars c with
        DOP2(Prod,c1,_) -> Some c1
      |	t ->
	  if (ise_undefined isevars t) then
	    (let (sigma,dom,_) = split_evar_to_arrow !isevars t in
	    isevars := sigma;
	    Some dom)
	  else None)
;;

(* Given a constraint on a term, returns the constraint corresponding to its
 * first argument.
 *) 
let app_dom_tycon isevars (_,(_,tyc)) =
  (false,(None, prod_dom_tycon_unif isevars tyc))
;;

(* Given a constraint on a term, returns the constraint corresponding to this
 * term applied to arg.
 *)
let app_rng_tycon isevars arg = function
    (_,(_,None)) as vtcon -> vtcon
  | (_,(_,Some c)) ->
      (match whd_betadeltaiota !isevars c with
        DOP2(Prod,_,DLAM(_,b)) -> mk_tycon (subst1 arg b)
      | _ -> mt_tycon)
;;

(* Given a constraint on an abstraction, returns the constraint on the value
 * of the domain type. If we had no constraint, we still know it should be
 * a type.
 *)
let abs_dom_valcon isevars (_,(_,tyc)) =
  (true,(prod_dom_tycon_unif isevars tyc, None))
;;

(* Given a constraint on an abstraction, returns the constraint on the body *)
let abs_rng_tycon isevars = function
    (_,(_,None)) -> mt_tycon
  | (_,(_,Some c)) ->
      (match whd_betadeltaiota !isevars c with
      | DOP2(Prod,_,DLAM(_,b)) -> mk_tycon b
      | _ -> mt_tycon)
;;

(* $Id$ *)
