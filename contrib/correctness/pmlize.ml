(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term
open Termast
open Pattern
open Matching

open Pmisc
open Ptype
open Past
open Putil
open Prename
open Penv
open Peffect
open Ptyping
open Pmonad


let has_proof_part ren env c =
  let sign = Pcicenv.trad_sign_of ren env in
  let ty = Typing.type_of (Global.env_of_context sign) Evd.empty c in
  Hipattern.is_matching_sigma (Reductionops.nf_betaiota ty)

(* main part: translation of imperative programs into functional ones.
 * 
 * [env] is the environment
 * [ren] is the current renamings of variables
 * [t] is the imperative program to translate, annotated with type+effects
 *
 * we return the translated program in type cc_term
 *)

let rec trad ren t =
  let env = t.info.env in
  trad_desc ren env t.info.kappa t.desc

and trad_desc ren env ct d =
  let (_,tt),eft,pt,qt = ct in
  match d with

  | Expression c ->
      let ids = get_reads eft in
      let al = current_vars ren ids in
      let c' = subst_in_constr al c in
      if has_proof_part ren env c' then
	CC_expr c'
      else
      	let ty = trad_ml_type_v ren env tt in
      	make_tuple [ CC_expr c',ty ] qt ren env (current_date ren)
      
  | Variable id ->
      if is_mutable_in_env env id then
	invalid_arg "Mlise.trad_desc"
      else if is_local env id then
	CC_var id
      else
	CC_expr (constant (string_of_id id))

  | Acc _ ->
      failwith "Mlise.trad: pure terms are supposed to be expressions"

  | TabAcc (check, x, e1) ->
      let _,ty_elem,_ = array_info ren env x in
      let te1 = trad ren e1 in
      let (_,ef1,p1,q1) = e1.info.kappa in
      let w = get_writes ef1 in
      let ren' = next ren w in
      let id = id_of_string "index" in
      let access = 
	make_raw_access ren' env (x,current_var ren' x) (mkVar id) 
      in
      let t,ty = result_tuple ren' (current_date ren) env
		   (CC_expr access, ty_elem) (eft,qt) in
      let t =
	if check then 
	  let h = make_pre_access ren env x (mkVar id) in 
	  let_in_pre ty (anonymous_pre true h) t
	else
	  t 
      in
      make_let_in ren env te1 p1
	(current_vars ren' w,q1) (id,constant "Z") (t,ty)

  | Aff (x, e1) ->
      let tx = trad_type_in_env ren env x in
      let te1 = trad ren e1 in
      let (_,ef1,p1,q1) = e1.info.kappa in
      let w1 = get_writes ef1 in
      let ren' = next ren (x::w1) in
      let t_ty = result_tuple ren' (current_date ren) env
		   (CC_expr (constant "tt"), constant "unit") (eft,qt) 
      in
      make_let_in ren env te1 p1
	(current_vars ren' w1,q1) (current_var ren' x,tx) t_ty

  | TabAff (check, x, e1, e2) ->
      let _,ty_elem,ty_array = array_info ren env x in
      let te1 = trad ren e1 in
      let (_,ef1,p1,q1) = e1.info.kappa in
      let w1 = get_writes ef1 in
      let ren' = next ren w1 in
      let te2 = trad ren' e2 in
      let (_,ef2,p2,q2) = e2.info.kappa in
      let w2 = get_writes ef2 in
      let ren'' = next ren' w2 in
      let id1 = id_of_string "index" in
      let id2 = id_of_string "v" in
      let ren''' = next ren'' [x] in
      let t,ty = result_tuple ren''' (current_date ren) env
		   (CC_expr (constant "tt"), constant "unit") (eft,qt) in
      let store = make_raw_store ren'' env (x,current_var ren'' x) (mkVar id1)
		   (mkVar id2) in
      let t = make_let_in ren'' env (CC_expr store) [] ([],None) 
		(current_var ren''' x,ty_array) (t,ty) in
      let t = make_let_in ren' env te2 p2
     	(current_vars ren'' w2,q2) (id2,ty_elem) (t,ty) in
      let t = 
	if check then
	  let h = make_pre_access ren' env x (mkVar id1) in
	  let_in_pre ty (anonymous_pre true h) t
	else
	  t 
      in
      make_let_in ren env te1 p1
	(current_vars ren' w1,q1) (id1,constant "Z") (t,ty)

  | Seq bl ->
      let before = current_date ren in
      let finish ren = function
	  Some (id,ty) -> 
	    result_tuple ren before env (CC_var id, ty) (eft,qt)
	| None ->
	    failwith "a block should contain at least one statement"
      in
      let bl = trad_block ren env bl in
      make_block ren env finish bl

  | If (b, e1, e2) ->
      let tb = trad ren b in
      let _,efb,_,_ = b.info.kappa in
      let ren' = next ren (get_writes efb) in
      let te1 = trad ren' e1 in
      let te2 = trad ren' e2 in
      make_if ren env (tb,b.info.kappa) ren' (te1,e1.info.kappa) 
	(te2,e2.info.kappa) ct

  (* Translation of the while. *)

  | While (b, inv, var, bl) ->
      let ren' = next ren (get_writes eft) in
      let tb = trad ren' b in
      let tbl = trad_block ren' env bl in
      let var' = typed_var ren env var in
      make_while ren env var' (tb,b.info.kappa) tbl (inv,ct)

  | Lam (bl, e) ->
      let bl' = trad_binders ren env bl in
      let env' = traverse_binders env bl in
      let ren' = initial_renaming env' in
      let te = trans ren' e in
      CC_lam (bl', te)

  | SApp ([Variable id; Expression q1; Expression q2], [e1; e2])
      when id = connective_and or id = connective_or ->
      let c = constant (string_of_id id) in
      let te1 = trad ren e1
      and te2 = trad ren e2 in
      let q1' = apply_post ren env (current_date ren) (anonymous q1)
      and q2' = apply_post ren env (current_date ren) (anonymous q2) in
      CC_app (CC_expr c, [CC_expr q1'.a_value; CC_expr q2'.a_value; te1; te2])

  | SApp ([Variable id; Expression q], [e]) when id = connective_not ->
      let c = constant (string_of_id id) in
      let te = trad ren e in
      let q' = apply_post ren env (current_date ren) (anonymous q) in
      CC_app (CC_expr c, [CC_expr q'.a_value; te])

  | SApp _ ->
      invalid_arg "mlise.trad (SApp)"

  | Apply (f, args) ->
      let trad_arg (ren,args) = function
	| Term a ->
	    let ((_,tya),efa,_,_) as ca = a.info.kappa in
	    let ta = trad ren a in
	    let w = get_writes efa in
	    let ren' = next ren w in
	    ren', ta::args
	| Refarg _ ->
	    ren, args
	| Type v -> 
	    let c = trad_ml_type_v ren env v in
	    ren, (CC_expr c)::args
      in
      let ren',targs = List.fold_left trad_arg (ren,[]) args in
      let tf = trad ren' f in
      let cf = f.info.kappa in
      let c,(s,_,_),capp = effect_app ren env f args in
      let tc_args =
	List.combine
	  (List.rev targs)
	  (Util.map_succeed
	     (function
		| Term x -> x.info.kappa
		| Refarg _ -> failwith "caught"
		| Type _ -> 
		    (result_id,TypePure mkSet),Peffect.bottom,[],None)
	     args)
      in
      make_app env ren tc_args ren' (tf,cf) (c,s,capp) ct
	
  | LetRef (x, e1, e2) ->
      let (_,v1),ef1,p1,q1 = e1.info.kappa in
      let te1 = trad ren e1 in
      let tv1 = trad_ml_type_v ren env v1 in
      let env' = add (x,Ref v1) env in
      let ren' = next ren [x] in
      let (_,v2),ef2,p2,q2 = e2.info.kappa in
      let tv2 = trad_ml_type_v ren' env' v2 in
      let te2 = trad ren' e2 in
      let ren'' = next ren' (get_writes ef2) in
      let t,ty = result_tuple ren'' (current_date ren) env
		   (CC_var result_id, tv2) (eft,qt) in
      let t = make_let_in ren' env' te2 p2
		(current_vars ren'' (get_writes ef2),q2)
		(result_id,tv2) (t,ty) in
      let t = make_let_in ren env te1 p1
     		(current_vars ren' (get_writes ef1),q1) (x,tv1) (t,ty) 
      in
      t

  | Let (x, e1, e2) ->
      let (_,v1),ef1,p1,q1 = e1.info.kappa in
      let te1 = trad ren e1 in
      let tv1 = trad_ml_type_v ren env v1 in
      let env' = add (x,v1) env in
      let ren' = next ren (get_writes ef1) in
      let (_,v2),ef2,p2,q2 = e2.info.kappa in
      let tv2 = trad_ml_type_v ren' env' v2 in
      let te2 = trad ren' e2 in
      let ren'' = next ren' (get_writes ef2) in
      let t,ty = result_tuple ren'' (current_date ren) env
		   (CC_var result_id, tv2) (eft,qt) in
      let t = make_let_in ren' env' te2 p2
		(current_vars ren'' (get_writes ef2),q2)
		(result_id,tv2) (t,ty) in
      let t = make_let_in ren env te1 p1
     		(current_vars ren' (get_writes ef1),q1) (x,tv1) (t,ty) 
      in
      t

  | LetRec (f,bl,v,var,e) ->
      let (_,ef,_,_) as c = 
	match tt with Arrow(_,c) -> c | _ -> assert false in
      let bl' = trad_binders ren env bl in
      let env' = traverse_binders env bl in
      let ren' = initial_renaming env' in
      let (phi0,var') = find_recursion f e.info.env in
      let te = trad ren' e in
      let t = make_letrec ren' env' (phi0,var') f bl' (te,e.info.kappa) c in
      CC_lam (bl', t)

  | PPoint (s,d) ->       
      let ren' = push_date ren s in
      trad_desc ren' env ct d

  | Debug _ -> failwith "Mlise.trad: Debug: not implemented"


and trad_binders ren env = function
  | [] -> 
      []
  | (_,BindType (Ref _ | Array _))::bl ->
      trad_binders ren env bl
  | (id,BindType v)::bl ->
      let tt = trad_ml_type_v ren env v in
      (id, CC_typed_binder tt) :: (trad_binders ren env bl)
  | (id,BindSet)::bl ->
      (id, CC_typed_binder mkSet) :: (trad_binders ren env bl)
  | (_,Untyped)::_ -> invalid_arg "trad_binders"

	
and trad_block ren env = function
  | [] -> 
      []
  | (Assert c)::block ->
      (Assert c)::(trad_block ren env block)
  | (Label s)::block ->
      let ren' = push_date ren s in
      (Label s)::(trad_block ren' env block)
  | (Statement e)::block ->
      let te = trad ren e in
      let _,efe,_,_ = e.info.kappa in
      let w = get_writes efe in
      let ren' = next ren w in
      (Statement (te,e.info.kappa))::(trad_block ren' env block)


and trans ren e =
  let env = e.info.env in
  let _,ef,p,_ = e.info.kappa in
  let ty = trad_ml_type_c ren env e.info.kappa in
  let ids = get_reads ef in
  let al = current_vars ren ids in
  let c = trad ren e in
  let c = abs_pre ren env (c,ty) p in
  let bl = binding_of_alist ren env al in
  make_abs (List.rev bl) c

