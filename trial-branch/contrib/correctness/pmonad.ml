(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Util
open Names
open Term
open Termast

open Pmisc
open Putil
open Ptype
open Past
open Prename
open Penv
open Pcic
open Peffect


(* [product ren [y1,z1;...;yk,zk] q] constructs
 * the (possibly dependent) tuple type
 *
 *      z1 x ... x zk                             if no post-condition
 * or   \exists. y1:z1. ... yk:zk. (Q x1 ... xn)  otherwise
 *
 * where the xi are given by the renaming [ren].
 *)

let product_name = function
  | 2 -> "prod"
  | n -> check_product_n n; Printf.sprintf "tuple_%d" n

let dep_product_name = function
  | 1 -> "sig"
  | n -> check_dep_product_n n; Printf.sprintf "sig_%d" n

let product ren env before lo = function
  | None -> (* non dependent case *)
      begin match lo with
	| [_,v] -> v
	| _ ->
	    let s = product_name (List.length lo) in
      	    Term.applist (constant s, List.map snd lo)
      end
  | Some q -> (* dependent case *)
      let s = dep_product_name (List.length lo) in
      let a' = apply_post ren env before q in
      Term.applist (constant s, (List.map snd lo) @ [a'.a_value])
	
(* [arrow ren v pl] abstracts the term v over the pre-condition if any
 * i.e. computes
 *
 *     (P1 x1 ... xn) -> ... -> (Pk x1 ... xn) -> v
 * 
 * where the xi are given by the renaming [ren].
 *)

let arrow ren env v pl =
  List.fold_left 
    (fun t p -> 
       if p.p_assert then t else Term.mkArrow (apply_pre ren env p).p_value t) 
    v pl
	
(* [abstract_post ren env (e,q) (res,v)] abstract a post-condition q
 * over the write-variables of e *)

let rec abstract_post ren env (e,q) =
  let after_id id = id_of_string ((string_of_id id) ^ "'") in
  let (_,go) = Peffect.get_repr e in
  let al = List.map (fun id -> (id,after_id id)) go in
  let q = Option.map (named_app (subst_in_constr al)) q in
  let tgo = List.map (fun (id,aid) -> (aid, trad_type_in_env ren env id)) al in
  Option.map (named_app (abstract tgo)) q

(* Translation of effects types in cic types.
 *
 * [trad_ml_type_v] and [trad_ml_type_c] translate types with effects
 * into cic types.
 *)

and prod ren env g = 
  List.map
    (fun id -> (current_var ren id, trad_type_in_env ren env id)) 
    g

and input ren env e  =
  let i,_ = Peffect.get_repr e in
  prod ren env i

and output ren env ((id,v),e) =
  let tv = trad_ml_type_v ren env v in
  let _,o = Peffect.get_repr e in
  (prod ren env o) @ [id,tv]

and input_output ren env c =
  let ((res,v),e,_,_) = c in
  input ren env e, output ren env ((res,v),e)

(* The function t -> \barre{t} on V and C. *)

and trad_ml_type_c ren env c =
  let ((res,v),e,p,q) = c in
  let q = abstract_post ren env (e,q) in
  let lo = output ren env ((res,v),e) in
  let ty = product ren env (current_date ren) lo q in
  let ty = arrow ren env ty p in
  let li = input ren env e in
  n_mkNamedProd ty li

and trad_ml_type_v ren env = function
    
  | Ref _ | Array _ -> invalid_arg "Monad.trad_ml_type_v"
	
  | Arrow (bl, c) ->
      let bl',ren',env' =
	List.fold_left
	  (fun (bl,ren,env) b -> match b with
	     | (id,BindType ((Ref _ | Array _) as v)) ->
		 let env' = add (id,v) env in
		 let ren' = initial_renaming env' in
		 (bl,ren',env')
	     | (id,BindType v) -> 
		 let tt = trad_ml_type_v ren env v in
		 let env' = add (id,v) env in
		 let ren' = initial_renaming env' in
		 (id,tt)::bl,ren',env'
	     | (id, BindSet) ->
		 (id,mkSet) :: bl,ren,env
	     | _ -> failwith "Monad: trad_ml_type_v: not yet implemented"
 	  )
 	  ([],ren,env) bl 
      in
      n_mkNamedProd (trad_ml_type_c ren' env' c) bl'
	
  | TypePure c ->
      (apply_pre ren env (anonymous_pre false c)).p_value

and trad_imp_type ren env = function
  | Ref v        -> trad_ml_type_v ren env v
  | Array (c,v)  -> Term.applist (constant "array", 
				  [c; trad_ml_type_v ren env v])
  | _            -> invalid_arg "Monad.trad_imp_type"

and trad_type_in_env ren env id =
  let v = type_in_env env id in trad_imp_type ren env v



(* bindings *)

let binding_of_alist ren env al =
  List.map
    (fun (id,id') -> (id', CC_typed_binder (trad_type_in_env ren env id)))
    al


(* [make_abs bl t p] abstracts t w.r.t binding list bl., that is
 * [x1:t1]...[xn:tn]t. Returns t if the binding is empty. *)

let make_abs bl t = match bl with
  | [] -> t
  | _  -> CC_lam (bl, t)


(* [result_tuple ren before env (res,v) (ef,q)] constructs the tuple 
 *
 *    (y1,...,yn,res,?::(q/ren y1 ... yn res))
 *
 * where the yi are the values of the output of ef.
 * if there is no yi and no post-condition, it is simplified in res itself.
 *)

let simple_constr_of_prog = function
  | CC_expr c -> c
  | CC_var id -> mkVar id
  | _ -> assert false

let make_tuple l q ren env before = match l with
  | [e,_] when q = None -> 
      e
  | _ ->
      let tl = List.map snd l in
      let dep,h,th = match q with
	| None -> false,[],[]
	| Some c ->
	    let args = List.map (fun (e,_) -> simple_constr_of_prog e) l in
	    let c = apply_post ren env before c in
	    true,
	    [ CC_hole (Term.applist (c.a_value, args)) ], (* hole *)
	    [ c.a_value ]                     (* type of the hole *)
      in 
      CC_tuple (dep, tl @ th, (List.map fst l) @ h)

let result_tuple ren before env (res,v) (ef,q) =
  let ids = get_writes ef in
  let lo = 
    (List.map (fun id -> 
		 let id' = current_var ren id in
		 CC_var id', trad_type_in_env ren env id) ids)
    @ [res,v]
  in
  let q = abstract_post ren env (ef,q) in
  make_tuple lo q ren env before,
  product ren env before lo q


(* [make_let_in ren env fe p (vo,q) (res,v) t] constructs the term
   
        [ let h1 = ?:P1 in ... let hn = ?:Pm in ]
          let y1,y2,...,yn, res [,q] = fe in
          t

   vo=[_,y1;...;_,ym] are list of renamings.
   v is the type of res
   *)

let let_in_pre ty p t =
  let h = p.p_value in
  CC_letin (false, ty, [pre_name p.p_name,CC_typed_binder h], CC_hole h, t)

let multiple_let_in_pre ty hl t =
  List.fold_left (fun t h -> let_in_pre ty h t) t hl

let make_let_in ren env fe p (vo,q) (res,tyres) (t,ty) =
  let b = [res, CC_typed_binder tyres] in
  let b',dep = match q with
    | None -> [],false
    | Some q -> [post_name q.a_name, CC_untyped_binder],true 
  in
  let bl = (binding_of_alist ren env vo) @ b @ b' in
  let tyapp =
    let n = succ (List.length vo) in
    let name = match q with None -> product_name n | _ -> dep_product_name n in
    constant name 
  in
  let t = CC_letin (dep, ty, bl, fe, t) in
  multiple_let_in_pre ty (List.map (apply_pre ren env) p) t


(* [abs_pre ren env (t,ty) pl] abstracts a term t with respect to the 
 * list of pre-conditions [pl]. Some of them are real pre-conditions
 * and others are assertions, according to the boolean field p_assert,
 * so we construct the term
 *   [h1:P1]...[hn:Pn]let h'1 = ?:P'1 in ... let H'm = ?:P'm in t
 *)

let abs_pre ren env (t,ty) pl =
  List.fold_left
    (fun t p ->
       if p.p_assert then
	 let_in_pre ty (apply_pre ren env p) t
       else
	 let h = pre_name p.p_name in 
	 CC_lam ([h,CC_typed_binder (apply_pre ren env p).p_value],t))
    t pl
    

(* [make_block ren env finish bl] builds the translation of a block
 * finish is the function that is applied to the result at the end of the
 * block. *)

let make_block ren env finish bl =
  let rec rec_block ren result = function
    | [] ->
	finish ren result
    | (Assert c) :: block ->
	let t,ty = rec_block ren result block in
	let c = apply_assert ren env c in
	let p = { p_assert = true; p_name = c.a_name; p_value = c.a_value } in
	let_in_pre ty p t, ty
    | (Label s) :: block ->
	let ren' = push_date ren s in
	rec_block ren' result block
    | (Statement (te,info)) :: block ->
	let (_,tye),efe,pe,qe = info in
	let w = get_writes efe in
	let ren' = next ren w in
	let id = result_id in
	let tye = trad_ml_type_v ren env tye in
	let t = rec_block ren' (Some (id,tye)) block in
	make_let_in ren env te pe (current_vars ren' w,qe) (id,tye) t,
	snd t
  in
  let t,_ = rec_block ren None bl in
  t


(* [make_app env ren args ren' (tf,cf) (cb,s,capp) c]
 * constructs the application of [tf] to [args].
 * capp is the effect of application, after substitution (s) and cb before
 *)

let eq ty e1 e2 =
  Term.applist (constant "eq", [ty; e1; e2])

let lt r e1 e2 =
  Term.applist (r, [e1; e2])

let is_recursive env = function
  | CC_var x -> 
      (try let _ = find_recursion x env in true with Not_found -> false)
  | _ -> false

let if_recursion env f = function
  | CC_var x ->
      (try let v = find_recursion x env in (f v x) with Not_found -> [])
  | _ -> []

let dec_phi ren env s svi =
  if_recursion env
    (fun (phi0,(cphi,r,_)) f -> 
       let phi = subst_in_constr svi (subst_in_constr s cphi) in
       let phi = (apply_pre ren env (anonymous_pre true phi)).p_value in
       [CC_expr phi; CC_hole (lt r phi (mkVar phi0))])

let eq_phi ren env s svi =
  if_recursion env
    (fun (phi0,(cphi,_,a)) f ->
       let phi = subst_in_constr svi (subst_in_constr s cphi) in
       let phi = (apply_pre ren env (anonymous_pre true phi)).p_value in
       [CC_hole (eq a phi phi)])

let is_ref_binder = function 
  | (_,BindType (Ref _ | Array _)) -> true
  | _ -> false

let make_app env ren args ren' (tf,cf) ((bl,cb),s,capp) c =
  let ((_,tvf),ef,pf,qf) = cf in
  let (_,eapp,papp,qapp) = capp in
  let ((_,v),e,p,q) = c in
  let bl = List.filter (fun b -> not (is_ref_binder b)) bl in
  let recur = is_recursive env tf in
  let before = current_date ren in
  let ren'' = next ren' (get_writes ef) in
  let ren''' = next ren'' (get_writes eapp) in
  let res = result_id in
  let vi,svi =
    let ids = List.map fst bl in 
    let s = fresh (avoid ren ids) ids in
    List.map snd s, s
  in
  let tyres = subst_in_constr svi (trad_ml_type_v ren env v) in
  let t,ty = result_tuple ren''' before env (CC_var res, tyres) (e,q) in
  let res_f = id_of_string "vf" in
  let inf,outf =
    let i,o = let _,e,_,_ = cb in get_reads e, get_writes e in
    let apply_s = List.map (fun id -> try List.assoc id s with _ -> id) in
    apply_s i, apply_s o
  in
  let fe =
    let xi = List.rev (List.map snd (current_vars ren'' inf)) in
    let holes = List.map (fun x -> (apply_pre ren'' env x).p_value)
		  (List.map (pre_app (subst_in_constr svi)) papp) in
    CC_app ((if recur then tf else CC_var res_f),
	    (dec_phi ren'' env s svi tf) 
	    @(List.map (fun id -> CC_var id) (vi @ xi))
	    @(eq_phi ren'' env s svi tf)
	    @(List.map (fun c -> CC_hole c) holes))
  in
  let qapp' = Option.map (named_app (subst_in_constr svi)) qapp in
  let t = 
    make_let_in ren'' env fe [] (current_vars ren''' outf,qapp')
      (res,tyres) (t,ty)
  in
  let t =
    if recur then 
      t
    else
      make_let_in ren' env tf pf
	(current_vars ren'' (get_writes ef),qf)
	(res_f,trad_ml_type_v ren env tvf) (t,ty)
  in
  let rec eval_args ren = function
    | [] -> t
    | (vx,(ta,((_,tva),ea,pa,qa)))::args ->
	let w = get_writes ea in
	let ren' = next ren w in
	let t' = eval_args ren' args in
	make_let_in ren env ta pa (current_vars ren' (get_writes ea),qa)
	  (vx,trad_ml_type_v ren env tva) (t',ty)
  in
  eval_args ren (List.combine vi args)


(* [make_if ren env (tb,cb) ren' (t1,c1) (t2,c2)]
 * constructs the term corresponding to a if expression, i.e
 *
 *       [p] let o1, b [,q1] = m1 [?::p1] in
 *           Cases b of
 *              R => let o2, v2 [,q2] = t1  [?::p2] in 
 *                   (proj (o1,o2)), v2 [,?::q] 
 *            | S => let o2, v2 [,q2] = t2  [?::p2] in 
 *                   (proj (o1,o2)), v2 [,?::q] 
 *)

let make_if_case ren env ty (b,qb) (br1,br2) =
  let id_b,ty',ty1,ty2 = match qb with
    | Some q ->  
  	let q = apply_post ren env (current_date ren) q in
    	let (name,t1,t2) = Term.destLambda q.a_value in
	q.a_name,
    	Term.mkLambda (name, t1, mkArrow t2 ty),
	Term.mkApp (q.a_value, [| coq_true |]),
	Term.mkApp (q.a_value, [| coq_false |])
    | None -> assert false
  in
  let n = test_name Anonymous in
  CC_app (CC_case (ty', b, [CC_lam ([n,CC_typed_binder ty1], br1);
			    CC_lam ([n,CC_typed_binder ty2], br2)]),
	  [CC_var (post_name id_b)])

let make_if ren env (tb,cb) ren' (t1,c1) (t2,c2) c =
  let ((_,tvb),eb,pb,qb) = cb in
  let ((_,tv1),e1,p1,q1) = c1 in
  let ((_,tv2),e2,p2,q2) = c2 in
  let ((_,t),e,p,q) = c in

  let wb = get_writes eb in
  let resb = id_of_string "resultb" in
  let res = result_id in
  let tyb = trad_ml_type_v ren' env tvb in
  let tt = trad_ml_type_v ren env t in

  (* une branche de if *)
  let branch (tv_br,e_br,p_br,q_br) f_br  = 
    let w_br = get_writes e_br in
    let ren'' = next ren' w_br in
    let t,ty = result_tuple ren'' (current_date ren') env
		 (CC_var res,tt) (e,q) in
    make_let_in ren' env f_br p_br (current_vars ren'' w_br,q_br)
      (res,tt) (t,ty),
    ty
  in
  let t1,ty1 = branch c1 t1 in
  let t2,ty2 = branch c2 t2 in
  let ty = ty1 in
  let qb = force_bool_name qb in
  let t = make_if_case ren env ty (CC_var resb,qb) (t1,t2) in
  make_let_in ren env tb pb (current_vars ren' wb,qb) (resb,tyb) (t,ty)


(* [make_while ren env (cphi,r,a) (tb,cb) (te,ce) c]
 * constructs the term corresponding to the while, i.e.
 * 
 *    [h:(I x)](well_founded_induction
 *              A R ?::(well_founded A R)
 *              [Phi:A] (x) Phi=phi(x)->(I x)-> \exists x'.res.(I x')/\(S x')
 *              [Phi_0:A][w:(Phi:A)(Phi<Phi_0)-> ...]
 *                [x][eq:Phi_0=phi(x)][h:(I x)]
 *                   Cases (b x) of
 *                     (left  HH) => (x,?::(IS x))
 *                   | (right HH) => let x1,_,_ = (e x ?) in
 *                                   (w phi(x1) ? x1 ? ?)
 *              phi(x) x ? ?)
 *)

let id_phi = id_of_string "phi"
let id_phi0 = id_of_string "phi0"

let make_body_while ren env phi_of a r id_phi0 id_w (tb,cb) tbl (i,c) =
  let ((_,tvb),eb,pb,qb) = cb in
  let (_,ef,_,is) = c in

  let ren' = next ren (get_writes ef) in
  let before = current_date ren in
  
  let ty = 
    let is = abstract_post ren' env (ef,is) in
    let _,lo = input_output ren env c in
    product ren env before lo is 
  in
  let resb = id_of_string "resultb" in
  let tyb = trad_ml_type_v ren' env tvb in
  let wb = get_writes eb in

  (* première branche: le test est vrai => e;w *)
  let t1 = 
    make_block ren' env 
      (fun ren'' result -> match result with
	 | Some (id,_) ->
	     let v = List.rev (current_vars ren'' (get_writes ef)) in
	       CC_app (CC_var id_w,
		       [CC_expr (phi_of ren'');
			CC_hole (lt r (phi_of ren'') (mkVar id_phi0))]
		       @(List.map (fun (_,id) -> CC_var id) v)
		       @(CC_hole (eq a (phi_of ren'') (phi_of ren'')))
		       ::(match i with
			    | None -> [] 
			    | Some c -> 
				[CC_hole (apply_assert ren'' env c).a_value])),
	       ty
      	 | None -> failwith "a block should contain at least one statement")
      tbl
  in
        
  (* deuxième branche: le test est faux => on sort de la boucle *)
  let t2,_ = 
    result_tuple ren' before env
      (CC_expr (constant "tt"),constant "unit") (ef,is)
  in

  let b_al = current_vars ren' (get_reads eb) in
  let qb = force_bool_name qb in
  let t = make_if_case ren' env ty (CC_var resb,qb) (t1,t2) in
  let t = 
    make_let_in ren' env tb pb (current_vars ren' wb,qb) (resb,tyb) (t,ty) 
  in
  let t = 
    let pl = List.map (pre_of_assert false) (list_of_some i) in
    abs_pre ren' env (t,ty) pl 
  in
  let t = 
    CC_lam ([var_name Anonymous,
	     CC_typed_binder (eq a (mkVar id_phi0) (phi_of ren'))],t) 
  in
  let bl = binding_of_alist ren env (current_vars ren' (get_writes ef)) in
  make_abs (List.rev bl) t


let make_while ren env (cphi,r,a) (tb,cb) tbl (i,c) =
  let (_,ef,_,is) = c in
  let phi_of ren = (apply_pre ren env (anonymous_pre true cphi)).p_value in
  let wf_a_r = Term.applist (constant "well_founded", [a; r]) in

  let before = current_date ren in
  let ren' = next ren (get_writes ef) in
  let al = current_vars ren' (get_writes ef) in
  let v =   
    let _,lo = input_output ren env c in
    let is = abstract_post ren' env (ef,is) in
    match i with
      | None -> product ren' env before lo is
      | Some ci -> 
	  Term.mkArrow (apply_assert ren' env ci).a_value 
	    (product ren' env before lo is) 
  in
  let v = Term.mkArrow (eq a (mkVar id_phi) (phi_of ren')) v in
  let v = 
    n_mkNamedProd v 
      (List.map (fun (id,id') -> (id',trad_type_in_env ren env id)) al) 
  in
  let tw = 
    Term.mkNamedProd id_phi a
      (Term.mkArrow (lt r (mkVar id_phi) (mkVar id_phi0)) v) 
  in
  let id_w = id_of_string "loop" in
  let vars = List.rev (current_vars ren (get_writes ef)) in
  let body =
    make_body_while ren env phi_of a r id_phi0 id_w (tb,cb) tbl (i,c) 
  in
  CC_app (CC_expr (constant "well_founded_induction"),
	  [CC_expr a; CC_expr r;
	   CC_hole wf_a_r;
	   CC_expr (Term.mkNamedLambda id_phi a v);
	   CC_lam ([id_phi0, CC_typed_binder a;
		    id_w, CC_typed_binder tw],
		   body);
	   CC_expr (phi_of ren)]
	  @(List.map (fun (_,id) -> CC_var id) vars)
          @(CC_hole (eq a (phi_of ren) (phi_of ren)))
	  ::(match i with
	       | None -> [] 
	       | Some c -> [CC_hole (apply_assert ren env c).a_value])) 


(* [make_letrec ren env (phi0,(cphi,r,a)) bl (te,ce) c]
 * constructs the term corresponding to the let rec i.e.
 *
 * [x][h:P(x)](well_founded_induction 
 *              A R ?::(well_founded A R)
 *              [Phi:A] (bl) (x) Phi=phi(x)->(P x)-> \exists x'.res.(Q x x')
 *              [Phi_0:A][w:(Phi:A)(Phi<Phi_0)-> ...]
 *                [bl][x][eq:Phi_0=phi(x)][h:(P x)]te
 *              phi(x) bl x ? ?)
 *)

let make_letrec ren env (id_phi0,(cphi,r,a)) idf bl (te,ce) c =
  let (_,ef,p,q) = c in
  let phi_of ren = (apply_pre ren env (anonymous_pre true cphi)).p_value in
  let wf_a_r = Term.applist (constant "well_founded", [a; r]) in

  let before = current_date ren in
  let al = current_vars ren (get_reads ef) in
  let v = 
    let _,lo = input_output ren env c in
    let q = abstract_post ren env (ef,q) in
    arrow ren env (product ren env (current_date ren) lo q) p 
  in
  let v = Term.mkArrow (eq a (mkVar id_phi) (phi_of ren)) v in
  let v = 
    n_mkNamedProd v 
      (List.map (fun (id,id') -> (id',trad_type_in_env ren env id)) al) 
  in
  let v = 
    n_mkNamedProd v
      (List.map (function (id,CC_typed_binder c) -> (id,c) 
		   | _ -> assert false) (List.rev bl)) 
  in
  let tw = 
    Term.mkNamedProd id_phi a
      (Term.mkArrow (lt r (mkVar id_phi) (mkVar id_phi0)) v) 
  in
  let vars = List.rev (current_vars ren (get_reads ef)) in
  let body =
    let al = current_vars ren (get_reads ef) in
    let bod = abs_pre ren env (te,v) p in
    let bod = CC_lam ([var_name Anonymous,
		       CC_typed_binder (eq a (mkVar id_phi0) (phi_of ren))],
		      bod) 
    in
    let bl' = binding_of_alist ren env al in
    make_abs (bl@(List.rev bl')) bod
  in
  let t =
    CC_app (CC_expr (constant "well_founded_induction"),
	    [CC_expr a; CC_expr r;
	     CC_hole wf_a_r;
	     CC_expr (Term.mkNamedLambda id_phi a v);
	     CC_lam ([id_phi0, CC_typed_binder a;
		      idf, CC_typed_binder tw],
		     body);
	     CC_expr (phi_of ren)]
	    @(List.map (fun (id,_) -> CC_var id) bl)
	    @(List.map (fun (_,id) -> CC_var id) vars)
            @[CC_hole (eq a (phi_of ren) (phi_of ren))]
	   )
  in
  (* on abstrait juste par rapport aux variables de ef *)
  let al = current_vars ren (get_reads ef) in
  let bl = binding_of_alist ren env al in
  make_abs (List.rev bl) t


(* [make_access env id c] Access in array id.
 *
 * Constructs [t:(array s T)](access_g s T t c ?::(lt c s)).
 *)

let array_info ren env id =
  let ty = type_in_env env id in
  let size,v = dearray_type ty in
  let ty_elem = trad_ml_type_v ren env v in
  let ty_array = trad_imp_type ren env ty in
  size,ty_elem,ty_array

let make_raw_access ren env (id,id') c =
  let size,ty_elem,_ = array_info ren env id in
  Term.applist (constant "access", [size; ty_elem; mkVar id'; c])

let make_pre_access ren env id c =
  let size,_,_ = array_info ren env id in
  conj (lt (constant "Zle") (constant "ZERO") c)
       (lt (constant "Zlt") c size)
      
let make_raw_store ren env (id,id') c1 c2 =
  let size,ty_elem,_ = array_info ren env id in
  Term.applist (constant "store", [size; ty_elem; mkVar id'; c1; c2])
