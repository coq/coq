(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Termops
open Environ
open Constrintern
open Himsg
open Proof_trees
open Topconstr

open Pmisc
open Putil
open Prename
open Ptype
open Past
open Penv 
open Peffect
open Pcicenv

(* Ce module implante le jugement  Gamma |-a e : kappa  de la thèse.
 * Les annotations passent du type CoqAst.t au type Term.constr ici. 
 * Les post-conditions sont abstraites par rapport au résultat. *)

let simplify_type_of env sigma t =
  Reductionops.nf_betaiota (Typing.type_of env sigma t)

let just_reads e =
  difference (get_reads e) (get_writes e)

let type_v_sup loc t1 t2 =
  if t1 = t2 then
    t1
  else
    Perror.if_branches loc

let typed_var ren env (phi,r) =
  let sign = Pcicenv.before_after_sign_of ren env in
  let a = simplify_type_of (Global.env_of_context sign) Evd.empty phi in
  (phi,r,a)

(* Application de fonction *)

let rec convert = function
  | (TypePure c1, TypePure c2) -> 
      Reductionops.is_conv (Global.env ()) Evd.empty c1 c2
  | (Ref v1, Ref v2) -> 
      convert (v1,v2)
  | (Array (s1,v1), Array (s2,v2)) -> 
      (Reductionops.is_conv (Global.env ()) Evd.empty s1 s2) && (convert (v1,v2))
  | (v1,v2) -> v1 = v2
      
let effect_app ren env f args =
  let n = List.length args in
  let tf = 
    let ((_,v),_,_,_) = f.info.kappa in
    match v with TypePure c -> v_of_constr c | _ -> v
  in
  let bl,c = 
    match tf with
	Arrow (bl, c) ->
	  if List.length bl <> n then Perror.partial_app f.loc;
	  bl,c
      | _ -> Perror.app_of_non_function f.loc
  in
  let check_type loc v t so =
    let v' = type_v_rsubst so v in
    if not (convert (v',t)) then Perror.expected_type loc (pp_type_v v')
  in
  let s,so,ok = 
    (* s est la substitution des références, so celle des autres arg. 
     * ok nous dit si les arguments sont sans effet i.e. des expressions *)
    List.fold_left
    (fun (s,so,ok) (b,a) ->
       match b,a with
	   (id,BindType (Ref _ | Array _ as v)), Refarg id' ->
	     let ta = type_in_env env id' in
	     check_type f.loc v ta so;
	     (id,id')::s, so, ok
	 | _, Refarg _ -> Perror.should_be_a_variable f.loc
	 | (id,BindType v), Term t ->
	     let ((_,ta),_,_,_) = t.info.kappa in
	     check_type t.loc v ta so;
	     (match t.desc with
		  Expression c -> s, (id,c)::so, ok
		| _ -> s,so,false)
	 | (id,BindSet), Type v ->
	     let c = Pmonad.trad_ml_type_v ren env v in
	     s, (id,c)::so, ok
	 | (id,BindSet), Term t -> Perror.expects_a_type id t.loc
	 | (id,BindType _), Type _ -> Perror.expects_a_term id
	 | (_,Untyped), _ -> invalid_arg "effects_app")
    ([],[],true)
    (List.combine bl args)
  in
  let (id,v),ef,pre,post = type_c_subst s c in
  (bl,c), (s,so,ok), ((id,type_v_rsubst so v),ef,pre,post)

(* Execution of a Coq AST. Returns value and type.
 * Also returns its variables *)

let state_coq_ast sign a =
  let env = Global.env_of_context sign in
  let j =
    reraise_with_loc (constr_loc a) (judgment_of_rawconstr Evd.empty env) a in
  let ids = global_vars env j.uj_val in
  j.uj_val, j.uj_type, ids

(* [is_pure p] tests wether the program p is an expression or not. *)

let type_of_expression ren env c =
  let sign = now_sign_of ren env in
  simplify_type_of (Global.env_of_context sign) Evd.empty c

let rec is_pure_type_v = function
    TypePure _ -> true
  | Arrow (bl,c) -> List.for_all is_pure_arg bl & is_pure_type_c c
  | Ref _ | Array _ -> false
and is_pure_arg = function
    (_,BindType v) -> is_pure_type_v v
  | (_,BindSet) -> true
  | (_,Untyped) -> false
and is_pure_type_c = function
    (_,v),_,[],None -> is_pure_type_v v
  | _ -> false

let rec is_pure_desc ren env = function
    Variable id ->
      not (is_in_env env id) or (is_pure_type_v (type_in_env env id))
  | Expression c -> 
      (c = isevar) or (is_pure_cci (type_of_expression ren env c))
  | Acc _ -> true
  | TabAcc (_,_,p) -> is_pure ren env p
  | Apply (p,args) -> 
      is_pure ren env p & List.for_all (is_pure_arg ren env) args
  | SApp _ | Aff _ | TabAff _ | Seq _ | While _ | If _ 
  | Lam _ | LetRef _ | Let _ | LetRec _ -> false
  | Debug (_,p) -> is_pure ren env p
  | PPoint (_,d) -> is_pure_desc ren env d
and is_pure ren env p =
  p.pre = [] & p.post = None & is_pure_desc ren env p.desc
and is_pure_arg ren env = function
    Term p -> is_pure ren env p
  | Type _ -> true
  | Refarg _ -> false

(* [state_var ren env (phi,r)] returns a tuple (e,(phi',r')) 
 * where e is the effect of the variant phi and phi',r' the corresponding 
 * constr of phi and r.
 *)

let state_var ren env (phi,r) = 
  let sign = Pcicenv.before_after_sign_of ren env in
  let phi',_,ids = state_coq_ast sign phi in
  let ef = List.fold_left
	     (fun e id ->
		if is_mutable_in_env env id then Peffect.add_read id e else e)
	     Peffect.bottom ids in
  let r',_,_ = state_coq_ast (Global.named_context ()) r in
  ef,(phi',r')
	
(* [state_pre ren env pl] returns a pair (e,c) where e is the effect of the
 * pre-conditions list pl and cl the corresponding constrs not yet abstracted
 * over the variables xi (i.e. c NOT [x1]...[xn]c !)
 *)

let state_pre ren env pl =
  let state e p =
    let sign = Pcicenv.before_sign_of ren env in
    let cc,_,ids = state_coq_ast sign p.p_value in
    let ef = List.fold_left
	       (fun e id ->
		  if is_mutable_in_env env id then
		    Peffect.add_read id e
		  else if is_at id then
		    let uid,_ = un_at id in
		    if is_mutable_in_env env uid then
		      Peffect.add_read uid e
		    else
		      e
	     	  else
		    e)
	       e ids 
    in
    ef,{ p_assert = p.p_assert; p_name = p.p_name; p_value = cc }
  in
  List.fold_left 
    (fun (e,cl) p -> let ef,c = state e p in (ef,c::cl)) 
    (Peffect.bottom,[]) pl

let state_assert ren env a =
  let p = pre_of_assert true a in
  let e,l = state_pre ren env [p] in
  e,assert_of_pre (List.hd l)

let state_inv ren env = function
    None -> Peffect.bottom, None
  | Some i -> let e,p = state_assert ren env i in e,Some p
	  
(* [state_post ren env (id,v,ef) q] returns a pair (e,c)
 * where e is the effect of the
 * post-condition q and c the corresponding constr not yet abstracted
 * over the variables xi, yi and result.
 * Moreover the RW variables not appearing in ef have been replaced by
 * RO variables, and (id,v) is the result
 *)

let state_post ren env (id,v,ef) = function
    None -> Peffect.bottom, None
  | Some q ->
      let v' = Pmonad.trad_ml_type_v ren env v in
      let sign = Pcicenv.before_after_result_sign_of (Some (id,v')) ren env in
      let cc,_,ids = state_coq_ast sign q.a_value in
      let ef,c = 
	List.fold_left
	  (fun (e,c) id ->
	     if is_mutable_in_env env id then
	       if is_write ef id then
		 Peffect.add_write id e, c
	       else
		 Peffect.add_read id e,
		 subst_in_constr [id,at_id id ""] c
	     else if is_at id then
	       let uid,_ = un_at id in
	       if is_mutable_in_env env uid then
		 Peffect.add_read uid e, c
	       else
		 e,c
	     else
	       e,c)
	  (Peffect.bottom,cc) ids 
      in
      let c = abstract [id,v'] c in
      ef, Some { a_name = q.a_name; a_value = c }

(* transformation of AST into constr in types V and C *)

let rec cic_type_v env ren = function
  | Ref v -> Ref (cic_type_v env ren v)
  | Array (com,v) ->
      let sign = Pcicenv.now_sign_of ren env in
      let c = interp_constr Evd.empty (Global.env_of_context sign) com in
      Array (c, cic_type_v env ren v)
  | Arrow (bl,c) ->
      let bl',ren',env' =
	List.fold_left
	(fun (bl,ren,env) b ->
	   let b' = cic_binder env ren b in
	   let env' = traverse_binders env [b'] in
	   let ren' = initial_renaming env' in
	     b'::bl,ren',env')
	([],ren,env) bl
      in
      let c' = cic_type_c env' ren' c in
      Arrow (List.rev bl',c')
  | TypePure com ->
      let sign = Pcicenv.cci_sign_of ren env in
      let c = interp_constr Evd.empty (Global.env_of_context sign) com in
      TypePure c

and cic_type_c env ren ((id,v),e,p,q) =
  let v' = cic_type_v env ren v in
  let cv = Pmonad.trad_ml_type_v ren env v' in
  let efp,p' = state_pre ren env p in
  let efq,q' = state_post ren env (id,v',e) q in
  let ef = Peffect.union e (Peffect.union efp efq) in
  ((id,v'),ef,p',q')

and cic_binder env ren = function
  | (id,BindType v) ->
      let v' = cic_type_v env ren v in
      let env' = add (id,v') env in
      let ren' = initial_renaming env' in
      (id, BindType v')
  | (id,BindSet) -> (id,BindSet)
  | (id,Untyped) -> (id,Untyped)

and cic_binders env ren = function
    [] -> []
  | b::bl ->
      let b' = cic_binder env ren b in
      let env' = traverse_binders env [b'] in
      let ren' = initial_renaming env' in
      b' :: (cic_binders env' ren' bl)


(* The case of expressions.
 * 
 * Expressions are programs without neither effects nor pre/post conditions.
 * But access to variables are allowed.
 *
 * Here we transform an expression into the corresponding constr,
 * the variables still appearing as VAR (they will be abstracted in
 * Mlise.trad)
 * We collect the pre-conditions (e<N for t[e]) as we traverse the term.
 * We also return the effect, which does contain only *read* variables.
 *)

let states_expression ren env expr =
  let rec effect pl = function
    | Variable id -> 
	(if is_global id then constant (string_of_id id) else mkVar id),
	pl, Peffect.bottom
    | Expression c -> c, pl, Peffect.bottom
    | Acc id -> mkVar id, pl, Peffect.add_read id Peffect.bottom
    | TabAcc (_,id,p) ->
	let c,pl,ef = effect pl p.desc in
	let pre = Pmonad.make_pre_access ren env id c in
	Pmonad.make_raw_access ren env (id,id) c, 
	(anonymous_pre true pre)::pl, Peffect.add_read id ef
    | Apply (p,args) ->
	let a,pl,e = effect pl p.desc in
	let args,pl,e =
	  List.fold_right
	    (fun arg (l,pl,e) -> 
	       match arg with
		   Term p ->
		     let carg,pl,earg = effect pl p.desc in
		     carg::l,pl,Peffect.union e earg
		 | Type v ->
		     let v' = cic_type_v env ren v in
		     (Pmonad.trad_ml_type_v ren env v')::l,pl,e
		 | Refarg _ -> assert false) 
	    args ([],pl,e) 
	in
	Term.applist (a,args),pl,e
    | _ -> invalid_arg "Ptyping.states_expression"
  in
  let e0,pl0 = state_pre ren env expr.pre in
  let c,pl,e = effect [] expr.desc in
  let sign = Pcicenv.before_sign_of ren env in
  (*i WAS
  let c = (Trad.ise_resolve true empty_evd [] (gLOB sign) c)._VAL in
  i*)
  let ty = simplify_type_of (Global.env_of_context sign) Evd.empty c in
  let v = TypePure ty in
  let ef = Peffect.union e0 e in
  Expression c, (v,ef), pl0@pl


(* We infer here the type with effects.
 * The type of types with effects (ml_type_c) is defined in the module ProgAst.
 * 
 * A program of the shape {P} e {Q} has a type 
 *   
 *        V, E, {None|Some P}, {None|Some Q}
 *
 * where - V is the type of e
 *       - E = (I,O) is the effect; the input I contains
 *         all the input variables appearing in P,e and Q;
 *         the output O contains variables possibly modified in e
 *       - P is NOT abstracted
 *       - Q = [y'1]...[y'k][result]Q where O = {y'j}
 *         i.e. Q is only abstracted over the output and the result
 *         the other variables now refer to value BEFORE
 *)

let verbose_fix = ref false

let rec states_desc ren env loc = function
	
    Expression c ->
      let ty = type_of_expression ren env c in
      let v = v_of_constr ty in
      Expression c, (v,Peffect.bottom)

  | Acc _ ->
      failwith "Ptyping.states: term is supposed not to be pure"

  | Variable id ->
      let v = type_in_env env id in
      let ef = Peffect.bottom in
      Variable id, (v,ef)

  | Aff (x, e1) ->
      Perror.check_for_reference loc x (type_in_env env x);
      let s_e1 = states ren env e1 in
      let _,e,_,_ = s_e1.info.kappa in
      let ef = add_write x e in
      let v = constant_unit () in
      Aff (x, s_e1), (v, ef)

  | TabAcc (check, x, e) ->
      let s_e = states ren env e in
      let _,efe,_,_ = s_e.info.kappa in
      let ef = Peffect.add_read x efe in
      let _,ty = dearray_type (type_in_env env x) in
      TabAcc (check, x, s_e), (ty, ef)

  | TabAff (check, x, e1, e2) ->
      let s_e1 = states ren env e1 in
      let s_e2 = states ren env e2 in 
      let _,ef1,_,_ = s_e1.info.kappa in
      let _,ef2,_,_ = s_e2.info.kappa in
      let ef = Peffect.add_write x (Peffect.union ef1 ef2) in
      let v = constant_unit () in
      TabAff (check, x, s_e1, s_e2), (v,ef)

  | Seq bl ->
      let bl,v,ef,_ = states_block ren env bl in
      Seq bl, (v,ef)
	      
  | While(b, invopt, var, bl) ->
      let efphi,(cvar,r') = state_var ren env var in
      let ren' = next ren [] in
      let s_b = states ren' env b in
      let s_bl,_,ef_bl,_ = states_block ren' env bl in
      let cb = s_b.info.kappa in
      let efinv,inv = state_inv ren env invopt in
      let _,efb,_,_ = s_b.info.kappa in
      let ef = 
	Peffect.union (Peffect.union ef_bl efb) (Peffect.union efinv efphi)
      in
      let v = constant_unit () in
      let cvar = 
	let al = List.map (fun id -> (id,at_id id "")) (just_reads ef) in
	subst_in_constr al cvar 
      in
      While (s_b,inv,(cvar,r'),s_bl), (v,ef)
      
  | Lam ([],_) ->
      failwith "Ptyping.states: abs. should have almost one binder"

  | Lam (bl, e) ->
      let bl' = cic_binders env ren bl in
      let env' = traverse_binders env bl' in
      let ren' = initial_renaming env' in
      let s_e = states ren' env' e in
      let v = make_arrow bl' s_e.info.kappa in
      let ef = Peffect.bottom in
      Lam(bl',s_e), (v,ef)
	 
  (* Connectives AND and OR *)
  | SApp ([Variable id], [e1;e2]) ->
      let s_e1 = states ren env e1
      and s_e2 = states ren env e2 in
      let (_,ef1,_,_) = s_e1.info.kappa
      and (_,ef2,_,_) = s_e2.info.kappa in
      let ef = Peffect.union ef1 ef2 in
      SApp ([Variable id], [s_e1; s_e2]), 
      (TypePure (constant "bool"), ef)

  (* Connective NOT *)
  | SApp ([Variable id], [e]) ->
      let s_e = states ren env e in
      let (_,ef,_,_) = s_e.info.kappa in
      SApp ([Variable id], [s_e]), 
      (TypePure (constant "bool"), ef)
      
  | SApp _ -> invalid_arg "Ptyping.states (SApp)"

  (* ATTENTION:
     Si un argument réel de type ref. correspond à une ref. globale
     modifiée par la fonction alors la traduction ne sera pas correcte.
     Exemple:
            f=[x:ref Int]( r := !r+1 ; x := !x+1) modifie r et son argument x
            donc si on l'applique à r justement, elle ne modifiera que r
            mais le séquencement ne sera pas correct. *)

  | Apply (f, args) ->
      let s_f = states ren env f in
      let _,eff,_,_ = s_f.info.kappa in
      let s_args = List.map (states_arg ren env) args in
      let ef_args = 
	List.map 
	  (function Term t -> let (_,e,_,_) = t.info.kappa in e
	          | _ -> Peffect.bottom) 
	  s_args 
      in
      let _,_,((_,tapp),efapp,_,_) = effect_app ren env s_f s_args in
      let ef = 
	Peffect.compose (List.fold_left Peffect.compose eff ef_args) efapp
      in
      Apply (s_f, s_args), (tapp, ef)
      
  | LetRef (x, e1, e2) ->
      let s_e1 = states ren env e1 in
      let (_,v1),ef1,_,_ = s_e1.info.kappa in
      let env' = add (x,Ref v1) env in
      let ren' = next ren [x] in
      let s_e2 = states ren' env' e2 in
      let (_,v2),ef2,_,_ = s_e2.info.kappa in
      Perror.check_for_let_ref loc v2;
      let ef = Peffect.compose ef1 (Peffect.remove ef2 x) in
      LetRef (x, s_e1, s_e2), (v2,ef)
	
  | Let (x, e1, e2) ->
      let s_e1 = states ren env e1 in
      let (_,v1),ef1,_,_ = s_e1.info.kappa in
      Perror.check_for_not_mutable e1.loc v1;
      let env' = add (x,v1) env in
      let s_e2 = states ren env' e2 in
      let (_,v2),ef2,_,_ = s_e2.info.kappa in
      let ef = Peffect.compose ef1 ef2 in
      Let (x, s_e1, s_e2), (v2,ef)
	    
  | If (b, e1, e2) ->
      let s_b = states ren env b in
      let s_e1 = states ren env e1
      and s_e2 = states ren env e2 in
      let (_,tb),efb,_,_ = s_b.info.kappa in
      let (_,t1),ef1,_,_ = s_e1.info.kappa in
      let (_,t2),ef2,_,_ = s_e2.info.kappa in
      let ef = Peffect.compose efb (disj ef1 ef2) in
      let v = type_v_sup loc t1 t2 in
      If (s_b, s_e1, s_e2), (v,ef)

  | LetRec (f,bl,v,var,e) ->
      let bl' = cic_binders env ren bl in
      let env' = traverse_binders env bl' in
      let ren' = initial_renaming env' in
      let v' = cic_type_v env' ren' v in
      let efvar,var' = state_var ren' env' var in
      let phi0 = phi_name () in
      let tvar = typed_var ren env' var' in
      (* effect for a let/rec construct is computed as a fixpoint *)
      let rec state_rec c =
	let tf = make_arrow bl' c in
	let env'' = add_recursion (f,(phi0,tvar)) (add (f,tf) env') in
	let s_e = states ren' env'' e in
	if s_e.info.kappa = c then
	  s_e
      	else begin
	  if !verbose_fix then begin msgnl (pp_type_c s_e.info.kappa) end ;
	  state_rec s_e.info.kappa
      	end
      in 
      let s_e = state_rec ((result_id,v'),efvar,[],None) in
      let tf = make_arrow bl' s_e.info.kappa in
      LetRec (f,bl',v',var',s_e), (tf,Peffect.bottom)

  | PPoint (s,d) -> 
      let ren' = push_date ren s in
      states_desc ren' env loc d
	
  | Debug _ -> failwith "Ptyping.states: Debug: TODO"


and states_arg ren env = function
    Term a    -> let s_a = states ren env a in Term s_a
  | Refarg id -> Refarg id
  | Type v    -> let v' = cic_type_v env ren v in Type v'
	

and states ren env expr =
  (* Here we deal with the pre- and post- conditions:
   * we add their effects to the effects of the program *)
  let (d,(v,e),p1) = 
    if is_pure_desc ren env expr.desc then
      states_expression ren env expr
    else
      let (d,ve) = states_desc ren env expr.loc expr.desc in (d,ve,[])
  in
  let (ep,p) = state_pre ren env expr.pre in
  let (eq,q) = state_post ren env (result_id,v,e) expr.post in
  let e' = Peffect.union e (Peffect.union ep eq) in
  let p' = p1 @ p in
  let tinfo = { env = env; kappa = ((result_id,v),e',p',q) } in
  { desc = d;
    loc = expr.loc;
    pre = p'; post = q; (* on les conserve aussi ici pour prog_wp *)
    info = tinfo }


and states_block ren env bl =
  let rec ef_block ren tyres = function
      [] ->
	begin match tyres with
	    Some ty -> [],ty,Peffect.bottom,ren
	  | None -> failwith "a block should contain at least one statement"
	end
    | (Assert p)::block -> 
	let ep,c = state_assert ren env p in
	let bl,t,ef,ren' = ef_block ren tyres block in
	(Assert c)::bl,t,Peffect.union ep ef,ren'
    | (Label s)::block ->
	let ren' = push_date ren s in
	let bl,t,ef,ren'' = ef_block ren' tyres block in
	(Label s)::bl,t,ef,ren''
    | (Statement e)::block ->
	let s_e = states ren env e in
	let (_,t),efe,_,_ = s_e.info.kappa in
	let ren' = next ren (get_writes efe) in
	let bl,t,ef,ren'' = ef_block ren' (Some t) block in
	(Statement s_e)::bl,t,Peffect.compose efe ef,ren''
  in
  ef_block ren None bl

