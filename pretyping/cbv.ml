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
open Term
open Identifier
open Names
open Environ
open Instantiate
open Univ
open Evd
open Closure
open Esubst

(**** Call by value reduction ****)

(* The type of terms with closure. The meaning of the constructors and
 * the invariants of this datatype are the following:
 *  VAL(k,c) represents the constr c with a delayed shift of k. c must be
 *          in normal form and neutral (i.e. not a lambda, a construct or a
 *          (co)fix, because they may produce redexes by applying them,
 *          or putting them in a case)
 *  LAM(x,a,b,S) is the term [S]([x:a]b). the substitution is propagated
 *          only when the abstraction is applied, and then we use the rule
 *                  ([S]([x:a]b) c) --> [S.c]b
 *          This corresponds to the usual strategy of weak reduction
 *  FIXP(op,bd,S,args) is the fixpoint (Fix or Cofix) of bodies bd under
 *          the substitution S, and then applied to args. Here again,
 *          weak reduction.
 *  CONSTR(n,(sp,i),vars,args) is the n-th constructor of the i-th
 *          inductive type sp.
 *
 * Note that any term has not an equivalent in cbv_value: for example,
 * a product (x:A)B must be in normal form because only VAL may
 * represent it, and the argument of VAL is always in normal
 * form. This remark precludes coding a head reduction with these
 * functions. Anyway, does it make sense to head reduce with a
 * call-by-value strategy ?
 *)
type cbv_value =
  | VAL of int * constr
  | LAM of name * constr * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value list
  | COFIXP of cofixpoint * cbv_value subs * cbv_value list
  | CONSTR of int * inductive_path * cbv_value array * cbv_value list

(* les vars pourraient etre des constr,
   cela permet de retarder les lift: utile ?? *) 

(* relocation of a value; used when a value stored in a context is expanded
 * in a larger context. e.g.  [%k (S.t)](k+1) --> [^k]t  (t is shifted of k)
 *)
let rec shift_value n = function
  | VAL (k,v) -> VAL ((k+n),v)
  | LAM (x,a,b,s) -> LAM (x,a,b,subs_shft (n,s))
  | FIXP (fix,s,args) ->
      FIXP (fix,subs_shft (n,s), List.map (shift_value n) args)
  | COFIXP (cofix,s,args) ->
      COFIXP (cofix,subs_shft (n,s), List.map (shift_value n) args)
  | CONSTR (i,spi,vars,args) ->
      CONSTR (i, spi, Array.map (shift_value n) vars,
              List.map (shift_value n) args)
	

(* Contracts a fixpoint: given a fixpoint and a substitution,
 * returns the corresponding fixpoint body, and the substitution in which
 * it should be evaluated: its first variables are the fixpoint bodies
 * (S, (fix Fi {F0 := T0 .. Fn-1 := Tn-1}))
 *    -> (S. [S]F0 . [S]F1 ... . [S]Fn-1, Ti)
 *)
let contract_fixp env ((reci,i),(_,_,bds as bodies)) =
  let make_body j = FIXP(((reci,j),bodies), env, []) in
  let n = Array.length bds in
  let rec subst_bodies_from_i i subs =
    if i=n then subs
    else subst_bodies_from_i (i+1) (subs_cons (make_body i, subs))
  in       
  subst_bodies_from_i 0 env, bds.(i)

let contract_cofixp env (i,(_,_,bds as bodies)) =
  let make_body j = COFIXP((j,bodies), env, []) in
  let n = Array.length bds in
  let rec subst_bodies_from_i i subs =
    if i=n then subs
    else subst_bodies_from_i (i+1) (subs_cons (make_body i, subs))
  in       
  subst_bodies_from_i 0 env, bds.(i)


(* type of terms with a hole. This hole can appear only under App or Case.
 *   TOP means the term is considered without context
 *   APP(l,stk) means the term is applied to l, and then we have the context st
 *      this corresponds to the application stack of the KAM.
 *      The members of l are values: we evaluate arguments before the function.
 *   CASE(t,br,pat,S,stk) means the term is in a case (which is himself in stk
 *      t is the type of the case and br are the branches, all of them under
 *      the subs S, pat is information on the patterns of the Case
 *      (Weak reduction: we propagate the sub only when the selected branch
 *      is determined)
 *
 * Important remark: the APPs should be collapsed:
 *    (APP (l,(APP ...))) forbidden
 *)

type cbv_stack =
  | TOP
  | APP of cbv_value list * cbv_stack
  | CASE of constr * constr array * case_info * cbv_value subs * cbv_stack

(* Adds an application list. Collapse APPs! *)
let stack_app appl stack =
  match (appl, stack) with
    | ([], _)            -> stack
    | (_, APP(args,stk)) -> APP(appl@args,stk)
    | _                  -> APP(appl, stack)

(* Tests if we are in a case (modulo some applications) *)
let under_case_stack = function
  | (CASE _ | APP(_,CASE _)) -> true
  | _ -> false

(* Tells if the reduction rk is allowed by flags under a given stack.
 * The stack is useful when flags is (SIMPL,r) because in that case,
 * we perform bdi-reduction under the Case, or r-reduction otherwise
 *)
let red_allowed flags stack rk =
  if under_case_stack stack then 
    red_under flags rk
  else 
    red_top flags rk

open RedFlags

let red_allowed_ref flags stack = function
  | FarRelBinding _ -> red_allowed flags stack fDELTA
  | VarBinding id -> red_allowed flags stack (fVAR id)
  | EvarBinding _ -> red_allowed flags stack fEVAR
  | ConstBinding (sp,_) -> red_allowed flags stack (fCONST sp)

(* Transfer application lists from a value to the stack
 * useful because fixpoints may be totally applied in several times
 *)
let strip_appl head stack =
  match head with
    | FIXP (fix,env,app) -> (FIXP(fix,env,[]), stack_app app stack)
    | COFIXP (cofix,env,app) -> (COFIXP(cofix,env,[]), stack_app app stack)
    | CONSTR (i,spi,vars,app) -> (CONSTR(i,spi,vars,[]), stack_app app stack)
    | _ -> (head, stack)


(* Invariant: if the result of norm_head is CONSTR or (CO)FIXP, its last
 * argument is [].
 * Because we must put all the applied terms in the stack.
 *)
let reduce_const_body redfun v stk =
  if under_case_stack stk then strip_appl (redfun v) stk else strip_appl v stk
 

(* Tests if fixpoint reduction is possible. A reduction function is given as
   argument *)
let rec check_app_constr redfun = function
  | ([], _) -> false
  | ((CONSTR _)::_, 0) -> true
  | (t::_, 0) -> (* TODO: partager ce calcul *)
      (match redfun t with
         | CONSTR _ -> true
         | _ -> false)
  | (_::l, n) -> check_app_constr redfun (l,(pred n))
	
let fixp_reducible redfun flgs ((reci,i),_) stk =
  if red_allowed flgs stk fIOTA then
    match stk with               (* !!! for Acc_rec: reci.(i) = -2 *)
      | APP(appl,_) -> reci.(i) >=0 & check_app_constr redfun (appl, reci.(i))
      | _ -> false
  else 
    false

let cofixp_reducible redfun flgs _ stk =
  if red_allowed flgs stk fIOTA then
    match stk with
      | (CASE _ | APP(_,CASE _)) -> true
      | _ -> false
  else 
    false

let mindsp_nparams env (sp,i) =
  let mib = lookup_mind sp env in
  (Declarations.mind_nth_type_packet mib i).Declarations.mind_nparams

(* The main recursive functions
 *
 * Go under applications and cases (pushed in the stack), expand head
 * constants or substitued de Bruijn, and try to make appear a
 * constructor, a lambda or a fixp in the head. If not, it is a value
 * and is completely computed here. The head redexes are NOT reduced:
 * the function returns the pair of a cbv_value and its stack.  *
 * Invariant: if the result of norm_head is CONSTR or (CO)FIXP, it last
 * argument is [].  Because we must put all the applied terms in the
 * stack. *)

let rec norm_head info env t stack =
  (* no reduction under binders *)
  match kind_of_term t with
  (* stack grows (remove casts) *)
  | IsApp (head,args) -> (* Applied terms are normalized immediately;
                        they could be computed when getting out of the stack *)
      let nargs = Array.map (cbv_stack_term info TOP env) args in
      norm_head info env head (stack_app (Array.to_list nargs) stack)
  | IsMutCase (ci,p,c,v) -> norm_head info env c (CASE(p,v,ci,env,stack))
  | IsCast (ct,_) -> norm_head info env ct stack

  (* constants, axioms
   * the first pattern is CRUCIAL, n=0 happens very often:
   * when reducing closed terms, n is always 0 *)
  | IsRel i -> (match expand_rel i env with
                | Inl (0,v) ->
                    reduce_const_body (cbv_norm_more info env) v stack
                | Inl (n,v) ->
                    reduce_const_body
                      (cbv_norm_more info env) (shift_value n v) stack
                | Inr (n,None) ->
		    (VAL(0, mkRel n), stack)
                | Inr (n,Some p) ->
		    norm_head_ref (n-p) info env stack (FarRelBinding p))

  | IsVar id -> norm_head_ref 0 info env stack (VarBinding id)

  | IsConst (sp,vars) ->
      let normt = (sp,Array.map (cbv_norm_term info env) vars) in
      norm_head_ref 0 info env stack (ConstBinding normt)

  | IsEvar ev -> norm_head_ref 0 info env stack (EvarBinding (ev,env))

  | IsLetIn (x, b, t, c) ->
      (* zeta means letin are contracted; delta without zeta means we *)
      (* allow substitution but leave let's in place *)
      let zeta = red_allowed (info_flags info) stack fZETA in
      let env' =
	if zeta or red_allowed (info_flags info) stack fDELTA then 
	  subs_cons (cbv_stack_term info TOP env b,env)
	else
	  subs_lift env in
      if zeta then
        norm_head info env' c stack
      else
	let normt =
	  mkLetIn (x, cbv_norm_term info env b,
		   cbv_norm_term info env t,
		   cbv_norm_term info env' c) in
	(VAL(0,normt), stack) (* Considérer une coupure commutative ? *)

  (* non-neutral cases *)
  | IsLambda (x,a,b) -> (LAM(x,a,b,env), stack)
  | IsFix fix -> (FIXP(fix,env,[]), stack)
  | IsCoFix cofix -> (COFIXP(cofix,env,[]), stack)
  | IsMutConstruct ((spi,i),vars) ->
      (CONSTR(i,spi, Array.map (cbv_stack_term info TOP env) vars,[]), stack)

  (* neutral cases *)
  | (IsSort _ | IsMeta _) -> (VAL(0, t), stack)
  | IsMutInd (sp,vars) -> 
      (VAL(0, mkMutInd (sp, Array.map (cbv_norm_term info env) vars)), stack)
  | IsProd (x,t,c) -> 
      (VAL(0, mkProd (x, cbv_norm_term info env t,
		      cbv_norm_term info (subs_lift env) c)),
	     stack)

and norm_head_ref k info env stack normt =
  if red_allowed_ref (info_flags info) stack normt then
    match ref_value_cache info normt with
      | Some body ->
	  reduce_const_body (cbv_norm_more info env) (shift_value k body) stack
      | None -> (VAL(0,make_constr_ref k info normt), stack)
  else (VAL(0,make_constr_ref k info normt), stack)

and make_constr_ref n info = function
  | FarRelBinding p -> mkRel (n+p)
  | VarBinding id -> mkVar id
  | EvarBinding ((ev,args),env) ->
      mkEvar (ev,Array.map (cbv_norm_term info env) args)
  | ConstBinding cst -> mkConst cst

(* cbv_stack_term performs weak reduction on constr t under the subs
 * env, with context stack, i.e. ([env]t stack).  First computes weak
 * head normal form of t and checks if a redex appears with the stack.
 * If so, recursive call to reach the real head normal form.  If not,
 * we build a value. 
 *)
and cbv_stack_term info stack env t =
  match norm_head info env t stack with
    (* a lambda meets an application -> BETA *)
    | (LAM (x,a,b,env), APP (arg::args, stk))
      when red_allowed (info_flags info) stk fBETA ->
        let subs = subs_cons (arg,env) in
          cbv_stack_term info (stack_app args stk) subs b

    (* a Fix applied enough -> IOTA *)
    | (FIXP(fix,env,_), stk)
        when fixp_reducible (cbv_norm_more info env) (info_flags info) fix stk ->
        let (envf,redfix) = contract_fixp env fix in
        cbv_stack_term info stk envf redfix

    (* constructor guard satisfied or Cofix in a Case -> IOTA *)
    | (COFIXP(cofix,env,_), stk)
        when cofixp_reducible (cbv_norm_more info env) (info_flags info) cofix stk->
        let (envf,redfix) = contract_cofixp env cofix in
        cbv_stack_term info stk envf redfix

    (* constructor in a Case -> IOTA
       (use red_under because we know there is a Case) *)
    | (CONSTR(n,sp,_,_), APP(args,CASE(_,br,(arity,_),env,stk)))
            when red_under (info_flags info) fIOTA ->
(*
	let ncargs = arity.(n-1) in
	let real_args = list_lastn ncargs args in
*)
	let real_args = snd (list_chop arity args) in
        cbv_stack_term info (stack_app real_args stk) env br.(n-1)
         
    (* constructor of arity 0 in a Case -> IOTA ( "   " )*)
    | (CONSTR(n,_,_,_), CASE(_,br,_,env,stk))
                  when red_under (info_flags info) fIOTA ->
                    cbv_stack_term info stk env br.(n-1)

    (* may be reduced later by application *)  
    | (head, TOP) -> head
    | (FIXP(fix,env,_), APP(appl,TOP)) -> FIXP(fix,env,appl) 
    | (COFIXP(cofix,env,_), APP(appl,TOP)) -> COFIXP(cofix,env,appl) 
    | (CONSTR(n,spi,vars,_), APP(appl,TOP)) -> CONSTR(n,spi,vars,appl)

    (* definitely a value *)
    | (head,stk) -> VAL(0,apply_stack info (cbv_norm_value info head) stk)


(* if we are in SIMPL mode, maybe v isn't reduced enough *)
and cbv_norm_more info env v =
  match (v, (info_flags info)) with
    | (VAL(k,t), ((SIMPL|WITHBACK),_)) ->
        cbv_stack_term (infos_under info) TOP (subs_shft (k,env)) t
    | _ -> v


(* When we are sure t will never produce a redex with its stack, we
 * normalize (even under binders) the applied terms and we build the
 * final term
 *)
and apply_stack info t = function
  | TOP -> t
  | APP (args,st) ->
      apply_stack info (applistc t (List.map (cbv_norm_value info) args)) st
  | CASE (ty,br,ci,env,st) ->
      apply_stack info
        (mkMutCase (ci, cbv_norm_term info env ty, t,
		    Array.map (cbv_norm_term info env) br))
        st


(* performs the reduction on a constr, and returns a constr *)
and cbv_norm_term info env t =
  (* reduction under binders *)
  cbv_norm_value info (cbv_stack_term info TOP env t)

(* reduction of a cbv_value to a constr *)
and cbv_norm_value info = function (* reduction under binders *)
  | VAL (n,v) -> lift n v
  | LAM (x,a,b,env) ->
      mkLambda (x, cbv_norm_term info env a,
		cbv_norm_term info (subs_lift env) b)
  | FIXP ((lij,(names,lty,bds)),env,args) ->
      applistc
        (mkFix (lij,
		(names,
                 Array.map (cbv_norm_term info env) lty,
		 Array.map (cbv_norm_term info 
			      (subs_liftn (Array.length lty) env)) bds)))
        (List.map (cbv_norm_value info) args)
  | COFIXP ((j,(names,lty,bds)),env,args) ->
      applistc
        (mkCoFix (j,
		  (names,Array.map (cbv_norm_term info env) lty,
		   Array.map (cbv_norm_term info 
				(subs_liftn (Array.length lty) env)) bds)))
        (List.map (cbv_norm_value info) args)
  | CONSTR (n,spi,vars,args) ->
      applistc
        (mkMutConstruct ((spi,n), Array.map (cbv_norm_value info) vars))
        (List.map (cbv_norm_value info) args)

(* with profiling *)
let cbv_norm infos constr =
  with_stats (lazy (cbv_norm_term infos (ESID 0) constr))


type 'a cbv_infos = (cbv_value, 'a) infos

(* constant bodies are normalized at the first expansion *)
let create_cbv_infos flgs env sigma =
  create
    (fun old_info s c -> cbv_stack_term old_info TOP s c)
    flgs
    env
    sigma
