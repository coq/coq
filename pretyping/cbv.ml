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
open Term
open Names
open Environ
open Univ
open Evd
open Conv_oracle
open Closure
open Esubst

(**** Call by value reduction ****)

(* The type of terms with closure. The meaning of the constructors and
 * the invariants of this datatype are the following:
 *  VAL(k,c) represents the constr c with a delayed shift of k. c must be
 *          in normal form and neutral (i.e. not a lambda, a construct or a
 *          (co)fix, because they may produce redexes by applying them,
 *          or putting them in a case)
 *  LAM(x,a,b,S) is the term [S]([x:a]b). the bindings is propagated
 *          only when the abstraction is applied, and then we use the rule
 *                  ([S]([x:a]b) c) --> [S.c]b
 *          This corresponds to the usual strategy of weak reduction
 *  FIXP(op,bd,S,args) is the fixpoint (Fix or Cofix) of bodies bd under
 *          the bindings S, and then applied to args. Here again,
 *          weak reduction.
 *  CONSTR(c,args) is the constructor [c] applied to [args].
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
  | LAM of int * (name * constr) list * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value array
  | COFIXP of cofixpoint * cbv_value subs * cbv_value array
  | CONSTR of constructor * cbv_value array

(* les vars pourraient etre des constr,
   cela permet de retarder les lift: utile ?? *) 

(* relocation of a value; used when a value stored in a context is expanded
 * in a larger context. e.g.  [%k (S.t)](k+1) --> [^k]t  (t is shifted of k)
 *)
let rec shift_value n = function
  | VAL (k,v) -> VAL ((k+n),v)
  | LAM (nlams,ctxt,b,s) -> LAM (nlams,ctxt,b,subs_shft (n,s))
  | FIXP (fix,s,args) ->
      FIXP (fix,subs_shft (n,s), Array.map (shift_value n) args)
  | COFIXP (cofix,s,args) ->
      COFIXP (cofix,subs_shft (n,s), Array.map (shift_value n) args)
  | CONSTR (c,args) ->
      CONSTR (c, Array.map (shift_value n) args)
let shift_value n v =
  if n = 0 then v else shift_value n v

(* Contracts a fixpoint: given a fixpoint and a bindings,
 * returns the corresponding fixpoint body, and the bindings in which
 * it should be evaluated: its first variables are the fixpoint bodies
 * (S, (fix Fi {F0 := T0 .. Fn-1 := Tn-1}))
 *    -> (S. [S]F0 . [S]F1 ... . [S]Fn-1, Ti)
 *)
let contract_fixp env ((reci,i),(_,_,bds as bodies)) =
  let make_body j = FIXP(((reci,j),bodies), env, [||]) in
  let n = Array.length bds in
  subs_cons(Array.init n make_body, env), bds.(i)

let contract_cofixp env (i,(_,_,bds as bodies)) =
  let make_body j = COFIXP((j,bodies), env, [||]) in
  let n = Array.length bds in
  subs_cons(Array.init n make_body, env), bds.(i)

let make_constr_ref n = function
  | RelKey p -> mkRel (n+p)
  | VarKey id -> mkVar id
  | ConstKey cst -> mkConst cst


(* type of terms with a hole. This hole can appear only under App or Case.
 *   TOP means the term is considered without context
 *   APP(v,stk) means the term is applied to v, and then the context stk
 *      (v.0 is the first argument).
 *      this corresponds to the application stack of the KAM.
 *      The members of l are values: we evaluate arguments before
        calling the function.
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
  | APP of cbv_value array * cbv_stack
  | CASE of constr * constr array * case_info * cbv_value subs * cbv_stack

(* Adds an application list. Collapse APPs! *)
let stack_app appl stack =
  if Array.length appl = 0 then stack else
    match stack with
    | APP(args,stk) -> APP(Array.append appl args,stk)
    | _             -> APP(appl, stack)


open RedFlags

let red_set_ref flags = function
  | RelKey _ -> red_set flags fDELTA
  | VarKey id -> red_set flags (fVAR id)
  | ConstKey sp -> red_set flags (fCONST sp)

(* Transfer application lists from a value to the stack
 * useful because fixpoints may be totally applied in several times
 *)
let strip_appl head stack =
  match head with
    | FIXP (fix,env,app) -> (FIXP(fix,env,[||]), stack_app app stack)
    | COFIXP (cofix,env,app) -> (COFIXP(cofix,env,[||]), stack_app app stack)
    | CONSTR (c,app) -> (CONSTR(c,[||]), stack_app app stack)
    | _ -> (head, stack)


(* Tests if fixpoint reduction is possible. *)
let fixp_reducible flgs ((reci,i),_) stk =
  if red_set flgs fIOTA then
    match stk with
      | APP(appl,_) ->
          Array.length appl > reci.(i) &&
          (match appl.(reci.(i)) with
              CONSTR _ -> true
            | _ -> false)
      | _ -> false
  else 
    false

let cofixp_reducible flgs _ stk =
  if red_set flgs fIOTA then
    match stk with
      | (CASE _ | APP(_,CASE _)) -> true
      | _ -> false
  else 
    false


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
  | App (head,args) -> (* Applied terms are normalized immediately;
                        they could be computed when getting out of the stack *)
      let nargs = Array.map (cbv_stack_term info TOP env) args in
      norm_head info env head (stack_app nargs stack)
  | Case (ci,p,c,v) -> norm_head info env c (CASE(p,v,ci,env,stack))
  | Cast (ct,_,_) -> norm_head info env ct stack

  (* constants, axioms
   * the first pattern is CRUCIAL, n=0 happens very often:
   * when reducing closed terms, n is always 0 *)
  | Rel i ->
      (match expand_rel i env with
        | Inl (0,v)      -> strip_appl v stack
        | Inl (n,v)      -> strip_appl (shift_value n v) stack
        | Inr (n,None)   -> (VAL(0, mkRel n), stack)
        | Inr (n,Some p) -> norm_head_ref (n-p) info env stack (RelKey p))

  | Var id -> norm_head_ref 0 info env stack (VarKey id)

  | Const sp -> norm_head_ref 0 info env stack (ConstKey sp)

  | LetIn (x, b, t, c) ->
      (* zeta means letin are contracted; delta without zeta means we *)
      (* allow bindings but leave let's in place *)
      let zeta = red_set (info_flags info) fZETA in
      let env' =
	if zeta 
          (* New rule: for Cbv, Delta does not apply to locally bound variables
          or red_set (info_flags info) fDELTA
          *)
        then 
	  subs_cons ([|cbv_stack_term info TOP env b|],env)
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
  | Lambda _ ->
      let ctxt,b = decompose_lam t in
      (LAM(List.length ctxt, List.rev ctxt,b,env), stack)
  | Fix fix -> (FIXP(fix,env,[||]), stack)
  | CoFix cofix -> (COFIXP(cofix,env,[||]), stack)
  | Construct c -> (CONSTR(c, [||]), stack)

  (* neutral cases *)
  | (Sort _ | Meta _ | Ind _|Evar _) -> (VAL(0, t), stack)
  | Prod (x,t,c) -> 
      (VAL(0, mkProd (x, cbv_norm_term info env t,
		      cbv_norm_term info (subs_lift env) c)),
	     stack)

and norm_head_ref k info env stack normt =
  if red_set_ref (info_flags info) normt then
    match ref_value_cache info normt with
      | Some body -> strip_appl (shift_value k body) stack
      | None -> (VAL(0,make_constr_ref k normt), stack)
  else (VAL(0,make_constr_ref k normt), stack)

(* cbv_stack_term performs weak reduction on constr t under the subs
 * env, with context stack, i.e. ([env]t stack).  First computes weak
 * head normal form of t and checks if a redex appears with the stack.
 * If so, recursive call to reach the real head normal form.  If not,
 * we build a value. 
 *)
and cbv_stack_term info stack env t =
  match norm_head info env t stack with
    (* a lambda meets an application -> BETA *)
    | (LAM (nlams,ctxt,b,env), APP (args, stk))
      when red_set (info_flags info) fBETA ->
        let nargs = Array.length args in
        if nargs == nlams then
          cbv_stack_term info stk (subs_cons(args,env)) b
        else if nlams < nargs then
          let env' = subs_cons(Array.sub args 0 nlams, env) in
          let eargs = Array.sub args nlams (nargs-nlams) in
          cbv_stack_term info (APP(eargs,stk)) env' b
        else
          let ctxt' = list_skipn nargs ctxt in
          LAM(nlams-nargs,ctxt', b, subs_cons(args,env))

    (* a Fix applied enough -> IOTA *)
    | (FIXP(fix,env,_), stk)
        when fixp_reducible (info_flags info) fix stk ->
        let (envf,redfix) = contract_fixp env fix in
        cbv_stack_term info stk envf redfix

    (* constructor guard satisfied or Cofix in a Case -> IOTA *)
    | (COFIXP(cofix,env,_), stk)
        when cofixp_reducible (info_flags info) cofix stk->
        let (envf,redfix) = contract_cofixp env cofix in
        cbv_stack_term info stk envf redfix

    (* constructor in a Case -> IOTA *)
    | (CONSTR((sp,n),_), APP(args,CASE(_,br,ci,env,stk)))
            when red_set (info_flags info) fIOTA ->
	let cargs =
          Array.sub args ci.ci_npar (Array.length args - ci.ci_npar) in
        cbv_stack_term info (stack_app cargs stk) env br.(n-1)
         
    (* constructor of arity 0 in a Case -> IOTA *)
    | (CONSTR((_,n),_), CASE(_,br,_,env,stk))
            when red_set (info_flags info) fIOTA ->
                    cbv_stack_term info stk env br.(n-1)

    (* may be reduced later by application *)  
    | (head, TOP) -> head
    | (FIXP(fix,env,_), APP(appl,TOP)) -> FIXP(fix,env,appl) 
    | (COFIXP(cofix,env,_), APP(appl,TOP)) -> COFIXP(cofix,env,appl) 
    | (CONSTR(c,_), APP(appl,TOP)) -> CONSTR(c,appl)

    (* absurd cases (ill-typed) *)
    | (LAM _, CASE _) -> assert false

    (* definitely a value *)
    | (head,stk) -> VAL(0,apply_stack info (cbv_norm_value info head) stk)


(* When we are sure t will never produce a redex with its stack, we
 * normalize (even under binders) the applied terms and we build the
 * final term
 *)
and apply_stack info t = function
  | TOP -> t
  | APP (args,st) ->
      apply_stack info (mkApp(t,Array.map (cbv_norm_value info) args)) st
  | CASE (ty,br,ci,env,st) ->
      apply_stack info
        (mkCase (ci, cbv_norm_term info env ty, t,
		    Array.map (cbv_norm_term info env) br))
        st


(* performs the reduction on a constr, and returns a constr *)
and cbv_norm_term info env t =
  (* reduction under binders *)
  cbv_norm_value info (cbv_stack_term info TOP env t)

(* reduction of a cbv_value to a constr *)
and cbv_norm_value info = function (* reduction under binders *)
  | VAL (n,v) -> lift n v
  | LAM (n,ctxt,b,env) ->
      let nctxt =
        list_map_i (fun i (x,ty) ->
          (x,cbv_norm_term info (subs_liftn i env) ty)) 0 ctxt in
      compose_lam (List.rev nctxt) (cbv_norm_term info (subs_liftn n env) b)
  | FIXP ((lij,(names,lty,bds)),env,args) ->
      mkApp
        (mkFix (lij,
		(names,
                 Array.map (cbv_norm_term info env) lty,
		 Array.map (cbv_norm_term info 
			      (subs_liftn (Array.length lty) env)) bds)),
         Array.map (cbv_norm_value info) args)
  | COFIXP ((j,(names,lty,bds)),env,args) ->
      mkApp
        (mkCoFix (j,
		  (names,Array.map (cbv_norm_term info env) lty,
		   Array.map (cbv_norm_term info 
				(subs_liftn (Array.length lty) env)) bds)),
         Array.map (cbv_norm_value info) args)
  | CONSTR (c,args) ->
      mkApp(mkConstruct c, Array.map (cbv_norm_value info) args)

(* with profiling *)
let cbv_norm infos constr =
  with_stats (lazy (cbv_norm_term infos (ESID 0) constr))


type cbv_infos = cbv_value infos

(* constant bodies are normalized at the first expansion *)
let create_cbv_infos flgs env =
  create
    (fun old_info c -> cbv_stack_term old_info TOP (ESID 0) c)
    flgs
    env
