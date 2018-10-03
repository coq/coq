(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Vars
open CClosure
open Esubst

(**** Call by value reduction ****)

(* The type of terms with closure. The meaning of the constructors and
 * the invariants of this datatype are the following:
 *  VAL(k,c) represents the constr c with a delayed shift of k. c must be
 *          in normal form and neutral (i.e. not a lambda, a construct or a
 *          (co)fix, because they may produce redexes by applying them,
 *          or putting them in a case)
 *  STACK(k,v,stk) represents an irreductible value [v] in the stack [stk].
 *          [k] is a delayed shift to be applied to both the value and
 *          the stack.
 *  CBN(t,S) is the term [S]t. It is used to delay evaluation. For
 *          instance products are evaluated only when actually needed
 *          (CBN strategy).
 *  LAM(n,a,b,S) is the term [S]([x:a]b) where [a] is a list of bindings and
 *          [n] is the length of [a]. the environment [S] is propagated
 *          only when the abstraction is applied, and then we use the rule
 *                  ([S]([x:a]b) c) --> [S.c]b
 *          This corresponds to the usual strategy of weak reduction
 *  FIXP(op,bd,S,args) is the fixpoint (Fix or Cofix) of bodies bd under
 *          the bindings S, and then applied to args. Here again,
 *          weak reduction.
 *  CONSTR(c,args) is the constructor [c] applied to [args].
 *
 *)
type cbv_value =
  | VAL of int * constr
  | STACK of int * cbv_value * cbv_stack
  | CBN of constr * cbv_value subs
  | LAM of int * (Name.t * constr) list * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value array
  | COFIXP of cofixpoint * cbv_value subs * cbv_value array
  | CONSTR of constructor Univ.puniverses * cbv_value array

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
 *   PROJ(p,pb,stk) means the term is in a primitive projection p, itself in stk.
 *      pb is the associated projection body
 *
 * Important remark: the APPs should be collapsed:
 *    (APP (l,(APP ...))) forbidden
 *)
and cbv_stack =
  | TOP
  | APP of cbv_value array * cbv_stack
  | CASE of constr * constr array * case_info * cbv_value subs * cbv_stack
  | PROJ of Projection.t * cbv_stack

(* les vars pourraient etre des constr,
   cela permet de retarder les lift: utile ?? *)

(* relocation of a value; used when a value stored in a context is expanded
 * in a larger context. e.g.  [%k (S.t)](k+1) --> [^k]t  (t is shifted of k)
 *)
let rec shift_value n = function
  | VAL (k,t) -> VAL (k+n,t)
  | STACK(k,v,stk) -> STACK(k+n,v,stk)
  | CBN (t,s) -> CBN(t,subs_shft(n,s))
  | LAM (nlams,ctxt,b,s) -> LAM (nlams,ctxt,b,subs_shft (n,s))
  | FIXP (fix,s,args) ->
      FIXP (fix,subs_shft (n,s), Array.map (shift_value n) args)
  | COFIXP (cofix,s,args) ->
      COFIXP (cofix,subs_shft (n,s), Array.map (shift_value n) args)
  | CONSTR (c,args) ->
      CONSTR (c, Array.map (shift_value n) args)
let shift_value n v =
  if Int.equal n 0 then v else shift_value n v

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
  | ConstKey cst -> mkConstU cst

(* Adds an application list. Collapse APPs! *)
let stack_app appl stack =
  if Int.equal (Array.length appl) 0 then stack else
    match stack with
    | APP(args,stk) -> APP(Array.append appl args,stk)
    | _             -> APP(appl, stack)

let rec stack_concat stk1 stk2 =
  match stk1 with
      TOP -> stk2
    | APP(v,stk1') -> APP(v,stack_concat stk1' stk2)
    | CASE(c,b,i,s,stk1') -> CASE(c,b,i,s,stack_concat stk1' stk2)
    | PROJ (p,stk1') -> PROJ (p,stack_concat stk1' stk2)

(* merge stacks when there is no shifts in between *)
let mkSTACK = function
    v, TOP -> v
  | STACK(0,v0,stk0), stk -> STACK(0,v0,stack_concat stk0 stk)
  | v,stk -> STACK(0,v,stk)

type cbv_infos = { tab : cbv_value infos_tab; infos : cbv_value infos; sigma : Evd.evar_map }

(* Change: zeta reduction cannot be avoided in CBV *)

open RedFlags

let red_set_ref flags = function
  | RelKey _ -> red_set flags fDELTA
  | VarKey id -> red_set flags (fVAR id)
  | ConstKey (sp,_) -> red_set flags (fCONST sp)

(* Transfer application lists from a value to the stack
 * useful because fixpoints may be totally applied in several times.
 * On the other hand, irreductible atoms absorb the full stack.
 *)
let strip_appl head stack =
  match head with
    | FIXP (fix,env,app) -> (FIXP(fix,env,[||]), stack_app app stack)
    | COFIXP (cofix,env,app) -> (COFIXP(cofix,env,[||]), stack_app app stack)
    | CONSTR (c,app) -> (CONSTR(c,[||]), stack_app app stack)
    | _ -> (head, stack)


(* Tests if fixpoint reduction is possible. *)
let fixp_reducible flgs ((reci,i),_) stk =
  if red_set flgs fFIX then
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
  if red_set flgs fCOFIX then
    match stk with
      | (CASE _ | PROJ _ | APP(_,CASE _) | APP(_,PROJ _)) -> true
      | _ -> false
  else
    false

let debug_cbv = ref false
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "cbv visited constants display";
  Goptions.optkey = ["Debug";"Cbv"];
  Goptions.optread = (fun () -> !debug_cbv);
  Goptions.optwrite = (fun a -> debug_cbv:=a);
}

let debug_pr_key = function
  | ConstKey (sp,_) -> Names.Constant.print sp
  | VarKey id -> Names.Id.print id
  | RelKey n -> Pp.(str "REL_" ++ int n)

let rec reify_stack t = function
  | TOP -> t
  | APP (args,st) ->
      reify_stack (mkApp(t,Array.map reify_value args)) st
  | CASE (ty,br,ci,env,st) ->
      reify_stack
        (mkCase (ci, ty, t,br))
        st
  | PROJ (p, st) ->
       reify_stack (mkProj (p, t)) st

and reify_value = function (* reduction under binders *)
  | VAL (n,t) -> lift n t
  | STACK (0,v,stk) ->
      reify_stack (reify_value v) stk
  | STACK (n,v,stk) ->
      lift n (reify_stack (reify_value v) stk)
  | CBN(t,env) ->
    apply_env env t
  | LAM (k,ctxt,b,env) ->
    apply_env env @@
    List.fold_left (fun c (n,t) ->
        mkLambda (n, t, c)) b ctxt
  | FIXP ((lij,(names,lty,bds)),env,args) ->
    let fix = mkFix (lij, (names, lty, bds)) in
    mkApp (apply_env env fix, Array.map reify_value args)
  | COFIXP ((j,(names,lty,bds)),env,args) ->
    let cofix = mkCoFix (j, (names,lty,bds)) in
    mkApp (apply_env env cofix, Array.map reify_value args)
  | CONSTR (c,args) ->
      mkApp(mkConstructU c, Array.map reify_value args)

and apply_env env t =
  match kind t with
  | Rel i ->
    begin match expand_rel i env with
      | Inl (k, v) ->
        reify_value (shift_value k v)
      | Inr (k,_) ->
        mkRel k
    end
  | _ ->
    map_with_binders subs_lift apply_env env t

(* The main recursive functions
 *
 * Go under applications and cases/projections (pushed in the stack), 
 * expand head constants or substitued de Bruijn, and try to a make a
 * constructor, a lambda or a fixp appear in the head. If not, it is a value
 * and is completely computed here. The head redexes are NOT reduced:
 * the function returns the pair of a cbv_value and its stack.  *
 * Invariant: if the result of norm_head is CONSTR or (CO)FIXP, it last
 * argument is [].  Because we must put all the applied terms in the
 * stack. *)

let rec norm_head info env t stack =
  (* no reduction under binders *)
  match kind t with
  (* stack grows (remove casts) *)
  | App (head,args) -> (* Applied terms are normalized immediately;
                        they could be computed when getting out of the stack *)
      let nargs = Array.map (cbv_stack_term info TOP env) args in
      norm_head info env head (stack_app nargs stack)
  | Case (ci,p,c,v) -> norm_head info env c (CASE(p,v,ci,env,stack))
  | Cast (ct,_,_) -> norm_head info env ct stack
  
  | Proj (p, c) -> 
    let p' =
      if red_set (info_flags info.infos) (fCONST (Projection.constant p)) 
      	&& red_set (info_flags info.infos) fBETA 
      then Projection.unfold p
      else p
    in 
      norm_head info env c (PROJ (p', stack))
	
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

  | Const sp ->
    Reductionops.reduction_effect_hook (env_of_infos info.infos) info.sigma
      (fst sp) (lazy (reify_stack t stack));
    norm_head_ref 0 info env stack (ConstKey sp)

  | LetIn (_, b, _, c) ->
      (* zeta means letin are contracted; delta without zeta means we *)
      (* allow bindings but leave let's in place *)
      if red_set (info_flags info.infos) fZETA then
        (* New rule: for Cbv, Delta does not apply to locally bound variables
           or red_set (info_flags info.infos) fDELTA
         *)
	let env' = subs_cons ([|cbv_stack_term info TOP env b|],env) in
        norm_head info env' c stack
      else
	(CBN(t,env), stack) (* Should we consider a commutative cut ? *)

  | Evar ev ->
      (match evar_value info.infos.i_cache ev with
          Some c -> norm_head info env c stack
        | None ->
          let e, xs = ev in
          let xs' = Array.map (apply_env env) xs in
          (VAL(0, mkEvar (e,xs')), stack))

  (* non-neutral cases *)
  | Lambda _ ->
      let ctxt,b = Term.decompose_lam t in
      (LAM(List.length ctxt, List.rev ctxt,b,env), stack)
  | Fix fix -> (FIXP(fix,env,[||]), stack)
  | CoFix cofix -> (COFIXP(cofix,env,[||]), stack)
  | Construct c -> (CONSTR(c, [||]), stack)

  (* neutral cases *)
  | (Sort _ | Meta _ | Ind _) -> (VAL(0, t), stack)
  | Prod _ -> (CBN(t,env), stack)

and norm_head_ref k info env stack normt =
  if red_set_ref (info_flags info.infos) normt then
    match ref_value_cache info.infos info.tab normt with
      | Some body ->
         if !debug_cbv then Feedback.msg_debug Pp.(str "Unfolding " ++ debug_pr_key normt);
         strip_appl (shift_value k body) stack
      | None ->
         if !debug_cbv then Feedback.msg_debug Pp.(str "Not unfolding " ++ debug_pr_key normt);
         (VAL(0,make_constr_ref k normt),stack)
  else
    begin
      if !debug_cbv then Feedback.msg_debug Pp.(str "Not unfolding " ++ debug_pr_key normt);
      (VAL(0,make_constr_ref k normt),stack)
    end

(* cbv_stack_term performs weak reduction on constr t under the subs
 * env, with context stack, i.e. ([env]t stack).  First computes weak
 * head normal form of t and checks if a redex appears with the stack.
 * If so, recursive call to reach the real head normal form.  If not,
 * we build a value.
 *)
and cbv_stack_term info stack env t =
  cbv_stack_value info env (norm_head info env t stack)

and cbv_stack_value info env = function
  (* a lambda meets an application -> BETA *)
  | (LAM (nlams,ctxt,b,env), APP (args, stk))
      when red_set (info_flags info.infos) fBETA ->
    let nargs = Array.length args in
      if nargs == nlams then
          cbv_stack_term info stk (subs_cons(args,env)) b
        else if nlams < nargs then
          let env' = subs_cons(Array.sub args 0 nlams, env) in
          let eargs = Array.sub args nlams (nargs-nlams) in
          cbv_stack_term info (APP(eargs,stk)) env' b
        else
          let ctxt' = List.skipn nargs ctxt in
          LAM(nlams-nargs,ctxt', b, subs_cons(args,env))

    (* a Fix applied enough -> IOTA *)
    | (FIXP(fix,env,[||]), stk)
        when fixp_reducible (info_flags info.infos) fix stk ->
        let (envf,redfix) = contract_fixp env fix in
        cbv_stack_term info stk envf redfix

    (* constructor guard satisfied or Cofix in a Case -> IOTA *)
    | (COFIXP(cofix,env,[||]), stk)
        when cofixp_reducible (info_flags info.infos) cofix stk->
        let (envf,redfix) = contract_cofixp env cofix in
        cbv_stack_term info stk envf redfix

    (* constructor in a Case -> IOTA *)
    | (CONSTR(((sp,n),u),[||]), APP(args,CASE(_,br,ci,env,stk)))
            when red_set (info_flags info.infos) fMATCH ->
	let cargs =
          Array.sub args ci.ci_npar (Array.length args - ci.ci_npar) in
        cbv_stack_term info (stack_app cargs stk) env br.(n-1)

    (* constructor of arity 0 in a Case -> IOTA *)
    | (CONSTR(((_,n),u),[||]), CASE(_,br,_,env,stk))
            when red_set (info_flags info.infos) fMATCH ->
                    cbv_stack_term info stk env br.(n-1)

    (* constructor in a Projection -> IOTA *)
    | (CONSTR(((sp,n),u),[||]), APP(args,PROJ(p,stk)))
        when red_set (info_flags info.infos) fMATCH && Projection.unfolded p ->
      let arg = args.(Projection.npars p + Projection.arg p) in
	cbv_stack_value info env (strip_appl arg stk)

    (* may be reduced later by application *)
    | (FIXP(fix,env,[||]), APP(appl,TOP)) -> FIXP(fix,env,appl)
    | (COFIXP(cofix,env,[||]), APP(appl,TOP)) -> COFIXP(cofix,env,appl)
    | (CONSTR(c,[||]), APP(appl,TOP)) -> CONSTR(c,appl)

    (* definitely a value *)
    | (head,stk) -> mkSTACK(head, stk)


(* When we are sure t will never produce a redex with its stack, we
 * normalize (even under binders) the applied terms and we build the
 * final term
 *)
let rec apply_stack info t = function
  | TOP -> t
  | APP (args,st) ->
      apply_stack info (mkApp(t,Array.map (cbv_norm_value info) args)) st
  | CASE (ty,br,ci,env,st) ->
      apply_stack info
        (mkCase (ci, cbv_norm_term info env ty, t,
		    Array.map (cbv_norm_term info env) br))
        st
  | PROJ (p, st) ->
       apply_stack info (mkProj (p, t)) st

(* performs the reduction on a constr, and returns a constr *)
and cbv_norm_term info env t =
  (* reduction under binders *)
  cbv_norm_value info (cbv_stack_term info TOP env t)

(* reduction of a cbv_value to a constr *)
and cbv_norm_value info = function (* reduction under binders *)
  | VAL (n,t) -> lift n t
  | STACK (0,v,stk) ->
      apply_stack info (cbv_norm_value info v) stk
  | STACK (n,v,stk) ->
      lift n (apply_stack info (cbv_norm_value info v) stk)
  | CBN(t,env) ->
      Constr.map_with_binders subs_lift (cbv_norm_term info) env t
  | LAM (n,ctxt,b,env) ->
      let nctxt =
        List.map_i (fun i (x,ty) ->
          (x,cbv_norm_term info (subs_liftn i env) ty)) 0 ctxt in
      Term.compose_lam (List.rev nctxt) (cbv_norm_term info (subs_liftn n env) b)
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
      mkApp(mkConstructU c, Array.map (cbv_norm_value info) args)

(* with profiling *)
let cbv_norm infos constr =
  let constr = EConstr.Unsafe.to_constr constr in
  EConstr.of_constr (with_stats (lazy (cbv_norm_term infos (subs_id 0) constr)))

(* constant bodies are normalized at the first expansion *)
let create_cbv_infos flgs env sigma =
  let infos = create
    ~share:true (** Not used by cbv *)
    ~repr:(fun old_info tab c -> cbv_stack_term { tab; infos = old_info; sigma } TOP (subs_id 0) c)
    flgs
    env
    (Reductionops.safe_evar_value sigma) in
  { tab = CClosure.create_tab (); infos; sigma }
