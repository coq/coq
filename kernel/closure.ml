
(* $Id$ *)

open Util
open Pp
open Term
open Names
open Environ
open Instantiate
open Univ
open Evd

let stats = ref false
let share = ref true

(* Profiling *)
let beta = ref 0
let delta = ref 0
let zeta = ref 0
let evar = ref 0
let iota = ref 0
let prune = ref 0

let reset () =
  beta := 0; delta := 0; zeta := 0; evar := 0; iota := 0; prune := 0

let stop() =
  mSGNL [< 'sTR"[Reds: beta=";'iNT !beta; 'sTR" delta="; 'iNT !delta;
	   'sTR" zeta="; 'iNT !zeta; 'sTR" evar="; 'iNT !evar;
           'sTR" iota="; 'iNT !iota; 'sTR" prune="; 'iNT !prune; 'sTR"]" >]


(* [r_const=(true,cl)] means all constants but those in [cl] *)
(* [r_const=(false,cl)] means only those in [cl] *)
type reds = {
  r_beta : bool;
  r_const : bool * section_path list;
  r_zeta : bool;
  r_evar : bool;
  r_iota : bool }

let betadeltaiota_red = {
  r_beta = true;
  r_const = true,[];
  r_zeta = true;
  r_evar = true;
  r_iota = true } 

let betaiota_red = {
  r_beta = true;
  r_const = false,[];
  r_zeta = false;
  r_evar = false;
  r_iota = true }
		     
let beta_red = {
  r_beta = true;
  r_const = false,[];
  r_zeta = false;
  r_evar = false;
  r_iota = false }

let no_red = {
  r_beta = false;
  r_const = false,[];
  r_zeta = false;
  r_evar = false;
  r_iota = false }

let betaiotazeta_red = {
  r_beta = true;
  r_const = false,[];
  r_zeta = true;
  r_evar = false;
  r_iota = true }

let unfold_red sp = {
  r_beta = true;
  r_const = false,[sp];
  r_zeta = false;
  r_evar = false;
  r_iota = true }

(* Sets of reduction kinds.
   Main rule: delta implies all consts (both global (= by
   section_path) and local (= by Rel or Var)), all evars, and zeta (= letin's).
   Rem: reduction of a Rel/Var bound to a term is Delta, but reduction of 
   a LetIn expression is Letin reduction *)

type red_kind =
    BETA | DELTA | ZETA | EVAR | IOTA
  | CONST of section_path list | CONSTBUT of section_path list

let rec red_add red = function
  | BETA -> { red with r_beta = true }
  | DELTA ->
      if snd red.r_const <> [] then error "Conflict in the reduction flags";
      { red with r_const = true,[]; r_zeta = true; r_evar = true }
  | CONST cl ->
      if fst red.r_const then error "Conflict in the reduction flags";
      { red with r_const = false, list_union cl (snd red.r_const) }
  | CONSTBUT cl ->
      if not (fst red.r_const) & snd red.r_const <> [] then
	error "Conflict in the reduction flags";
      { red with r_const = true, list_union cl (snd red.r_const);
	  r_zeta = true; r_evar = true }
  | IOTA -> { red with r_iota = true }
  | EVAR -> { red with r_evar = true }
  | ZETA -> { red with r_zeta = true }

let incr_cnt red cnt =
  if red then begin
    if !stats then incr cnt;
    true
  end else 
    false

let red_local_const red = fst red.r_const

(* to know if a redex is allowed, only a subset of red_kind is used ... *)
let red_set red = function
  | BETA -> incr_cnt red.r_beta beta
  | CONST [sp] -> 
      let (b,l) = red.r_const in
      let c = List.mem sp l in
      incr_cnt ((b & not c) or (c & not b)) delta
  | ZETA -> incr_cnt red.r_zeta zeta
  | EVAR -> incr_cnt red.r_zeta evar
  | IOTA -> incr_cnt red.r_iota iota
  | DELTA -> fst red.r_const  (* Used for Rel/Var defined in context *)
  (* Not for internal use *)
  | CONST _ | CONSTBUT _ -> failwith "not implemented"

(* specification of the reduction function *)

type red_mode = UNIFORM | SIMPL | WITHBACK

type flags = red_mode * reds

(* (UNIFORM,r)  == r-reduce in any context
 * (SIMPL,r)    == bdi-reduce under cases or fix, r otherwise (like hnf does)
 * (WITHBACK,r) == internal use: means we are under a case or in rec. arg. of
 *                 fix
 *)

(* Examples *)
let no_flag = (UNIFORM,no_red)
let beta = (UNIFORM,beta_red)
let betaiota = (UNIFORM,betaiota_red)
let betadeltaiota = (UNIFORM,betadeltaiota_red)

let hnf_flags = (SIMPL,betaiotazeta_red)
let unfold_flags sp = (UNIFORM, unfold_red sp)

let flags_under = function
  | (SIMPL,r) -> (WITHBACK,r)
  | fl -> fl


(* Reductions allowed in "normal" circumstances: reduce only what is
 * specified by r *)

let red_top (_,r) rk = red_set r rk

(* Sometimes, we may want to perform a bdi reduction, to generate new redexes.
 * Typically: in the Simpl reduction, terms in recursive position of a fixpoint
 * are bdi-reduced, even if r is weaker.
 *
 * It is important to keep in mind that when we talk of "normal" or
 * "head normal" forms, it always refer to the reduction specified by r,
 * whatever the term context. *)

let red_under (md,r) rk =
  match md with
    | WITHBACK -> true
    | _ -> red_set r rk

(* (bounded) explicit substitutions of type 'a *)
type 'a subs =
  | ESID of int            (* ESID(n)    = %n END   bounded identity *)
  | CONS of 'a * 'a subs   (* CONS(t,S)  = (S.t)    parallel substitution *)
  | SHIFT of int * 'a subs (* SHIFT(n,S) = (^n o S) terms in S are relocated *)
                           (*                        with n vars *)
  | LIFT of int * 'a subs  (* LIFT(n,S) = (%n S) stands for ((^n o S).n...1) *)

(* operations of subs: collapses constructors when possible.
 * Needn't be recursive if we always use these functions
 *)

let subs_cons(x,s) = CONS(x,s)

let subs_liftn n = function
  | ESID p -> ESID (p+n) (* bounded identity lifted extends by p *)
  | LIFT (p,lenv) -> LIFT (p+n, lenv)
  | lenv -> LIFT (n,lenv)

let subs_lift a = subs_liftn 1 a

let subs_shft = function
  | (0, s)            -> s
  | (n, SHIFT (k,s1)) -> SHIFT (k+n, s1)
  | (n, s)            -> SHIFT (n,s)

(* Expands de Bruijn k in the explicit substitution subs
 * lams accumulates de shifts to perform when retrieving the i-th value
 * the rules used are the following:
 *
 *    [id]k       --> k
 *    [S.t]1      --> t
 *    [S.t]k      --> [S](k-1)  if k > 1
 *    [^n o S] k  --> [^n]([S]k)
 *    [(%n S)] k  --> k         if k <= n
 *    [(%n S)] k  --> [^n]([S](k-n))
 *
 * the result is (Inr (k+lams,p)) when the variable is just relocated
 * where p is None if the variable points insider subs and Some(k) if the
 * variable points k bindings beyond subs.
 *) 
let rec exp_rel lams k subs =
  match (k,subs) with
    | (1, CONS (def,_)) -> Inl(lams,def)
    | (_, CONS (_,l)) -> exp_rel lams (pred k) l
    | (_, LIFT (n,_)) when k<=n -> Inr(lams+k,None)
    | (_, LIFT (n,l)) -> exp_rel (n+lams) (k-n) l
    | (_, SHIFT (n,s)) -> exp_rel (n+lams) k s
    | (_, ESID n) when k<=n -> Inr(lams+k,None)
    | (_, ESID n) -> Inr(lams+k,Some (k-n))

let expand_rel k subs = exp_rel 0 k subs

(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
 *  * i_evc is the set of constraints for existential variables
 *  * i_tab is the cache table of the results
 *  * i_repr is the function to get the representation from the current
 *         state of the cache and the body of the constant. The result
 *         is stored in the table.
 *  * i_rels = (4,[(1,c);(3,d)]) means there are 4 free rel variables
 *    and only those with index 1 and 3 have bodies which are c and d resp.
 *  * i_vars is the list of _defined_ named variables.
 *
 * ref_value_cache searchs in the tab, otherwise uses i_repr to
 * compute the result and store it in the table. If the constant can't
 * be unfolded, returns None, but does not store this failure.  * This
 * doesn't take the RESET into account. You mustn't keep such a table
 * after a Reset.  * This type is not exported. Only its two
 * instantiations (cbv or lazy) are.
 *)

type 'a table_key =
  | ConstBinding of constant
  | EvarBinding of (existential * 'a subs)
  | VarBinding of identifier
  | FarRelBinding of int

type ('a, 'b) infos = {
  i_flags : flags;
  i_repr : ('a, 'b) infos -> 'a subs -> constr -> 'a;
  i_env : env;
  i_evc : 'b evar_map;
  i_rels : int * (int * constr) list;
  i_vars : (identifier * constr) list;
  i_tab : ('a table_key, 'a) Hashtbl.t }

let ref_value_cache info ref =
  try  
    Some (Hashtbl.find info.i_tab ref)
  with Not_found ->
  try
    let body,subs =
      match ref with
	| FarRelBinding n ->
	    let (s,l) = info.i_rels in lift n (List.assoc (s-n) l), ESID 0
	| VarBinding id -> List.assoc id info.i_vars, ESID 0
	| EvarBinding (evc,subs) -> existential_value info.i_evc evc, subs
	| ConstBinding cst -> constant_value info.i_env cst, ESID 0
    in
    let v = info.i_repr info subs body in
    Hashtbl.add info.i_tab ref v;
    Some v
  with
    | Not_found (* List.assoc *)
    | NotInstantiatedEvar (* Evar *)
    | NotEvaluableConst _ (* Const *)
      -> None

let defined_vars flags env =
  if red_local_const (snd flags) then
    fold_named_context 
      (fun env (id,b,t) e ->
	 match b with
	   | None -> e
	   | Some body -> (id, body)::e)
      env []
  else []

let defined_rels flags env =
  if red_local_const (snd flags) then
  fold_rel_context 
      (fun env (id,b,t) (i,subs) ->
	 match b with
	   | None -> (i+1, subs)
	   | Some body -> (i+1, (i,body) :: subs))
      env (0,[])
  else (0,[])

let infos_under infos = { infos with i_flags = flags_under infos.i_flags }


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
  | CONSTR of int * (section_path * int) * cbv_value array * cbv_value list

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

type stack =
  | TOP
  | APP of cbv_value list * stack
  | CASE of constr * constr array * case_info * cbv_value subs * stack

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

let red_allowed_ref flags stack = function
  | FarRelBinding _ | VarBinding _ -> red_allowed flags stack DELTA
  | EvarBinding _ -> red_allowed flags stack EVAR
  | ConstBinding (sp,_) -> red_allowed flags stack (CONST [sp])

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
  if red_allowed flgs stk IOTA then
    match stk with               (* !!! for Acc_rec: reci.(i) = -2 *)
      | APP(appl,_) -> reci.(i) >=0 & check_app_constr redfun (appl, reci.(i))
      | _ -> false
  else 
    false

let cofixp_reducible redfun flgs _ stk =
  if red_allowed flgs stk IOTA then
    match stk with
      | (CASE _ | APP(_,CASE _)) -> true
      | _ -> false
  else 
    false

let mindsp_nparams env sp =
  let mib = lookup_mind sp env in mib.Declarations.mind_nparams

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
      let zeta = red_allowed info.i_flags stack ZETA in
      let env' =
	if zeta or red_allowed info.i_flags stack DELTA then 
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
  | (IsSort _ | IsMeta _ | IsXtra _ ) -> (VAL(0, t), stack)
  | IsMutInd (sp,vars) -> 
      (VAL(0, mkMutInd (sp, Array.map (cbv_norm_term info env) vars)), stack)
  | IsProd (x,t,c) -> 
      (VAL(0, mkProd (x, cbv_norm_term info env t,
		      cbv_norm_term info (subs_lift env) c)),
	     stack)

and norm_head_ref k info env stack normt =
  if red_allowed_ref info.i_flags stack normt then
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
      when red_allowed info.i_flags stk BETA ->
        let subs = subs_cons (arg,env) in
          cbv_stack_term info (stack_app args stk) subs b

    (* a Fix applied enough -> IOTA *)
    | (FIXP(fix,env,_), stk)
        when fixp_reducible (cbv_norm_more info env) info.i_flags fix stk ->
        let (envf,redfix) = contract_fixp env fix in
        cbv_stack_term info stk envf redfix

    (* constructor guard satisfied or Cofix in a Case -> IOTA *)
    | (COFIXP(cofix,env,_), stk)
        when cofixp_reducible (cbv_norm_more info env) info.i_flags cofix stk->
        let (envf,redfix) = contract_cofixp env cofix in
        cbv_stack_term info stk envf redfix

    (* constructor in a Case -> IOTA
       (use red_under because we know there is a Case) *)
    | (CONSTR(n,(sp,_),_,_), APP(args,CASE(_,br,_,env,stk)))
            when red_under info.i_flags IOTA ->
              let nparams = mindsp_nparams info.i_env sp in
              let real_args = snd (list_chop nparams args) in
                cbv_stack_term info (stack_app real_args stk) env br.(n-1)
         
    (* constructor of arity 0 in a Case -> IOTA ( "   " )*)
    | (CONSTR(n,_,_,_), CASE(_,br,_,env,stk))
                  when red_under info.i_flags IOTA ->
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
  match (v, info.i_flags) with
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
  | FIXP ((lij,(lty,lna,bds)),env,args) ->
      applistc
        (mkFix (lij,
		(Array.map (cbv_norm_term info env) lty, lna, 
		 Array.map (cbv_norm_term info 
			      (subs_liftn (Array.length lty) env)) bds)))
        (List.map (cbv_norm_value info) args)
  | COFIXP ((j,(lty,lna,bds)),env,args) ->
      applistc
        (mkCoFix (j,
		  (Array.map (cbv_norm_term info env) lty, lna, 
		   Array.map (cbv_norm_term info 
				(subs_liftn (Array.length lty) env)) bds)))
        (List.map (cbv_norm_value info) args)
  | CONSTR (n,spi,vars,args) ->
      applistc
        (mkMutConstruct ((spi,n), Array.map (cbv_norm_value info) vars))
        (List.map (cbv_norm_value info) args)

type 'a cbv_infos = (cbv_value, 'a) infos

(* constant bodies are normalized at the first expansion *)
let create_cbv_infos flgs env sigma =
  { i_flags = flgs;
    i_repr = (fun old_info s c -> cbv_stack_term old_info TOP s c);
    i_env = env;
    i_evc = sigma;
    i_rels = defined_rels flgs env;
    i_vars = defined_vars flgs env;
    i_tab = Hashtbl.create 17 }


(* with profiling *)
let cbv_norm infos constr =
  let repr_fun = cbv_stack_term infos TOP in
  if !stats then begin
    reset();
    let r= cbv_norm_term infos (ESID 0) constr in
    stop();
    r
  end else
    cbv_norm_term infos (ESID 0) constr


(**** End of call by value ****)


(* Lazy reduction: the one used in kernel operations *)

(* type of shared terms. freeze and frterm are mutually recursive.
 * Clone of the Generic.term structure, but completely mutable, and
 * annotated with booleans (true when we noticed that the term is
 * normal and neutral) FLIFT is a delayed shift; allows sharing
 * between 2 lifted copies of a given term FFROZEN is a delayed
 * substitution applied to a constr
 *)

type freeze = { 
  mutable norm: bool; 
  mutable term: frterm }

and frterm =
  | FRel of int
  | FAtom of constr
  | FCast of freeze * freeze
  | FFlex of frreference
  | FInd of inductive_path * freeze array
  | FConstruct of constructor_path * freeze array
  | FApp of freeze * freeze array
  | FFix of (int array * int) * (freeze array * name list * freeze array)
      * constr array * freeze subs
  | FCoFix of int * (freeze array * name list * freeze array)
      * constr array * freeze subs
  | FCases of case_info * freeze * freeze * freeze array
  | FLambda of name * freeze * freeze * constr * freeze subs
  | FProd of name * freeze * freeze * constr * freeze subs
  | FLetIn of name * freeze * freeze * freeze * constr * freeze subs
  | FLIFT of int * freeze
  | FFROZEN of constr * freeze subs

and frreference =
  (* only vars as args of FConst ... exploited for caching *)
  | FConst of constant
  | FEvar of (existential * freeze subs)
  | FVar of identifier
  | FFarRel of int (* index in the rel_context part of _initial_ environment *)

let reloc_flex r el = r

let frterm_of v = v.term
let is_val v = v.norm 

(* Copies v2 in v1 and returns v1. The only side effect is here!  The
 * invariant of the reduction functions is that the interpretation of
 * v2 as a constr (e.g term_of_freeze below) is a reduct of the
 * interpretation of v1.
 *
 * The implementation without side effect, but losing sharing,
 * simply returns v2. *)

let freeze_assign v1 v2 =
  if !share then begin
      v1.norm <- v2.norm;
      v1.term <- v2.term;
      v1
  end else 
    v2

(* lift a freeze and yields a frterm.  No loss of sharing: the
 * resulting term takes advantage of any reduction performed in v.
 * i.e.: if (lift_frterm n v) yields w, reductions in w are reported
 * in w.term (yes: w.term, not only in w) The lifts are collapsed,
 * because we often insert lifts of 0. *)

let rec lift_frterm n v =
  match v.term with
    | FLIFT (k,f) -> lift_frterm (k+n) f
    | FAtom _ as ft -> { norm = true; term = ft }
     	(* gene: closed terms *)
    | _ -> { norm = v.norm; term = FLIFT (n,v) }


(* lift a freeze, keep sharing, but spare records when possible (case
 * n=0 ... ) The difference with lift_frterm is that reductions in v
 * are reported only in w, and not necessarily in w.term (with
 * notations above). *)
let lift_freeze n v =
  match (n, v.term) with
    | (0, _) | (_, FAtom _ ) -> v  (* identity lift or closed term *)
    | _ -> lift_frterm n v


let freeze env t = { norm = false; term = FFROZEN (t,env) }
let freeze_vect env v = Array.map (freeze env) v
let freeze_list env l = List.map (freeze env) l

let freeze_rec env (tys,lna,bds) =
  let env' = subs_liftn (Array.length bds) env in
  (Array.map (freeze env) tys, lna, Array.map (freeze env') bds)


(* pourrait peut-etre remplacer freeze ?! (et alors FFROZEN
 * deviendrait inutile) *)
(* traverse_term : freeze subs -> constr -> freeze *)
let rec traverse_term env t =
  match kind_of_term t with
    | IsRel i -> (match expand_rel i env with
		  | Inl (lams,v) -> (lift_frterm lams v)
		  | Inr (k,None) -> { norm = true; term = FRel k }
		  | Inr (k,Some p) ->
		      lift_frterm (k-p) 
		      { norm = false; term = FFlex (FFarRel p) })
    | IsVar x -> { norm = false; term = FFlex (FVar x) }
    | IsMeta _ | IsSort _ | IsXtra _ ->  { norm = true; term = FAtom t }
    | IsCast (a,b) ->
        { norm = false;
          term = FCast (traverse_term env a, traverse_term env b)}
    | IsApp (f,v) ->
        { norm = false;
	  term = FApp (traverse_term env f, Array.map (traverse_term env) v) }
    | IsMutInd (sp,v) ->
        { norm = false; term = FInd (sp, Array.map (traverse_term env) v) }
    | IsMutConstruct (sp,v) ->
        { norm = false; term = FConstruct (sp,Array.map (traverse_term env) v)}
    | IsConst (_,v as cst) ->
	assert (array_for_all isVar v);
        { norm = false;
	  term = FFlex (FConst cst) }
    | IsEvar (_,v as ev) ->
	assert (array_for_all (fun a -> isVar a or isRel a) v);
        { norm = false;
	  term = FFlex (FEvar (ev, env)) }

    | IsMutCase (ci,p,c,v) ->
        { norm = false;
	  term = FCases (ci, traverse_term env p, traverse_term env c,
			 Array.map (traverse_term env) v) }
    | IsFix (op,(tys,lna,bds)) ->
	let env' = subs_liftn (Array.length bds) env in
        { norm = false;
	  term = FFix (op, (Array.map (traverse_term env) tys, lna,
			    Array.map (traverse_term env') bds),
		       bds, env) }
    | IsCoFix (op,(tys,lna,bds)) ->
	let env' = subs_liftn (Array.length bds) env in
        { norm = false;
	  term = FCoFix (op, (Array.map (traverse_term env) tys, lna,
			      Array.map (traverse_term env') bds),
			 bds, env) }

    | IsLambda (n,t,c) ->
        { norm = false;
	  term = FLambda (n, traverse_term env t,
			  traverse_term (subs_lift env) c,
			  c, env) }
    | IsProd (n,t,c)   ->
        { norm = false;
	  term = FProd (n, traverse_term env t, 
			traverse_term (subs_lift env) c,
			c, env) }
    | IsLetIn (n,b,t,c) ->
        { norm = false;
	  term = FLetIn (n, traverse_term env b, traverse_term env t,
			 traverse_term (subs_lift env) c,
			 c, env) }

(* Back to regular terms: remove all FFROZEN, keep casts (since this
 * fun is not dedicated to the Calculus of Constructions). 
 *)
let rec lift_term_of_freeze lfts v =
  match v.term with
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (FVar x) -> mkVar x
    | FFlex (FFarRel p) -> mkRel (reloc_rel p lfts)
    | FAtom c -> c
    | FCast (a,b) ->
        mkCast (lift_term_of_freeze lfts a, lift_term_of_freeze lfts b)
    | FFlex (FConst cst) ->
	mkConst cst
    | FFlex (FEvar ((n,args), env)) ->
	let f a = lift_term_of_freeze lfts (traverse_term env a) in
	mkEvar (n, Array.map f args)
    | FInd (op, ve) ->
	mkMutInd (op, Array.map (lift_term_of_freeze lfts) ve)
    | FConstruct (op, ve) -> 
	mkMutConstruct (op, Array.map (lift_term_of_freeze lfts) ve)
    | FCases (ci, p, c, ve) ->
	mkMutCase (ci, lift_term_of_freeze lfts p,
		   lift_term_of_freeze lfts c,
		   Array.map (lift_term_of_freeze lfts) ve)
    | FFix (op,(tys,lna,bds),_,_) ->
	let lfts' = el_liftn (Array.length bds) lfts in
	mkFix (op, (Array.map (lift_term_of_freeze lfts) tys, lna,
		    Array.map (lift_term_of_freeze lfts') bds))
    | FCoFix (op,(tys,lna,bds),_,_) ->
	let lfts' = el_liftn (Array.length bds) lfts in
	mkCoFix (op, (Array.map (lift_term_of_freeze lfts) tys, lna,
		      Array.map (lift_term_of_freeze lfts') bds))
    | FApp (f,ve) ->
	mkApp (lift_term_of_freeze lfts f,
		Array.map (lift_term_of_freeze lfts) ve)
    | FLambda (n,t,c,_,_)   ->
	mkLambda (n, lift_term_of_freeze lfts t, 
	      lift_term_of_freeze (el_lift lfts) c)
    | FProd (n,t,c,_,_)   ->
	mkProd (n, lift_term_of_freeze lfts t, 
		lift_term_of_freeze (el_lift lfts) c)
    | FLetIn (n,b,t,c,_,_) ->
	mkLetIn (n, lift_term_of_freeze lfts b,
	      lift_term_of_freeze lfts t,
	      lift_term_of_freeze (el_lift lfts) c)
    | FLIFT (k,a) -> lift_term_of_freeze (el_shft k lfts) a
    | FFROZEN (t,env) ->
        let unfv = freeze_assign v (traverse_term env t) in
        lift_term_of_freeze lfts unfv


(* This function defines the correspondance between constr and freeze *)
let term_of_freeze v = lift_term_of_freeze ELID v
let applist_of_freeze appl = Array.to_list (Array.map term_of_freeze appl)


(* fstrong applies unfreeze_fun recursively on the (freeze) term and
 * yields a term.  Assumes that the unfreeze_fun never returns a
 * FFROZEN term. 
 *)
let rec fstrong unfreeze_fun lfts v =
  match (unfreeze_fun v).term with
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (FFarRel p) -> mkRel (reloc_rel p lfts)
    | FFlex (FVar x) -> mkVar x
    | FAtom c -> c
    | FCast (a,b) ->
        mkCast (fstrong unfreeze_fun lfts a, fstrong unfreeze_fun lfts b)
    | FFlex (FConst (op,ve)) ->
	mkConst (op, ve)
    | FFlex (FEvar ((n,args),env)) ->
	let f a = fstrong unfreeze_fun lfts (freeze env a) in
	mkEvar (n, Array.map f args)
    | FInd (op,ve) ->
	mkMutInd (op, Array.map (fstrong unfreeze_fun lfts) ve)
    | FConstruct (op,ve) -> 
	mkMutConstruct (op, Array.map (fstrong unfreeze_fun lfts) ve)
    | FCases (ci,p,c,ve) ->
	mkMutCase (ci, fstrong unfreeze_fun lfts p,
		   fstrong unfreeze_fun lfts c,
		   Array.map (fstrong unfreeze_fun lfts) ve)
    | FFix (op,(tys,lna,bds),_,_) ->
	let lfts' = el_liftn (Array.length bds) lfts in
	mkFix (op, (Array.map (fstrong unfreeze_fun lfts) tys, lna,
		    Array.map (fstrong unfreeze_fun lfts') bds))
    | FCoFix (op,(tys,lna,bds),_,_) ->
	let lfts' = el_liftn (Array.length bds) lfts in
	mkCoFix (op, (Array.map (fstrong unfreeze_fun lfts) tys, lna,
		      Array.map (fstrong unfreeze_fun lfts') bds))
    | FApp (f,ve) ->
	mkApp (fstrong unfreeze_fun lfts f,
		Array.map (fstrong unfreeze_fun lfts) ve)
    | FLambda (n,t,c,_,_)   ->
	mkLambda (n, fstrong unfreeze_fun lfts t,
	      fstrong unfreeze_fun (el_lift lfts) c)
    | FProd (n,t,c,_,_)   ->
	mkProd (n, fstrong unfreeze_fun lfts t,
	      fstrong unfreeze_fun (el_lift lfts) c)
    | FLetIn (n,b,t,c,_,_) ->
	mkLetIn (n, fstrong unfreeze_fun lfts b,
	      fstrong unfreeze_fun lfts t,
	      fstrong unfreeze_fun (el_lift lfts) c)
    | FLIFT (k,a) -> fstrong unfreeze_fun (el_shft k lfts) a
    | FFROZEN _ -> anomaly "Closure.fstrong"


(* Build a freeze, which represents the substitution of arg in t
 * Used to constract a beta-redex:
 *           [^depth](FLamda(S,t)) arg -> [(^depth o S).arg]t
 *)
let rec contract_subst depth t subs arg =
  freeze (subs_cons (arg, subs_shft (depth,subs))) t
  

(* Calculus of Constructions *)

type fconstr = freeze

(* Remove head lifts, applications and casts *)
let rec strip_frterm n v stack =
  match v.term with
    | FLIFT (k,f) -> strip_frterm (k+n) f stack
    | FApp (f,args) ->
        strip_frterm n f ((Array.map (lift_freeze n) args)::stack)
    | FCast (f,_) -> (strip_frterm n f stack)
    | _ -> (n, v, Array.concat stack)

let strip_freeze v = strip_frterm 0 v []


(* Same as contract_fixp, but producing a freeze *)
(* does not deal with FLIFT *)
let contract_fix_vect fix =
  let (thisbody, make_body, env, nfix) =
    match fix with
      | FFix ((reci,i),def,bds,env) ->
          (bds.(i),
	   (fun j -> { norm = false; term = FFix ((reci,j),def,bds,env) }),
	   env, Array.length bds)
      | FCoFix (i,def,bds,env) ->
          (bds.(i),
	   (fun j -> { norm = false; term = FCoFix (j,def,bds,env) }),
	   env, Array.length bds)
      | _ -> anomaly "Closure.contract_fix_vect: not a (co)fixpoint" 
  in
  let rec subst_bodies_from_i i env =
    if i = nfix then
      freeze env thisbody
    else
      subst_bodies_from_i (i+1) (subs_cons (make_body i, env))
  in       
  subst_bodies_from_i 0 env


(* CoFix reductions are context dependent. Therefore, they cannot be shared. *)
let copy_case ci p ft bl =
  (* Is the copy of bl necessary ?? I'd guess no HH *)
  { norm = false; term = FCases (ci,p,ft,Array.copy bl) }


(* Check if the case argument enables iota-reduction *)
type case_status =
  | CONSTRUCTOR of int * fconstr array
  | COFIX of int * int * (fconstr array * name list * fconstr array) *
      fconstr array * constr array * freeze subs
  | IRREDUCTIBLE


let constr_or_cofix env v =
  let (lft_hd, head, appl) = strip_freeze v in
  match head.term with
    | FConstruct (((indsp,_),i),_) ->
        let args = snd (array_chop (mindsp_nparams env indsp) appl) in
        CONSTRUCTOR (i, args)
    | FCoFix (bnum, def, bds, env) -> COFIX (lft_hd,bnum,def,appl, bds, env)
    | _ -> IRREDUCTIBLE

let fix_reducible env unf_fun n appl =
  if n < Array.length appl & n >= 0 (* e.g for Acc_rec: n = -2 *) then
    let v = unf_fun appl.(n) in
    match constr_or_cofix env v with
      | CONSTRUCTOR _ -> true
      | _ -> false
  else 
    false


(* unfreeze computes the weak head normal form of v (according to the
 * flags in info) and updates the mutable term. 
 *)
let rec unfreeze info v =
  freeze_assign v (whnf_frterm info v)

(* weak head normal form
 * Sharing info: the physical location of the ouput of this function
 * doesn't matter (only the values of its fields do). 
 *)
and whnf_frterm info ft =
  if ft.norm then begin
    incr prune; ft
  end else
    match ft.term with
      | FFROZEN (t,env) -> whnf_term info env t
      | FLIFT (k,f) ->
	  let uf = unfreeze info f in
          { norm = uf.norm; term = FLIFT(k, uf) }
      | FCast (f,_) -> whnf_frterm info f  (* remove outer casts *)
      | FApp (f,appl) -> whnf_apply info f appl
      | FFlex (FConst (sp,vars as cst)) ->
	  if red_under info.i_flags (CONST [sp]) then
            (match ref_value_cache info (ConstBinding cst) with
               | Some def ->
                   let udef = unfreeze info def in
                   lift_frterm 0 udef
               | None ->
		   { norm = true (* because only mkVar *); term = ft.term })
	  else 
	    ft
      | FFlex (FEvar ((_,vars),_ as ev)) ->
	  if red_under info.i_flags EVAR then
            (match ref_value_cache info (EvarBinding ev) with
               | Some def ->
                   let udef = unfreeze info def in
                   lift_frterm 0 udef
               | None ->
		   { norm = true (* because only mkVar/Rel *);term = ft.term })
	  else 
	    ft
      | FFlex (FVar id) as t->
	  if red_under info.i_flags DELTA then
	    match ref_value_cache info (VarBinding id) with
	      | Some def ->
		  let udef = unfreeze info def in
		  lift_frterm 0 udef
	      | None -> { norm = true; term = t }
	  else ft
      | FFlex (FFarRel k) as t ->
	  if red_under info.i_flags DELTA then
	    match ref_value_cache info (FarRelBinding k) with
	      | Some def ->
		  let udef = unfreeze info def in
		  lift_frterm 0 udef
	      | None -> { norm = true; term = t }
	  else ft

      | FCases (ci,p,co,bl) ->
	  if red_under info.i_flags IOTA then
            let c = unfreeze (infos_under info) co in
            (match constr_or_cofix info.i_env c with
	       | CONSTRUCTOR (n,real_args) when n <= Array.length bl ->
                   whnf_apply info bl.(n-1) real_args
               | COFIX (lft_hd,bnum,def,appl,bds,env) ->
                   let cofix = contract_fix_vect (FCoFix (bnum,def,bds,env)) in
                   let red_cofix =
                     whnf_apply info (lift_freeze lft_hd cofix) appl in
                   whnf_frterm info (copy_case ci p red_cofix bl)
               | _ ->
		   { norm = is_val p & is_val co & array_for_all is_val bl;
		     term = ft.term })
          else 
	    ft

      | FLetIn (na,b,fd,fc,d,subs) ->
          let c = unfreeze info b in
	  if red_under info.i_flags ZETA then
	    whnf_frterm info (contract_subst 0 d subs c)
	  else
	    { norm = false;
	      term = FLetIn (na,c,fd,fc,d,subs) }

      | FRel _ | FAtom _ -> { norm = true; term = ft.term }

      | FFix _ | FCoFix _ | FInd _ | FConstruct _ | FLambda _ | FProd _ -> ft

(* Weak head reduction: case of the application (head appl) *)
and whnf_apply info head appl =
  let head = unfreeze info head in
  if Array.length appl = 0 then 
    head
  else
    let (lft_hd,whd,args) = strip_frterm 0 head [appl] in
    match whd.term with
      | FLambda (_,_,_,t,subs) when red_under info.i_flags BETA ->
          let vbody = contract_subst lft_hd t subs args.(0) in
          whnf_apply info vbody (array_tl args)
      | FFix ((reci,bnum), _, _, _) as fx
          when red_under info.i_flags IOTA
            & fix_reducible info.i_env 
	        (unfreeze (infos_under info)) reci.(bnum) args ->
          let fix = contract_fix_vect fx in
          whnf_apply info (lift_freeze lft_hd fix) args
      | _ -> 
	  { norm = (is_val head) & (array_for_all is_val appl);
            term = FApp (head, appl) }
	    
(* essayer whnf_frterm info (traverse_term env t) a la place?
 * serait moins lazy: traverse_term ne supprime pas les Cast a la volee, etc.
 *)
and whnf_term info env t =
  match kind_of_term t with
    | IsRel i ->
	(match expand_rel i env with
	   | Inl (lams,v) ->
	       let uv = unfreeze info v in
	       lift_frterm lams uv
	   | Inr (n,None) ->
	       { norm = true; term = FRel n }
	   | Inr (n,Some k) ->
	       whnf_frterm info
		 (lift_frterm (n-k) { norm = false; term = FFlex(FFarRel k) }))

    | IsVar x -> whnf_frterm info { norm = false; term = FFlex(FVar x) }

    | IsSort _ | IsXtra _ | IsMeta _ -> {norm = true; term = FAtom t }
    | IsCast (c,_) -> whnf_term info env c    (* remove outer casts *)

    | IsApp (f,ve) ->
      	whnf_frterm info
	  { norm = false; term = FApp (freeze env f, freeze_vect env ve)}
    | IsConst cst ->
      	whnf_frterm info { norm = false; term = FFlex (FConst cst) }
    | IsEvar ev ->
      	whnf_frterm info { norm = false; term = FFlex (FEvar (ev, env)) }
    | IsMutCase (ci,p,c,ve) ->
      	whnf_frterm info
	  { norm = false;
	    term = FCases (ci, freeze env p, freeze env c, freeze_vect env ve)}

    | IsMutInd (op,v) ->
      	{ norm = (v=[||]); term = FInd (op, freeze_vect env v) }
    | IsMutConstruct (op,v) ->
      	{ norm = (v=[||]); term = FConstruct (op, freeze_vect env v) }

    | IsFix (op,(_,_,bds as def)) ->
      	{ norm = false; term = FFix (op, freeze_rec env def, bds, env) }
    | IsCoFix (op,(_,_,bds as def)) ->
      	{ norm = false; term = FCoFix (op, freeze_rec env def, bds, env) }

    | IsLambda (n,t,c) ->
        { norm = false;
	  term = FLambda (n, freeze env t, freeze (subs_lift env) c,
		       c, env) }
    | IsProd (n,t,c)   ->
        { norm = false;
	  term = FProd (n, freeze env t, freeze (subs_lift env) c,
		       c, env) }

    | IsLetIn (n,b,t,c) -> 
      	whnf_frterm info
          { norm = false;
	    term = FLetIn (n, freeze env b, freeze env t,
			   freeze (subs_lift env) c, c, env) }

(* parameterized norm *)
let norm_val info v =
  if !stats then begin
    reset();
    let r = fstrong (unfreeze info) ELID v in
    stop();
    r
  end else
    fstrong (unfreeze info) ELID v

let whd_val info v =
  let uv = unfreeze info v in
  term_of_freeze uv

let inject = freeze (ESID 0)

let search_frozen_value info = function
  | FConst cst -> ref_value_cache info (ConstBinding cst)
  | FEvar ev -> ref_value_cache info (EvarBinding ev)
  | FVar id -> ref_value_cache info (VarBinding id)
  | FFarRel p -> ref_value_cache info (FarRelBinding p)

(* cache of constants: the body is computed only when needed. *)
type 'a clos_infos = (fconstr, 'a) infos


let create_clos_infos flgs env sigma =
  { i_flags = flgs;
    i_repr = (fun old_info s c -> freeze s c);
    i_env = env;
    i_evc = sigma;
    i_rels = defined_rels flgs env;
    i_vars = defined_vars flgs env;
    i_tab = Hashtbl.create 17 }

let clos_infos_env infos = infos.i_env

(* Head normal form. *)
let fhnf info v =
  let uv = unfreeze info v in
  strip_freeze uv

let fhnf_apply infos k head appl =
  let v = whnf_apply infos (lift_freeze k head) appl in
  strip_freeze v
