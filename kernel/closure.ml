
(* $Id$ *)

open Util
open Pp
open Term
open Generic
open Names
open Inductive
open Environ
open Instantiate
open Univ
open Evd

let stats = ref false
let share = ref true

(* Profiling *)
let beta = ref 0
let delta = ref 0
let iota = ref 0
let prune = ref 0

let reset () =
  beta := 0; delta := 0; iota := 0; prune := 0

let stop() =
  mSGNL [< 'sTR"[Reds: beta=";'iNT !beta; 'sTR" delta="; 'iNT !delta;
           'sTR" iota="; 'iNT !iota; 'sTR" prune="; 'iNT !prune; 'sTR"]" >]


(* sets of reduction kinds *)
type red_kind = BETA | DELTA of sorts oper | IOTA

type reds = {
  r_beta : bool;
  r_delta : sorts oper -> bool; (* this is unsafe: exceptions may pop out *)
  r_iota : bool }

let betadeltaiota_red = {
  r_beta = true;
  r_delta = (fun _ -> true);
  r_iota = true } 

let betaiota_red = {
  r_beta = true;
  r_delta = (fun _ -> false);
  r_iota = true }
		     
let beta_red = {
  r_beta = true;
  r_delta = (fun _ -> false);
  r_iota = false }

let no_red = {
  r_beta = false;
  r_delta = (fun _ -> false);
  r_iota = false }

let incr_cnt red cnt =
  if red then begin
    if !stats then incr cnt;
    true
  end else 
    false

let red_set red = function
  | BETA -> incr_cnt red.r_beta beta
  | DELTA op -> incr_cnt (red.r_delta op) delta
  | IOTA -> incr_cnt red.r_iota iota


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

let hnf_flags = (SIMPL,betaiota_red)

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


(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
 *  * i_evc is the set of constraints for existential variables
 *  * i_tab is the cache table of the results
 *  * i_repr is the function to get the representation from the current
 *         state of the cache and the body of the constant. The result
 *         is stored in the table.
 *
 * const_value_cache searchs in the tab, otherwise uses i_repr to
 * compute the result and store it in the table. If the constant can't
 * be unfolded, returns None, but does not store this failure.  * This
 * doesn't take the RESET into account. You mustn't keep such a table
 * after a Reset.  * This type is not exported. Only its two
 * instantiations (cbv or lazy) are.
 *)

type ('a, 'b) infos = {
  i_flags : flags;
  i_repr : ('a, 'b) infos -> constr -> 'a;
  i_env : env;
  i_evc : 'b evar_map;
  i_tab : (constr, 'a) Hashtbl.t }

let const_value_cache info c =
  try  
    Some (Hashtbl.find info.i_tab c)
  with Not_found ->
    match const_abst_opt_value info.i_env info.i_evc c with
      | Some body ->
          let v = info.i_repr info body in
          Hashtbl.add info.i_tab c v;
          Some v
      | None -> None

let infos_under infos =
  { i_flags = flags_under infos.i_flags; 
    i_repr = infos.i_repr; 
    i_env = infos.i_env; 
    i_evc = infos.i_evc;
    i_tab = infos.i_tab }


(**** Call by value reduction ****)

(* The type of terms with closure. The meaning of the constructors and
 * the invariants of this datatype are the following:
 *  VAL(k,c) represents the constr c with a delayed shift of k. c must be
 *          in normal form and neutral (i.e. not a lambda, a constr or a
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
  | FIXP of sorts oper * constr array * cbv_value subs * cbv_value list
  | CONSTR of int * (section_path * int) * cbv_value array * cbv_value list

(* les vars pourraient etre des constr,
   cela permet de retarder les lift: utile ?? *) 

(* relocation of a value; used when a value stored in a context is expanded
 * in a larger context. e.g.  [%k (S.t)](k+1) --> [^k]t  (t is shifted of k)
 *)
let rec shift_value n = function
  | VAL (k,v) -> VAL ((k+n),v)
  | LAM (x,a,b,s) -> LAM (x,a,b,subs_shft (n,s))
  | FIXP (op,bv,s,args) ->
      FIXP (op,bv,subs_shft (n,s), List.map (shift_value n) args)
  | CONSTR (i,spi,vars,args) ->
      CONSTR (i, spi, Array.map (shift_value n) vars,
              List.map (shift_value n) args)
	

(* Contracts a fixpoint: given a fixpoint and a substitution,
 * returns the corresponding fixpoint body, and the substitution in which
 * it should be evaluated: its first variables are the fixpoint bodies
 * (S, (fix Fi {F0 := T0 .. Fn-1 := Tn-1}))
 *    -> (S. [S]F0 . [S]F1 ... . [S]Fn-1, Ti)
 *)
let contract_fixp env fix =
  let (bnum, bodies, make_body) = match fix with
    | DOPN(Fix(reci,i),bvect) ->
        (i, array_last bvect, (fun j -> FIXP(Fix(reci,j), bvect, env, [])))
    | DOPN(CoFix i,bvect) ->
        (i, array_last bvect, (fun j -> FIXP(CoFix j, bvect, env, [])))
    | _ -> anomaly "Closure.contract_fixp: not a (co)fixpoint" 
  in
  let rec subst_bodies_from_i i subs = function
    | DLAM(_,t) -> subst_bodies_from_i (i+1) (subs_cons (make_body i, subs)) t
    | DLAMV(_,bds) -> (subs_cons (make_body i, subs), bds.(bnum))
    | _ -> anomaly "Closure.contract_fixp: malformed (co)fixpoint"
  in       
  subst_bodies_from_i 0 env bodies


(* type of terms with a hole. This hole can appear only under AppL or Case.
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


(* Transfer application lists from a value to the stack
 * useful because fixpoints may be totally applied in several times
 *)
let strip_appl head stack =
  match head with
    | FIXP (op,bv,env,app) -> (FIXP(op,bv,env,[]), stack_app app stack)
    | CONSTR (i,spi,vars,app) -> (CONSTR(i,spi,vars,[]), stack_app app stack)
    | _ -> (head, stack)


(* Invariant: if the result of norm_head is CONSTR or FIXP, it last
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
	
let fixp_reducible redfun flgs op stk =
  if red_allowed flgs stk IOTA then
    match (op,stk) with               (* !!! for Acc_rec: reci.(i) = -2 *)
      | (Fix (reci,i), APP(appl,_)) ->
          (reci.(i) >= 0  &  check_app_constr redfun (appl, reci.(i)))
      | (CoFix i, (CASE _ | APP(_,CASE _))) -> true
      | _ -> false
  else 
    false

let mindsp_nparams env sp =
  let mib = lookup_mind sp env in mib.mind_nparams

(* The main recursive functions
 *
 * Go under applications and cases (pushed in the stack), expand head
 * constants or substitued de Bruijn, and try to make appear a
 * constructor, a lambda or a fixp in the head. If not, it is a value
 * and is completely computed here. The head redexes are NOT reduced:
 * the function returns the pair of a cbv_value and its stack.  *
 * Invariant: if the result of norm_head is CONSTR or FIXP, it last
 * argument is [].  Because we must put all the applied terms in the
 * stack. *)

let rec norm_head info env t stack =
  (* no reduction under binders *)
  match t with
  (* stack grows (remove casts) *)
  | DOPN (AppL,appl) -> (* Applied terms are normalized immediately;
                        they could be computed when getting out of the stack *)
      (match Array.to_list appl with
	 | head::args ->
	     let nargs = List.map (cbv_stack_term info TOP env) args in
               norm_head info env head (stack_app nargs stack)
	 | [] -> anomaly "norm_head : malformed constr AppL [||]")
  | DOPN (MutCase _,_) -> 
      let (ci,p,c,v) = destCase t in
      norm_head info env c (CASE(p,v,ci,env,stack))
  | DOP2 (Cast,ct,c) -> norm_head info env ct stack

  (* constants, axioms
   * the first pattern is CRUCIAL, n=0 happens very often:
   * when reducing closed terms, n is always 0 *)
  | Rel i -> (match expand_rel i env with
                | Inl (0,v) ->
                    reduce_const_body (cbv_norm_more info) v stack
                | Inl (n,v) ->
                    reduce_const_body
                      (cbv_norm_more info) (shift_value n v) stack
                | Inr n -> (VAL(0, Rel n), stack))
  | DOPN ((Const _ | Evar _ | Abst _) as op, vars)
                  when red_allowed info.i_flags stack (DELTA op) ->
      let normt = DOPN(op, Array.map (cbv_norm_term info env) vars) in
      (match const_value_cache info normt with
         | Some body -> reduce_const_body (cbv_norm_more info) body stack
         | None -> (VAL(0,normt), stack))

  (* non-neutral cases *)
  | DOP2 (Lambda,a,DLAM(x,b)) -> (LAM(x,a,b,env), stack)
  | DOPN ((Fix _ | CoFix _) as op, v) -> (FIXP(op,v,env,[]), stack)
  | DOPN (MutConstruct(spi,i),vars) ->
      (CONSTR(i,spi, Array.map (cbv_stack_term info TOP env) vars,[]), stack)

  (* neutral cases *)
  | (VAR _ | DOP0 _) -> (VAL(0, t), stack)
  | DOP1 (op, nt) -> (VAL(0, DOP1(op, cbv_norm_term info env nt)), stack)
  | DOP2 (op,a,b) ->
      (VAL(0, DOP2(op, cbv_norm_term info env a, cbv_norm_term info env b)),
       stack)
  | DOPN (op,vars) ->
      (VAL(0, DOPN(op, Array.map (cbv_norm_term info env) vars)), stack)
  | DOPL (op,l) ->
      (VAL(0, DOPL(op, List.map (cbv_norm_term info env) l)), stack)
  | DLAM (x,t) ->
      (VAL(0, DLAM(x, cbv_norm_term info (subs_lift env) t)), stack)
  | DLAMV (x,ve) ->
      (VAL(0, DLAMV(x, Array.map(cbv_norm_term info (subs_lift env)) ve)),
       stack)


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

    (* a Fix applied enough,
       constructor guard satisfied or Cofix in a Case -> IOTA *)
    | (FIXP(op,bv,env,_), stk)
             when fixp_reducible (cbv_norm_more info) info.i_flags op stk ->
               let (envf,redfix) = contract_fixp env (DOPN(op,bv)) in
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
    | (FIXP(op,bv,env,_), APP(appl,TOP)) -> FIXP(op,bv,env,appl) 
    | (CONSTR(n,spi,vars,_), APP(appl,TOP)) -> CONSTR(n,spi,vars,appl)

    (* definitely a value *)
    | (head,stk) -> VAL(0,apply_stack info (cbv_norm_value info head) stk)


(* if we are in SIMPL mode, maybe v isn't reduced enough *)
and cbv_norm_more info v =
  match (v, info.i_flags) with
    | (VAL(k,t), ((SIMPL|WITHBACK),_)) ->
        cbv_stack_term (infos_under info) TOP (subs_shft (k,ESID)) t
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
        (mkMutCaseA ci (cbv_norm_term info env ty) t
           (Array.map (cbv_norm_term info env) br))
        st


(* performs the reduction on a constr, and returns a constr *)
and cbv_norm_term info env t =
  (* reduction under binders *)
  cbv_norm_value info (cbv_stack_term info TOP env t)

(* reduction of a cbv_value to a constr *)
and cbv_norm_value info = function (* reduction under binders *)
  | VAL (n,v) -> lift n v
  | LAM (x,a,b,env) -> DOP2(Lambda, cbv_norm_term info env a,
                              DLAM(x,cbv_norm_term info (subs_lift env) b))
  | FIXP (op,cl,env,args) ->
      applistc
        (DOPN(op, Array.map (cbv_norm_term info env) cl))
        (List.map (cbv_norm_value info) args)
  | CONSTR (n,spi,vars,args) ->
      applistc
        (DOPN (MutConstruct(spi,n), Array.map (cbv_norm_value info) vars))
        (List.map (cbv_norm_value info) args)



type 'a cbv_infos = (cbv_value, 'a) infos

(* constant bodies are normalized at the first expansion *)
let create_cbv_infos flgs env sigma =
  { i_flags = flgs;
    i_repr = (fun old_info c -> cbv_stack_term old_info TOP ESID c);
    i_env = env;
    i_evc = sigma;
    i_tab = Hashtbl.create 17 }


(* with profiling *)
let cbv_norm infos constr =
  if !stats then begin
    reset();
    let r= cbv_norm_term infos ESID constr in
    stop();
    r
  end else
    cbv_norm_term infos ESID constr

(**** End of call by value ****)


(* Lazy reduction: the one used in kernel operations *)

(* type of shared terms. freeze and frterm are mutually recursive.
 * Clone of the Generic.term structure, but completely mutable, and
 * annotated with booleans (true when we noticed that the term is
 * normal and neutral) FLIFT is a delayed shift; allows sharing
 * between 2 lifted copies of a given term FFROZEN is a delayed
 * substitution applied to a constr
 *)

type 'oper freeze = { 
  mutable norm: bool; 
  mutable term: 'oper frterm }

and 'oper frterm =
  | FRel of int
  | FVAR of identifier
  | FOP0 of 'oper
  | FOP1 of 'oper * 'oper freeze
  | FOP2 of 'oper * 'oper freeze * 'oper freeze
  | FOPN of 'oper * 'oper freeze array
  | FOPL of 'oper * 'oper freeze list
  | FLAM of name * 'oper freeze * 'oper term * 'oper freeze subs
  | FLAMV of name * 'oper freeze array * 'oper term array * 'oper freeze subs
  | FLIFT of int * 'oper freeze
  | FFROZEN of 'oper term * 'oper freeze subs

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
    | (FOP0 _ | FVAR _) as ft -> { norm = true; term = ft }
     	(* gene: closed terms *)
    | _ -> { norm = v.norm; term = FLIFT (n,v) }


(* lift a freeze, keep sharing, but spare records when possible (case
 * n=0 ... ) The difference with lift_frterm is that reductions in v
 * are reported only in w, and not necessarily in w.term (with
 * notations above). *)
let lift_freeze n v =
  match (n, v.term) with
    | (0, _) | (_, (FOP0 _ | FVAR _)) -> v   (* identity lift or closed term *)
    | _ -> lift_frterm n v


let freeze env t = { norm = false; term = FFROZEN (t,env) }
let freeze_vect env v = Array.map (freeze env) v
let freeze_list env l = List.map (freeze env) l

(* pourrait peut-etre remplacer freeze ?! (et alors FFROZEN
 * deviendrait inutile) *)

let rec traverse_term env t =
  match t with
    | Rel i -> (match expand_rel i env with
		  | Inl (lams,v) -> (lift_frterm lams v)
		  | Inr k -> { norm = true; term = FRel k })
    | VAR x -> { norm = true; term = FVAR x }
    | DOP0 op ->  { norm = true; term = FOP0 op }
    | DOP1 (op, nt) -> { norm = false; term = FOP1 (op, traverse_term env nt) }
    | DOP2 (op,a,b) ->
        { norm = false;
          term = FOP2 (op, traverse_term env a, traverse_term env b)}
    | DOPN (op,v) ->
        { norm = false; term = FOPN (op, Array.map (traverse_term env) v) }
    | DOPL (op,l) ->
        { norm = false; term = FOPL (op, List.map (traverse_term env) l) }
    | DLAM (x,a) ->
        { norm = false;
          term = FLAM (x, traverse_term (subs_lift env) a, a, env) }
    | DLAMV (x,ve) ->
        { norm = (ve=[||]);
          term = FLAMV (x, Array.map (traverse_term (subs_lift env)) ve,
                        ve, env) }

(* Back to regular terms: remove all FFROZEN, keep casts (since this
 * fun is not dedicated to the Calulus of Constructions). 
 *)
let rec lift_term_of_freeze lfts v =
  match v.term with
    | FRel i -> Rel (reloc_rel i lfts)
    | FVAR x -> VAR x
    | FOP0 op -> DOP0 op
    | FOP1 (op,a) -> DOP1 (op, lift_term_of_freeze lfts a)
    | FOP2 (op,a,b) ->
        DOP2 (op, lift_term_of_freeze lfts a, lift_term_of_freeze lfts b)
    | FOPN (op,ve) -> DOPN (op, Array.map (lift_term_of_freeze lfts) ve)
    | FOPL (op,l) -> DOPL (op, List.map (lift_term_of_freeze lfts) l)
    | FLAM (x,a,_,_) -> DLAM (x, lift_term_of_freeze (el_lift lfts) a)
    | FLAMV (x,ve,_,_) ->
        DLAMV (x, Array.map (lift_term_of_freeze (el_lift lfts)) ve)
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
    | FRel i -> Rel (reloc_rel i lfts)
    | FVAR x -> VAR x
    | FOP0 op -> DOP0 op
    | FOP1 (op,a) -> DOP1 (op, fstrong unfreeze_fun lfts a)
    | FOP2 (op,a,b) ->
        DOP2 (op, fstrong unfreeze_fun lfts a, fstrong unfreeze_fun lfts b)
    | FOPN (op,ve) -> DOPN (op, Array.map (fstrong unfreeze_fun lfts) ve)
    | FOPL (op,l) -> DOPL (op, List.map (fstrong unfreeze_fun lfts) l)
    | FLAM (x,a,_,_) -> DLAM (x, fstrong unfreeze_fun (el_lift lfts) a)
    | FLAMV (x,ve,_,_) ->
        DLAMV (x, Array.map (fstrong unfreeze_fun (el_lift lfts)) ve)
    | FLIFT (k,a) -> fstrong unfreeze_fun (el_shft k lfts) a
    | FFROZEN _ -> anomaly "Closure.fstrong"


(* Build a freeze, which represents the substitution of arg in fun_body.
 * Used to constract a beta-redex:
 *           [^depth](FLAM(S,t)) arg -> [(^depth o S).arg]t
 * We also deal with FLIFT that would have been inserted between the
 * Lambda and FLAM operators. This never happens in practice.
 *)
let rec contract_subst depth fun_body arg =
    match fun_body.term with
        FLAM(_,_,t,subs) -> freeze (subs_cons (arg, subs_shft (depth,subs))) t
      | FLIFT(k,fb) -> contract_subst (depth+k) fb arg
      | _ -> anomaly "Closure.contract_subst: malformed function"
  

(* Calculus of Constructions *)

type fconstr = sorts oper freeze

let inject constr = freeze ESID constr

(* Remove head lifts, applications and casts *)
let rec strip_frterm n v stack =
  match v.term with
    | FLIFT (k,f) -> strip_frterm (k+n) f stack
    | FOPN (AppL,appl) ->
        strip_frterm n appl.(0)
          ((Array.map (lift_freeze n) (array_tl appl))::stack)
    | FOP2 (Cast,f,_) -> (strip_frterm n f stack)
    | _ -> (n, v, Array.concat stack)

let strip_freeze v = strip_frterm 0 v []


(* Same as contract_fixp, but producing a freeze *)
(* does not deal with FLIFT *)
let contract_fix_vect unf_fun fix =
  let (bnum, bodies, make_body) =
    match fix with
      | FOPN(Fix(reci,i),bvect) ->
          (i, array_last bvect,
           (fun j -> { norm = false; term = FOPN(Fix(reci,j), bvect) }))
      | FOPN(CoFix i,bvect) ->
          (i, array_last bvect,
           (fun j -> { norm = false; term = FOPN(CoFix j, bvect) }))
      | _ -> anomaly "Closure.contract_fix_vect: not a (co)fixpoint" 
  in
  let rec subst_bodies_from_i i depth bds =
    let ubds = unf_fun bds in
    match ubds.term with
      | FLAM(_,_,t,env) ->
          subst_bodies_from_i (i+1) depth
            (freeze (subs_cons (make_body i, env)) t)
      | FLAMV(_,_,tv,env) ->
          freeze (subs_shft (depth, subs_cons (make_body i, env))) tv.(bnum)
      | FLIFT(k,lbds) -> subst_bodies_from_i i (k+depth) lbds
      | _ -> anomaly "Closure.contract_fix_vect: malformed (co)fixpoint"
  in       
  subst_bodies_from_i 0 0 bodies


(* CoFix reductions are context dependent. Therefore, they cannot be shared. *)
let copy_case ci cl ft =
  let ncl = Array.copy cl in
  ncl.(1) <- ft;
  { norm = false; term = FOPN(MutCase ci,ncl) }


(* Check if the case argument enables iota-reduction *)
type case_status =
  | CONSTRUCTOR of int * fconstr array
  | COFIX of int * int * fconstr array * fconstr array
  | IRREDUCTIBLE


let constr_or_cofix env v =
  let (lft_hd, head, appl) = strip_freeze v in
  match head.term with
    | FOPN(MutConstruct ((indsp,_),i),_) ->
        let args = snd (array_chop (mindsp_nparams env indsp) appl) in
        CONSTRUCTOR (i, args)
    | FOPN(CoFix bnum, bv) -> COFIX (lft_hd,bnum,bv,appl)
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
      | FOP2 (Cast,f,_) -> whnf_frterm info f  (* remove outer casts *)
      | FOPN (AppL,appl) -> whnf_apply info appl.(0) (array_tl appl)
      | FOPN ((Const _ | Evar _ | Abst _) as op,vars) ->
	  if red_under info.i_flags (DELTA op) then
            let cst = DOPN(op, Array.map term_of_freeze vars) in
            (match const_value_cache info cst with
               | Some def ->
                   let udef = unfreeze info def in
                   lift_frterm 0 udef
               | None -> { norm = array_for_all is_val vars; term = ft.term })
	  else 
	    ft
      | FOPN (MutCase ci,cl) ->
	  if red_under info.i_flags IOTA then
            let c = unfreeze (infos_under info) cl.(1) in
            (match constr_or_cofix info.i_env c with
	       | CONSTRUCTOR (n,real_args) when n <= (Array.length cl - 2) ->
                   whnf_apply info cl.(n+1) real_args
               | COFIX (lft_hd,bnum,bvect,appl) ->
                   let cofix =
                     contract_fix_vect (unfreeze info)
                       (FOPN(CoFix bnum, bvect)) in
                   let red_cofix =
                     whnf_apply info (lift_freeze lft_hd cofix) appl in
                   whnf_frterm info (copy_case ci cl red_cofix)
               | _ -> { norm = array_for_all is_val cl; term = ft.term })
          else 
	    ft

   | FRel _ | FVAR _ | FOP0 _ -> { norm = true; term = ft.term }
   | _ -> ft

(* Weak head reduction: case of the application (head appl) *)
and whnf_apply info head appl =
  let head = unfreeze info head in
  if Array.length appl = 0 then 
    head
  else
    let (lft_hd,whd,args) = strip_frterm 0 head [appl] in
    match whd.term with
      | FOP2(Lambda,_,b) when red_under info.i_flags BETA ->
          let vbody = contract_subst lft_hd (unfreeze info b) args.(0) in
          whnf_apply info vbody (array_tl args)
      | (FOPN(Fix(reci,bnum), tb) as fx)
          when red_under info.i_flags IOTA
            & fix_reducible info.i_env 
	        (unfreeze (infos_under info)) reci.(bnum) args ->
          let fix = contract_fix_vect (unfreeze info) fx in
          whnf_apply info (lift_freeze lft_hd fix) args
      | _ -> 
	  { norm = (is_val head) & (array_for_all is_val appl);
            term = FOPN(AppL, array_cons head appl) }
	    
(* essayer whnf_frterm info (traverse_term env t) a la place?
 * serait moins lazy: traverse_term ne supprime pas les Cast a la volee, etc.
 *)
and whnf_term info env t =
  match t with
    | Rel i -> (match expand_rel i env with
		  | Inl (lams,v) ->
		      let uv = unfreeze info v in
		      lift_frterm lams uv
		  | Inr k -> { norm = true; term = FRel k })
    | VAR x -> { norm = true; term = FVAR x }
    | DOP0 op -> {norm = true; term = FOP0 op }
    | DOP1 (op, nt) -> { norm = false; term = FOP1 (op, freeze env nt) }
    | DOP2 (Cast,ct,c) -> whnf_term info env ct    (* remove outer casts *)
    | DOP2 (op,a,b) -> (* Lambda Prod *)
      	{ norm = false; term = FOP2 (op, freeze env a, freeze env b) }
    | DOPN ((AppL | Const _ | Evar _ | Abst _ | MutCase _) as op, ve) ->
      	whnf_frterm info { norm = false; term = FOPN (op, freeze_vect env ve) }
    | DOPN ((MutInd _ | MutConstruct _) as op,v) ->
      	{ norm = (v=[||]); term = FOPN (op, freeze_vect env v) }
    | DOPN (op,v) ->
      	{ norm = false; term = FOPN (op, freeze_vect env v) } (* Fix CoFix *)
    | DOPL (op,l) -> { norm = false; term = FOPL (op, freeze_list env l) }
    | DLAM (x,a) ->
      	{ norm = false; term = FLAM (x, freeze (subs_lift env) a, a, env) }
    | DLAMV (x,ve) ->
      	{ norm = (ve=[||]);
          term = FLAMV (x, freeze_vect (subs_lift env) ve, ve, env) }
      
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

let search_frozen_cst info op vars =
  let cst = DOPN(op, Array.map (norm_val info) vars) in
  const_value_cache info cst
    

(* cache of constants: the body is computed only when needed. *)
type 'a clos_infos = (fconstr, 'a) infos

let create_clos_infos flgs env sigma =
  { i_flags = flgs;
    i_repr = (fun old_info c -> inject c);
    i_env = env;
    i_evc = sigma;
    i_tab = Hashtbl.create 17 }

let clos_infos_env infos = infos.i_env

(* Head normal form. *)
let fhnf info v =
  let uv = unfreeze info v in
  strip_freeze uv

let fhnf_apply infos k head appl =
  let v = whnf_apply infos (lift_freeze k head) appl in
  strip_freeze v
