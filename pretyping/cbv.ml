(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Term
open Names
open Native
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
 *  PRIMITIVE(cop,args) represent a particial application of 
 *          a primitive, or a fully applied primitive 
 *          which does not reduce.
 *          cop is the constr representing op.
 *)

type cbv_value =
  | VAL of int * constr
  | STACK of int * cbv_value * cbv_stack
  | CBN of constr * cbv_value subs
  | LAM of int * (name * constr) list * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value array
  | COFIXP of cofixpoint * cbv_value subs * cbv_value array
  | CONSTR of constructor * cbv_value array
  | NATIVEINT of Native.Uint31.t
  | NATIVEARR of cbv_value * cbv_value Native.Parray.t
  | PRIMITIVE of Native.op * constr * cbv_value array

                  


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
and cbv_stack =
  | TOP
  | APP of cbv_value array * cbv_stack
  | CASE of constr * constr array * case_info * cbv_value subs * cbv_stack

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
  | NATIVEINT _ as v -> v
  | NATIVEARR(t,p) -> 
      NATIVEARR(shift_value n t, Parray.map (shift_value n) p)
  | PRIMITIVE(op,c,args) ->
      PRIMITIVE(op,c,Array.map (shift_value n) args)

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

let make_constr_ref n k t = 
  match k with 
  | RelKey p -> mkRel (n+p)
  | VarKey id -> t 
  | ConstKey cst -> t

(* Adds an application list. Collapse APPs! *)
let stack_app appl stack =
  if Array.length appl = 0 then stack else
    match stack with
    | APP(args,stk) -> APP(Array.append appl args,stk)
    | _             -> APP(appl, stack)

let rec stack_concat stk1 stk2 =
  match stk1 with
      TOP -> stk2
    | APP(v,stk1') -> APP(v,stack_concat stk1' stk2)
    | CASE(c,b,i,s,stk1') -> CASE(c,b,i,s,stack_concat stk1' stk2)

(* merge stacks when there is no shifts in between *)
let mkSTACK = function
    v, TOP -> v
  | STACK(0,v0,stk0), stk -> STACK(0,v0,stack_concat stk0 stk)
  | v,stk -> STACK(0,v,stk)


(* Change: zeta reduction cannot be avoided in CBV *)

open RedFlags

let red_set_ref flags = function
  | RelKey _ -> red_set flags fDELTA
  | VarKey id -> red_set flags (fVAR id)
  | ConstKey sp -> red_set flags (fCONST sp)

(* Transfer application lists from a value to the stack
 * useful because fixpoints may be totally applied in several times.
 * On the other hand, irreductible atoms absorb the full stack.
 *)
let strip_appl head stack =
  match head with
    | FIXP (fix,env,app) -> (FIXP(fix,env,[||]), stack_app app stack)
    | COFIXP (cofix,env,app) -> (COFIXP(cofix,env,[||]), stack_app app stack)
    | CONSTR (c,app) -> (CONSTR(c,[||]), stack_app app stack)
    | PRIMITIVE(op,c,app) -> (PRIMITIVE(op,c,[||]), stack_app app stack)
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

(* Reduction of primitives *)

module VNativeEntries =
  struct 

    type elem = cbv_value 
    type args = cbv_value array
    module Parray = Parray	
	  
    let get = Array.get

    let get_int e =
      match e with
      | NATIVEINT i -> i
      | _ -> raise Not_found

    let get_parray e =
      match e with
      | NATIVEARR(t,p) -> (t,p)
      | _ -> raise Not_found

    let dummy = VAL (0,mkRel 0)

    let current_retro = ref Pre_env.empty_retroknowledge
    let defined_int = ref false
    let vint = ref dummy 

    let init_int retro =
      match retro.Pre_env.retro_int31 with
      | Some (cte, c) ->
	  defined_int := true;
	  vint := VAL(0,c)
      | None -> defined_int := false

    let defined_bool = ref false
    let vtrue = ref dummy
    let vfalse = ref dummy

    let init_bool retro =
      match retro.Pre_env.retro_bool with
      | Some (ct,cf) ->
	  defined_bool := true;
	  vtrue := CONSTR(ct,[||]);
	  vfalse := CONSTR(cf,[||])
      | None -> defined_bool :=false

    let dummy_construct =
      let did = Names.id_of_string "dummy" in
      let dp = Names.make_dirpath [did] in
      let mind = 
	Names.make_mind (Names.MPfile dp) dp (Names.mk_label "dummy") in
      ((mind ,0),0)

    let defined_carry = ref false
    let cC0 = ref dummy_construct
    let cC1 = ref dummy_construct

    let init_carry retro =
      match retro.Pre_env.retro_carry with
      | Some(c0,c1) ->
	  defined_carry := true;
          cC0 := c0;
	  cC1 := c1 
      | None -> defined_carry := false

    let defined_pair = ref false
    let cPair = ref dummy_construct
	
    let init_pair retro = 
      match retro.Pre_env.retro_pair with
      | Some c ->
	  defined_pair := true;
          cPair := c
      | None -> defined_pair := false

    let defined_cmp = ref false
    let vEq = ref dummy  
    let vLt = ref dummy
    let vGt = ref dummy

    let init_cmp retro =
      match retro.Pre_env.retro_cmp with
      | Some (cEq, cLt, cGt) ->
	  defined_cmp := true;
	  vEq := CONSTR(cEq,[||]);
	  vLt := CONSTR(cLt,[||]);
	  vGt := CONSTR(cGt,[||])
      | None -> defined_cmp := false

    let defined_array = ref false

    let init_array retro =
      defined_array := retro.Pre_env.retro_array <> None
   
    let defined_refl = ref false
	
    let crefl = ref dummy_construct
	
    let init_refl retro =
      match retro.Pre_env.retro_refl with
      | Some crefl' ->
	  defined_refl := true;
	  crefl := crefl'
      | None -> defined_refl := false

    let init env = 
      current_retro := retroknowledge env;
      init_int !current_retro;
      init_bool !current_retro;
      init_carry !current_retro;
      init_pair !current_retro;
      init_cmp !current_retro;
      init_array !current_retro;
      init_refl !current_retro
	  
    let check_env env =
      if not (!current_retro == retroknowledge env) then init env

    let check_int env =
      check_env env; 
      assert (!defined_int)

    let check_bool env =
      check_env env;
      assert (!defined_bool)

    let check_carry env = 
      check_env env;
      assert (!defined_carry && !defined_int)

    let check_pair env =
      check_env env;
      assert (!defined_pair && !defined_int)

    let check_cmp env =
      check_env env;
      assert (!defined_cmp)

    let check_array env =
      check_env env;
      assert (!defined_array)
 
    let check_refl env =
      check_env env;
      assert (!defined_refl && !defined_int)

    let is_refl e =
      match e with
      | CONSTR(_,_) -> true
      | _ -> false

    let mk_int_refl env e =
      check_refl env;
      CONSTR(!crefl,[|!vint;e|])

    let mkInt env i = 
      check_int env;
      NATIVEINT i

    let mkBool env b = 
      check_bool env;
      if b then !vtrue else !vfalse
       
    let mkCarry env b e =
      check_carry env;
      CONSTR((if b then !cC1 else !cC0), [|!vint;e|])

    let mkPair env e1 e2 =
      check_pair env;
      CONSTR(!cPair, [|!vint;!vint;e1;e2|])

    let mkLt env = 
      check_cmp env;
      !vLt
 
    let mkEq env = 
      check_cmp env;
      !vEq

    let mkGt env = 
      check_cmp env;
      !vGt

    let mkArray env t p =
      check_array env;
      NATIVEARR(t,p)

    let mkClos id t body s =
      LAM(1,[id,t],body, Esubst.CONS (s,Esubst.ESID 0))

  end

module VredNative = RedNative(VNativeEntries)



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
        | Inr (n,Some p) -> norm_head_ref (n-p) info env stack (RelKey p) t) 

  | Var id -> norm_head_ref 0 info env stack (VarKey id) t

  | Const sp -> norm_head_ref 0 info env stack (ConstKey sp) t

  | LetIn (_, b, _, c) ->
      (* zeta means letin are contracted; delta without zeta means we *)
      (* allow bindings but leave let's in place *)
      if red_set (info_flags info) fZETA then
        (* New rule: for Cbv, Delta does not apply to locally bound variables
           or red_set (info_flags info) fDELTA
         *)
	let env' = subs_cons ([|cbv_stack_term info TOP env b|],env) in
        norm_head info env' c stack
      else
	(CBN(t,env), stack) (* Considérer une coupure commutative ? *)

  | Evar ev ->
      (match evar_value info ev with
          Some c -> norm_head info env c stack
        | None -> (VAL(0, t), stack))

  (* non-neutral cases *)
  | Lambda _ ->
      let ctxt,b = decompose_lam t in
      (LAM(List.length ctxt, List.rev ctxt,b,env), stack)
  | Fix fix -> (FIXP(fix,env,[||]), stack)
  | CoFix cofix -> (COFIXP(cofix,env,[||]), stack)
  | Construct c -> (CONSTR(c, [||]), stack)

  (* neutral cases *)
  | (Sort _ | Meta _ | Ind _) -> (VAL(0, t), stack)
  | Prod _ -> (CBN(t,env), stack)
  
  (* Native *)
  | NativeInt i -> (NATIVEINT i,stack)
  | NativeArr(t,p) ->
      let len = Array.length p - 1 in
      let t = cbv_stack_term info TOP env t in
      let p = 
	Parray.init (Uint31.of_int len) 
	  (fun i -> cbv_stack_term info TOP env  p.(i))
	  (cbv_stack_term info TOP env p.(len)) in
      (NATIVEARR(t, p),stack)

and norm_head_ref k info env stack normt t =
  if red_set_ref (info_flags info) normt then
    match ref_value_cache info normt with
    | Declarations.Def body -> strip_appl (shift_value k body) stack
    | Declarations.Primitive op -> (PRIMITIVE(op,t,[||]),stack)
    | _ -> (VAL(0,make_constr_ref k normt t),stack)
  else (VAL(0,make_constr_ref k normt t),stack)

(* cbv_stack_term performs weak reduction on constr t under the subs
 * env, with context stack, i.e. ([env]t stack).  First computes weak
 * head normal form of t and checks if a redex appears with the stack.
 * If so, recursive call to reach the real head normal form.  If not,
 * we build a value.
 *)

and cbv_stack_term info stack env t =
  cbv_val_stack info (norm_head info env t stack) 

and cbv_val_stack info (v,stack) =
  match (v,stack) with
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
  | (FIXP(fix,env,[||]), stk)
    when fixp_reducible (info_flags info) fix stk ->
      let (envf,redfix) = contract_fixp env fix in
      cbv_stack_term info stk envf redfix

      (* constructor guard satisfied or Cofix in a Case -> IOTA *)
  | (COFIXP(cofix,env,[||]), stk)
        when cofixp_reducible (info_flags info) cofix stk->
        let (envf,redfix) = contract_cofixp env cofix in
        cbv_stack_term info stk envf redfix

    (* constructor in a Case -> IOTA *)
    | (CONSTR((sp,n),[||]), APP(args,CASE(_,br,ci,env,stk)))
            when red_set (info_flags info) fIOTA ->
	let cargs =
          Array.sub args ci.ci_npar (Array.length args - ci.ci_npar) in
        cbv_stack_term info (stack_app cargs stk) env br.(n-1)

    (* constructor of arity 0 in a Case -> IOTA *)
    | (CONSTR((_,n),_), CASE(_,br,_,env,stk))
            when red_set (info_flags info) fIOTA ->
                    cbv_stack_term info stk env br.(n-1)

    (* may be reduced later by application *)
    | (FIXP(fix,env,[||]), APP(appl,TOP)) -> FIXP(fix,env,appl)
    | (COFIXP(cofix,env,[||]), APP(appl,TOP)) -> COFIXP(cofix,env,appl)
    | (CONSTR(c,[||]), APP(appl,TOP)) -> CONSTR(c,appl)
    (* primitive apply to arguments *)
    | (PRIMITIVE(op,c,[||]), APP(appl,stk)) ->
	let (nparams,nargs) = Native.arity op in
	let nall = nparams + nargs in
	let len = Array.length appl in
	if nall <= len then
	  let args = 
	    if len = nall then appl
	    else Array.sub appl 0 nall in
	  let stk = 
	    if nall < len then 
	      stack_app (Array.sub appl nall (len - nall)) stk
	    else stk in
	  match VredNative.red_op (env_info info) op c args with
	  | Some v ->  cbv_val_stack info (v,stk)
	  | None -> mkSTACK(PRIMITIVE(op,c,args), stk)
	else (* partical application *)
	  (assert (stk = TOP);
	   PRIMITIVE(op,c,appl))

       (* Need to push argument on the stack *)
    | ((FIXP (_,_,appl)|COFIXP(_,_,appl)|
      CONSTR(_,appl)|PRIMITIVE(_,_,appl)),stk) when Array.length appl <> 0 ->
	cbv_val_stack info (strip_appl v stk)

       (* definitely a value *)
    | (head,stk) -> mkSTACK(head, stk)

(*and red_primitive info op c args stk =
  
  let env = env_info info in
  match op with
  | Ocaml_prim cop ->
      (try Inl (VredNative.red_caml_prim env cop args, stk)
      with _ -> Inr (mkSTACK(PRIMITIVE(op,c,args), stk)))

  | Oprim cop -> 
      (try Inl (VredNative.red_prim env cop args, stk)
      with _ -> Inr (mkSTACK(PRIMITIVE(op,c,args), stk)))

  | Oiterator Int31foldi ->
      let get_args () =
	try 
	  let t = VNativeEntries.get args 0 in
	  let f = VNativeEntries.get args 1 in
	  let a = VNativeEntries.get args 2 in
	  let min = VNativeEntries.get_int (VNativeEntries.get args 3) in
	  let max =  VNativeEntries.get_int (VNativeEntries.get args 4) in
	  Some (t,f,a,min,max)
	with _ -> None in
      begin match get_args () with
      | Some (t,f,a,min,max) ->
	  if Uint31.lt min max then
	    let p = PRIMITIVE(op,c,[||]) in
	    let pstk = 
	      APP([|t;f;a;
		    VNativeEntries.mkInt env 
		      (Uint31.add min (Uint31.of_int 1));
		    VNativeEntries.get args 4|],TOP) in
	    let fold = cbv_val_stack info (p,pstk) in
	    Inl (f,stack_app  [|VNativeEntries.get args 3;fold|] stk)
	  else if Uint31.eq min max then
	    Inl (f,stack_app [|VNativeEntries.get args 3;a|] stk)
	  else Inl (a,stk)
      | None -> Inr(mkSTACK(PRIMITIVE(op,c,args), stk))
      end
  | Oiterator Int31foldi_down ->
      let get_args () =
	try 
	  let t = VNativeEntries.get args 0 in
	  let f = VNativeEntries.get args 1 in
	  let a = VNativeEntries.get args 2 in
	  let min = VNativeEntries.get_int (VNativeEntries.get args 3) in
	  let max =  VNativeEntries.get_int (VNativeEntries.get args 4) in
	  Some (t,f,a,min,max)
	with _ -> None in
      begin match get_args () with
      | Some (t,f,a,min,max) ->
	  if Uint31.lt min max then
	    let p = PRIMITIVE(op,c,[||]) in
	    let pstk = 
	      APP([|t;f;a;VNativeEntries.get args 3;
		    VNativeEntries.mkInt env 
		      (Uint31.sub max (Uint31.of_int 1));
		  |],TOP) in
	    let fold = cbv_val_stack info (p,pstk) in
	    Inl (f,stack_app  [|VNativeEntries.get args 4;fold|] stk)
	  else if Uint31.eq min max then
	    Inl (f,stack_app [|VNativeEntries.get args 3;a|] stk)
	  else Inl (a,stk)
      | None -> Inr(mkSTACK(PRIMITIVE(op,c,args), stk))
      end
 *)   
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
      map_constr_with_binders subs_lift (cbv_norm_term info) env t
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
  | NATIVEINT i -> mkInt i
  | NATIVEARR(t,p) ->
      let ct = cbv_norm_value info t in
      let len = Uint31.to_int (Native.Parray.length p) in
      let cdef = cbv_norm_value info (Parray.default p) in
      let cp = Array.create (len + 1) cdef in  
      for i = 0 to len - 1 do
	cp.(i) <- cbv_norm_value info (Parray.get p (Uint31.of_int i))
      done;
      mkArray(ct, cp)
  | PRIMITIVE(op,c,args) ->
      mkApp(c,Array.map (cbv_norm_value info) args)

(* with profiling *)
let cbv_norm infos constr =
  with_stats (lazy (cbv_norm_term infos (ESID 0) constr))

type cbv_infos = cbv_value infos

(* constant bodies are normalized at the first expansion *)
let create_cbv_infos flgs env sigma =
  create
    (fun old_info c -> cbv_stack_term old_info TOP (ESID 0) c)
    flgs
    env
    (Reductionops.safe_evar_value sigma)
