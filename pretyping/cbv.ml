(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Vars
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
 *  LAMBDA(n,a,b,S) is the term [S]([x:a]b) where [a] is a list of bindings and
 *          [n] is the length of [a]. the environment [S] is propagated
 *          only when the abstraction is applied, and then we use the rule
 *                  ([S]([x:a]b) c) --> [S.c]b
 *          This corresponds to the usual strategy of weak reduction
 *  PROD(na,t,u,S) is the term [S](forall na:t, u).
 *  LETIN(na,b,t,S) is the term [S](let na:= b : t in.c).
 *  FIX(op,bd,S,args) is the fixpoint (Fix or Cofix) of bodies bd under
 *          the bindings S, and then applied to args. Here again,
 *          weak reduction.
 *  CONSTRUCT(c,args) is the constructor [c] applied to [args].
 *  PRIMITIVE(cop,args) represent a particial application of
 *          a primitive, or a fully applied primitive
 *          which does not reduce.
 *          cop is the constr representing op.
 *
 *)
type cbv_value =
  | VAL of int * constr
  | STACK of int * cbv_value * cbv_stack
  | LAMBDA of int * (Name.t Constr.binder_annot * types) list * constr * cbv_value subs
  | PROD of Name.t Constr.binder_annot * types * types * cbv_value subs
  | LETIN of Name.t Constr.binder_annot * cbv_value * types * constr * cbv_value subs
  | FIX of fixpoint * cbv_value subs * cbv_value array
  | COFIX of cofixpoint * cbv_value subs * cbv_value array
  | CONSTRUCT of constructor UVars.puniverses * cbv_value array
  | PRIMITIVE of CPrimitives.t * pconstant * cbv_value array
  | ARRAY of UVars.Instance.t * cbv_value Parray.t * cbv_value
  | SYMBOL of { cst: Constant.t UVars.puniverses; unfoldfix: bool; rules: Declarations.rewrite_rule list; stk: cbv_stack }

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
  | APP of cbv_value list * cbv_stack
  | CASE of UVars.Instance.t * constr array * case_return * case_branch array * Constr.case_invert * case_info * cbv_value subs * cbv_stack
  | PROJ of Projection.t * Sorts.relevance * cbv_stack

(* les vars pourraient etre des constr,
   cela permet de retarder les lift: utile ?? *)

(* relocation of a value; used when a value stored in a context is expanded
 * in a larger context. e.g.  [%k (S.t)](k+1) --> [^k]t  (t is shifted of k)
 *)
let rec shift_value n = function
  | VAL (k,t) -> VAL (k+n,t)
  | STACK(k,v,stk) -> STACK(k+n,v,stk)
  | PROD (na,t,u,s) -> PROD(na,t,u,subs_shft(n,s))
  | LETIN (na,b,t,c,s) -> LETIN(na,shift_value n b,t,c,subs_shft(n,s))
  | LAMBDA (nlams,ctxt,b,s) -> LAMBDA (nlams,ctxt,b,subs_shft (n,s))
  | FIX (fix,s,args) ->
      FIX (fix,subs_shft (n,s), Array.map (shift_value n) args)
  | COFIX (cofix,s,args) ->
      COFIX (cofix,subs_shft (n,s), Array.map (shift_value n) args)
  | CONSTRUCT (c,args) ->
      CONSTRUCT (c, Array.map (shift_value n) args)
  | PRIMITIVE(op,c,args) ->
      PRIMITIVE(op,c,Array.map (shift_value n) args)
  | ARRAY (u,t,ty) ->
      ARRAY(u, Parray.map (shift_value n) t, shift_value n ty)
  | SYMBOL s -> SYMBOL { s with stk = shift_stack n s.stk }

and shift_stack n = function (* Slow *)
  | TOP -> TOP
  | APP (args, stk) -> APP (List.map (shift_value n) args, shift_stack n stk)
  | CASE (u,pms,c,b,iv,i,s,stk) -> CASE (u,pms,c,b,iv,i,subs_shft(n,s), shift_stack n stk)
  | PROJ (p, r, stk) -> PROJ (p, r, shift_stack n stk)

let shift_value n v =
  if Int.equal n 0 then v else shift_value n v

(* Contracts a fixpoint: given a fixpoint and a bindings,
 * returns the corresponding fixpoint body, and the bindings in which
 * it should be evaluated: its first variables are the fixpoint bodies
 * (S, (fix Fi {F0 := T0 .. Fn-1 := Tn-1}))
 *    -> (S. [S]F0 . [S]F1 ... . [S]Fn-1, Ti)
 *)

let rec mk_fix_subs make_body n env i =
  if Int.equal i n then env
  else mk_fix_subs make_body n (subs_cons (make_body i) env) (i + 1)

let contract_fixp env ((reci,i),(_,_,bds as bodies)) =
  let make_body j = FIX(((reci,j),bodies), env, [||]) in
  let n = Array.length bds in
  mk_fix_subs make_body n env 0, bds.(i)

let contract_cofixp env (i,(_,_,bds as bodies)) =
  let make_body j = COFIX((j,bodies), env, [||]) in
  let n = Array.length bds in
  mk_fix_subs make_body n env 0, bds.(i)

let make_constr_ref n k t =
  match k with
  | RelKey p -> mkRel (n+p)
  | VarKey id -> t
  | ConstKey cst -> t

(* Adds an application list. Collapse APPs! *)
let stack_vect_app appl stack =
  if Int.equal (Array.length appl) 0 then stack else
    match stack with
    | APP(args,stk) -> APP(Array.fold_right (fun v accu -> v :: accu) appl args,stk)
    | _             -> APP(Array.to_list appl, stack)

let stack_app appl stack =
  if List.is_empty appl then stack else
    match stack with
    | APP(args,stk) -> APP(appl @ args,stk)
    | _             -> APP(appl, stack)

let rec stack_concat stk1 stk2 =
  match stk1 with
      TOP -> stk2
    | APP(v,stk1') -> APP(v,stack_concat stk1' stk2)
    | CASE(u,pms,c,b,iv,i,s,stk1') -> CASE(u,pms,c,b,iv,i,s,stack_concat stk1' stk2)
    | PROJ (p,r,stk1') -> PROJ (p,r,stack_concat stk1' stk2)

(* merge stacks when there is no shifts in between *)
let mkSTACK = function
    v, TOP -> v
  | STACK(0,v0,stk0), stk -> STACK(0,v0,stack_concat stk0 stk)
  | v,stk -> STACK(0,v,stk)

module KeyTable = Hashtbl.Make(struct
  type t = Constant.t UVars.puniverses tableKey
  let equal = Names.eq_table_key (eq_pair eq_constant_key UVars.Instance.equal)
  let hash = Names.hash_table_key (fun (c, _) -> Constant.UserOrd.hash c)
end)

type cbv_infos = {
  env : Environ.env;
  tab : (cbv_value, Empty.t, bool * Declarations.rewrite_rule list) Declarations.constant_def KeyTable.t;
  reds : RedFlags.reds;
  sigma : Evd.evar_map;
  strong : bool;
}

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
    | FIX (fix,env,app) -> (FIX(fix,env,[||]), stack_vect_app app stack)
    | COFIX (cofix,env,app) -> (COFIX(cofix,env,[||]), stack_vect_app app stack)
    | CONSTRUCT (c,app) -> (CONSTRUCT(c,[||]), stack_vect_app app stack)
    | PRIMITIVE(op,c,app) -> (PRIMITIVE(op,c,[||]), stack_vect_app app stack)
    | LETIN _ | VAL _ | STACK _ | PROD _ | LAMBDA _ | ARRAY _ | SYMBOL _ -> (head, stack)

let destack head stack =
  match head with
  | FIX (fix,env,app) -> (FIX(fix,env,[||]), stack_vect_app app stack)
  | COFIX (cofix,env,app) -> (COFIX(cofix,env,[||]), stack_vect_app app stack)
  | CONSTRUCT (c,app) -> (CONSTRUCT(c,[||]), stack_vect_app app stack)
  | PRIMITIVE(op,c,app) -> (PRIMITIVE(op,c,[||]), stack_vect_app app stack)
  | STACK (k, v, stk) -> (shift_value k v, stack_concat (shift_stack k stk) stack)
  | SYMBOL ({ stk } as s) -> (SYMBOL { s with stk=TOP }, stack_concat stk stack)
  | LETIN _ | VAL _ | PROD _ | LAMBDA _ | ARRAY _ -> (head, stack)

let rec fixp_reducible_symb_stk = function
  | TOP -> true
  | APP (_, stk) -> fixp_reducible_symb_stk stk
  | CASE _ | PROJ _ -> false

(* Tests if fixpoint reduction is possible. *)
let fixp_reducible flgs ((reci,i),_) stk =
  if red_set flgs fFIX then
    match stk with
      | APP(appl,_) ->
        let rec check n = function
        | [] -> false
        | v :: appl ->
          if Int.equal n 0 then match v with
          | CONSTRUCT _ -> true
          | SYMBOL { unfoldfix=true; stk; _ } ->
              fixp_reducible_symb_stk stk
          | _ -> false
          else check (n - 1) appl
        in
        check reci.(i) appl
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

let debug_cbv = CDebug.create ~name:"Cbv" ()

(* Reduction of primitives *)

open Primred

module VNativeEntries =
  struct

    type elem = cbv_value
    type args = cbv_value array
    type evd = unit
    type uinstance = UVars.Instance.t

    let get = Array.get

    let get_int () e =
      match e with
      | VAL(_, ci) ->
          (match kind ci with
          | Int i -> i
          | _ -> raise Primred.NativeDestKO)
      | _ -> raise Primred.NativeDestKO

    let get_float () e =
      match e with
      | VAL(_, cf) ->
        (match kind cf with
        | Float f -> f
        | _ -> raise Primred.NativeDestKO)
      | _ -> raise Primred.NativeDestKO

    let get_string () e =
      match e with
      | VAL(_, cf) ->
        (match kind cf with
        | String s -> s
        | _ -> raise Primred.NativeDestKO)
      | _ -> raise Primred.NativeDestKO

    let get_parray () e =
      match e with
      | ARRAY(_u,t,_ty) -> t
      | _ -> raise Primred.NativeDestKO

    let mkInt env i = VAL(0, mkInt i)

    let mkFloat env f = VAL(0, mkFloat f)

    let mkString env s = VAL(0, mkString s)

    let mkBool env b =
      let (ct,cf) = get_bool_constructors env in
      CONSTRUCT(UVars.in_punivs (if b then ct else cf), [||])

    let int_ty env = VAL(0, UnsafeMonomorphic.mkConst @@ get_int_type env)

    let float_ty env = VAL(0, UnsafeMonomorphic.mkConst @@ get_float_type env)

    let mkCarry env b e =
      let (c0,c1) = get_carry_constructors env in
      CONSTRUCT(UVars.in_punivs (if b then c1 else c0), [|int_ty env;e|])

    let mkIntPair env e1 e2 =
      let int_ty = int_ty env in
      let c = get_pair_constructor env in
      CONSTRUCT(UVars.in_punivs c, [|int_ty;int_ty;e1;e2|])

    let mkFloatIntPair env f i =
      let float_ty = float_ty env in
      let int_ty = int_ty env in
      let c = get_pair_constructor env in
      CONSTRUCT(UVars.in_punivs c, [|float_ty;int_ty;f;i|])

    let mkLt env =
      let (_eq,lt,_gt) = get_cmp_constructors env in
      CONSTRUCT(UVars.in_punivs lt, [||])

    let mkEq env =
      let (eq,_lt,_gt) = get_cmp_constructors env in
      CONSTRUCT(UVars.in_punivs eq, [||])

    let mkGt env =
      let (_eq,_lt,gt) = get_cmp_constructors env in
      CONSTRUCT(UVars.in_punivs gt, [||])

    let mkFLt env =
      let (_eq,lt,_gt,_nc) = get_f_cmp_constructors env in
      CONSTRUCT(UVars.in_punivs lt, [||])

    let mkFEq env =
      let (eq,_lt,_gt,_nc) = get_f_cmp_constructors env in
      CONSTRUCT(UVars.in_punivs eq, [||])

    let mkFGt env =
      let (_eq,_lt,gt,_nc) = get_f_cmp_constructors env in
      CONSTRUCT(UVars.in_punivs gt, [||])

    let mkFNotComparable env =
      let (_eq,_lt,_gt,nc) = get_f_cmp_constructors env in
      CONSTRUCT(UVars.in_punivs nc, [||])

    let mkPNormal env =
      let (pNormal,_nNormal,_pSubn,_nSubn,_pZero,_nZero,_pInf,_nInf,_nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs pNormal, [||])

    let mkNNormal env =
      let (_pNormal,nNormal,_pSubn,_nSubn,_pZero,_nZero,_pInf,_nInf,_nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs nNormal, [||])

    let mkPSubn env =
      let (_pNormal,_nNormal,pSubn,_nSubn,_pZero,_nZero,_pInf,_nInf,_nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs pSubn, [||])

    let mkNSubn env =
      let (_pNormal,_nNormal,_pSubn,nSubn,_pZero,_nZero,_pInf,_nInf,_nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs nSubn, [||])

    let mkPZero env =
      let (_pNormal,_nNormal,_pSubn,_nSubn,pZero,_nZero,_pInf,_nInf,_nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs pZero, [||])

    let mkNZero env =
      let (_pNormal,_nNormal,_pSubn,_nSubn,_pZero,nZero,_pInf,_nInf,_nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs nZero, [||])

    let mkPInf env =
      let (_pNormal,_nNormal,_pSubn,_nSubn,_pZero,_nZero,pInf,_nInf,_nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs pInf, [||])

    let mkNInf env =
      let (_pNormal,_nNormal,_pSubn,_nSubn,_pZero,_nZero,_pInf,nInf,_nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs nInf, [||])

    let mkNaN env =
      let (_pNormal,_nNormal,_pSubn,_nSubn,_pZero,_nZero,_pInf,_nInf,nan) =
        get_f_class_constructors env in
      CONSTRUCT(UVars.in_punivs nan, [||])

    let mkArray env u t ty =
      ARRAY (u,t,ty)
  end

module VredNative = RedNative(VNativeEntries)

let debug_pr_key = function
  | ConstKey (sp,_) -> Names.Constant.print sp
  | VarKey id -> Names.Id.print id
  | RelKey n -> Pp.(str "REL_" ++ int n)

let rec reify_stack t = function
  | TOP -> t
  | APP (args,st) ->
      reify_stack (mkApp(t,Array.map_of_list reify_value args)) st
  | CASE (u,pms,ty,br,iv,ci,env,st) ->
      reify_stack
        (apply_env env @@ mkCase (ci, u, pms, ty, iv, t,br))
        st
  | PROJ (p, r, st) ->
       reify_stack (mkProj (p, r, t)) st

and reify_value = function (* reduction under binders *)
  | VAL (n,t) -> lift n t
  | STACK (0,v,stk) ->
      reify_stack (reify_value v) stk
  | STACK (n,v,stk) ->
      lift n (reify_stack (reify_value v) stk)
  | PROD(na,t,u,env) ->
    apply_env env (mkProd (na,t,u))
  | LETIN(na,b,t,c,env) ->
    apply_env env (mkLetIn (na,reify_value b,t,c))
  | LAMBDA (k,ctxt,b,env) ->
    apply_env env @@
    List.fold_left (fun c (n,t) ->
        mkLambda (n, t, c)) b ctxt
  | FIX ((lij,fix),env,args) ->
    let fix = mkFix (lij, fix) in
    mkApp (apply_env env fix, Array.map reify_value args)
  | COFIX ((j,cofix),env,args) ->
    let cofix = mkCoFix (j, cofix) in
    mkApp (apply_env env cofix, Array.map reify_value args)
  | CONSTRUCT (c,args) ->
      mkApp(mkConstructU c, Array.map reify_value args)
  | PRIMITIVE(op,c,args) ->
      mkApp(mkConstU c, Array.map reify_value args)
  | ARRAY (u,t,ty) ->
    let t, def = Parray.to_array t in
      mkArray(u, Array.map reify_value t, reify_value def, reify_value ty)
  | SYMBOL { cst; stk; _ } ->
      reify_stack (mkConstU cst) stk

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

let apply_env_context e ctx =
  let open Context.Rel.Declaration in
  let rec subst_context ctx = match ctx with
  | [] -> e, []
  | LocalAssum (na, ty) :: ctx ->
    let e, ctx = subst_context ctx in
    let ty = apply_env e ty in
    subs_lift e, LocalAssum (na, ty) :: ctx
  | LocalDef (na, ty, bdy) :: ctx ->
    let e, ctx = subst_context ctx in
    let ty = apply_env e ty in
    let bdy = apply_env e bdy in
    subs_lift e, LocalDef (na, ty, bdy) :: ctx
  in
  snd @@ subst_context ctx

let rec strip_app = function
  | APP (args,st) -> APP (args,strip_app st)
  | s -> TOP

(* TODO: share the common parts with EConstr *)
let expand_branch env u pms (ind, i) br =
  let open Declarations in
  let nas, _br = br.(i - 1) in
  let (mib, mip) = Inductive.lookup_mind_specif env ind in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl pms in
  let (ctx, _) = mip.mind_nf_lc.(i - 1) in
  let (ctx, _) = List.chop mip.mind_consnrealdecls.(i - 1) ctx in
  Inductive.instantiate_context u paramsubst nas ctx

let cbv_subst_of_rel_context_instance_list mkclos sign args env =
  let rec aux subst sign l =
    let open Context.Rel.Declaration in
    match sign, l with
    | LocalAssum _ :: sign', a::args' -> aux (subs_cons a subst) sign' args'
    | LocalDef (_,c,_)::sign', args' ->
        aux (subs_cons (mkclos subst c) subst) sign' args'
    | [], [] -> subst
    | _ -> CErrors.anomaly (Pp.str "Instance and signature do not match.")
  in aux env (List.rev sign) args

(* The main recursive functions
 *
 * Go under applications and cases/projections (pushed in the stack),
 * expand head constants or substitued de Bruijn, and try to a make a
 * constructor, a lambda or a fixp appear in the head. If not, it is a value
 * and is completely computed here. The head redexes are NOT reduced:
 * the function returns the pair of a cbv_value and its stack.  *
 * Invariant: if the result of norm_head is CONSTRUCT or (CO)FIX, its last
 * argument is [].  Because we must put all the applied terms in the
 * stack. *)

exception PatternFailure

let rec norm_head info env t stack =
  (* no reduction under binders *)
  match kind t with
  (* stack grows (remove casts) *)
  | App (head,args) -> (* Applied terms are normalized immediately;
                        they could be computed when getting out of the stack *)
    let fold c accu = cbv_stack_term info TOP env c :: accu in
    let rem, stack = match stack with
    | APP (nargs, stack) -> nargs, stack
    | _ -> [], stack
    in
    let stack = APP (Array.fold_right fold args rem, stack) in
    norm_head info env head stack
  | Case (ci,u,pms,p,iv,c,v) -> norm_head info env c (CASE(u,pms,p,v,iv,ci,env,stack))
  | Cast (ct,_,_) -> norm_head info env ct stack

  | Proj (p, r, c) ->
    let p' =
      if red_set info.reds (fPROJ (Projection.repr p))
      then Projection.unfold p
      else p
    in
      norm_head info env c (PROJ (p', r, stack))

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

  | Const sp ->
    Reductionops.reduction_effect_hook info.env info.sigma
      (fst sp) (lazy (reify_stack t (strip_app stack)));
    norm_head_ref 0 info env stack (ConstKey sp) t

  | LetIn (na, b, u, c) ->
      (* zeta means letin are contracted; delta without zeta means we *)
      (* allow bindings but leave let's in place *)
      if red_set info.reds fZETA then
        (* New rule: for Cbv, Delta does not apply to locally bound variables
           or red_set info.reds fDELTA
         *)
        let env' = subs_cons (cbv_stack_term info TOP env b) env in
        norm_head info env' c stack
      else
        (* Note: we may also consider a commutative cut! *)
        LETIN(na,cbv_stack_term info TOP env b,u,c,env), stack

  | Evar ((e, _) as ev) ->
      (match Evd.existential_opt_value0 info.sigma ev with
          Some c -> norm_head info env c stack
        | None ->
          let ev = EConstr.of_existential ev in
          let map c = EConstr.of_constr @@ apply_env env (EConstr.Unsafe.to_constr c) in
          let ev' = EConstr.map_existential info.sigma map ev in
          (VAL(0, EConstr.Unsafe.to_constr @@ EConstr.mkEvar ev'), stack))

  (* non-neutral cases *)
  | Lambda _ ->
      let ctxt,b = Term.decompose_lambda t in
      (LAMBDA(List.length ctxt, List.rev ctxt,b,env), stack)
  | Fix fix -> (FIX(fix,env,[||]), stack)
  | CoFix cofix -> (COFIX(cofix,env,[||]), stack)
  | Construct c -> (CONSTRUCT(c, [||]), stack)

  | Array(u,t,def,ty) ->
    let ty = cbv_stack_term info TOP env ty in
    let len = Array.length t in
    let t =
      Parray.init (Uint63.of_int len)
      (fun i -> cbv_stack_term info TOP env t.(i))
      (cbv_stack_term info TOP env def) in
    (ARRAY (u,t,ty), stack)

  (* neutral cases *)
  | (Sort _ | Meta _ | Ind _ | Int _ | Float _ | String _) -> (VAL(0, t), stack)
  | Prod (na,t,u) -> (PROD(na,t,u,env), stack)

and norm_head_ref k info env stack normt t =
  if red_set_ref info.reds normt then
    match cbv_value_cache info normt with
      | Declarations.Def body ->
         debug_cbv (fun () -> Pp.(str "Unfolding " ++ debug_pr_key normt));
         strip_appl (shift_value k body) stack
      | Declarations.Primitive op ->
        let c = match normt with
          | ConstKey c -> c
          | RelKey _ | VarKey _ -> assert false
        in
        (PRIMITIVE(op,c,[||]),stack)
      | Declarations.Symbol (unfoldfix, rules) ->
        assert (k = 0);
        let cst = match normt with
          | ConstKey c -> c
          | RelKey _ | VarKey _ -> assert false
        in
        (SYMBOL { cst; unfoldfix; rules; stk=TOP }, stack)
      | Declarations.OpaqueDef _ | Declarations.Undef _ ->
         debug_cbv (fun () -> Pp.(str "Not unfolding " ++ debug_pr_key normt));
         (VAL(0,make_constr_ref k normt t),stack)
  else
    begin
      debug_cbv (fun () -> Pp.(str "Not unfolding " ++ debug_pr_key normt));
      (VAL(0,make_constr_ref k normt t),stack)
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
  | (LAMBDA (nlams,ctxt,b,env), APP (args, stk))
      when red_set info.reds fBETA ->
    let rec apply env lams args =
      if Int.equal lams 0 then
        let stk = if List.is_empty args then stk else APP (args, stk) in
        cbv_stack_term info stk env b
      else match args with
      | [] ->
        let ctxt' = List.skipn (nlams - lams) ctxt in
        LAMBDA (lams, ctxt', b, env)
      | v :: args ->
        let env = subs_cons v env in
        apply env (lams - 1) args
    in
    apply env nlams args
    (* a Fix applied enough -> IOTA *)
    | (FIX(fix,env,[||]), stk)
        when fixp_reducible info.reds fix stk ->
        let (envf,redfix) = contract_fixp env fix in
        cbv_stack_term info stk envf redfix

    (* constructor guard satisfied or Cofix in a Case -> IOTA *)
    | (COFIX(cofix,env,[||]), stk)
        when cofixp_reducible info.reds cofix stk->
        let (envf,redfix) = contract_cofixp env cofix in
        cbv_stack_term info stk envf redfix

    (* constructor in a Case -> IOTA *)
    | (CONSTRUCT(((sp,n),_),[||]), APP(args,CASE(u,pms,_p,br,iv,ci,env,stk)))
            when red_set info.reds fMATCH ->
        let cargs = List.skipn ci.ci_npar args in
        let env =
          if (Int.equal ci.ci_cstr_ndecls.(n - 1) ci.ci_cstr_nargs.(n - 1)) then (* no lets *)
            List.fold_left (fun accu v -> subs_cons v accu) env cargs
          else
            let mkclos env c = cbv_stack_term info TOP env c in
            let ctx = expand_branch info.env u pms (sp, n) br in
            cbv_subst_of_rel_context_instance_list mkclos ctx cargs env
        in
        cbv_stack_term info stk env (snd br.(n-1))

    (* constructor of arity 0 in a Case -> IOTA *)
    | (CONSTRUCT(((sp, n), _),[||]), CASE(u,pms,_,br,_,ci,env,stk))
            when red_set info.reds fMATCH ->
        let env =
          if (Int.equal ci.ci_cstr_ndecls.(n - 1) ci.ci_cstr_nargs.(n - 1)) then (* no lets *)
            env
          else
            let mkclos env c = cbv_stack_term info TOP env c in
            let ctx = expand_branch info.env u pms (sp, n) br in
            cbv_subst_of_rel_context_instance_list mkclos ctx [] env
        in
        cbv_stack_term info stk env (snd br.(n-1))

    (* constructor in a Projection -> IOTA *)
    | (CONSTRUCT(((sp,n),u),[||]), APP(args,PROJ(p,_,stk)))
        when red_set info.reds fMATCH && Projection.unfolded p ->
      let arg = List.nth args (Projection.npars p + Projection.arg p) in
        cbv_stack_value info env (strip_appl arg stk)

    (* may be reduced later by application *)
    | (FIX(fix,env,[||]), APP(appl,TOP)) -> FIX(fix,env,Array.of_list appl)
    | (COFIX(cofix,env,[||]), APP(appl,TOP)) -> COFIX(cofix,env,Array.of_list appl)
    | (CONSTRUCT(c,[||]), APP(appl,TOP)) -> CONSTRUCT(c,Array.of_list appl)

    (* primitive apply to arguments *)
    | (PRIMITIVE(op,(_,u as c),[||]), APP(appl,stk)) ->
      let nargs = CPrimitives.arity op in
      begin match List.chop nargs appl with
      | (args, appl) ->
        let stk = if List.is_empty appl then stk else stack_app appl stk in
        begin match VredNative.red_prim info.env () op u (Array.of_list args) with
        | Some (CONSTRUCT (c, args)) ->
          (* args must be moved to the stack to allow future reductions *)
          cbv_stack_value info env (CONSTRUCT(c, [||]), stack_vect_app args stk)
        | Some v ->  cbv_stack_value info env (v,stk)
        | None -> mkSTACK(PRIMITIVE(op,c,Array.of_list args), stk)
        end
      | exception Failure _ ->
        (* partial application *)
              (assert (stk = TOP);
               PRIMITIVE(op,c,Array.of_list appl))
        end
    | SYMBOL ({ cst; rules; stk } as s ), stk' ->
        let stk = stack_concat stk stk' in
        begin try
          let rhs, stack = cbv_apply_rules info env (snd cst) rules stk in
          cbv_stack_value info env (destack rhs stack)
        with PatternFailure ->
          SYMBOL { s with stk }
        end

    (* definitely a value *)
    | (head,stk) -> mkSTACK(head, stk)

and cbv_value_cache info ref =
  try KeyTable.find info.tab ref with
    Not_found ->
    let v =
      try
        let body = match ref with
          | RelKey n ->
            let open Context.Rel.Declaration in
            begin match Environ.lookup_rel n info.env with
              | LocalDef (_, c, _) -> lift n c
              | LocalAssum _ -> raise Not_found
            end
          | VarKey id ->
            let open Context.Named.Declaration in
            begin match Environ.lookup_named id info.env with
              | LocalDef (_, c, _) -> c
              | LocalAssum _ -> raise Not_found
            end
          | ConstKey cst -> Environ.constant_value_in info.env cst
        in
        let v = cbv_stack_term info TOP (subs_id 0) body in
        Declarations.Def v
      with
      | Environ.NotEvaluableConst (Environ.IsPrimitive (_u,op)) -> Declarations.Primitive op
      | Environ.NotEvaluableConst (Environ.HasRules (u, b, r)) -> Declarations.Symbol (b, r)
      | Not_found | Environ.NotEvaluableConst _ -> Declarations.Undef None
    in
    KeyTable.add info.tab ref v; v


and it_mkLambda_or_LetIn info ctx t =
  let open Context.Rel.Declaration in
  match List.rev ctx with
  | [] -> t
  | LocalAssum (n, ty) :: ctx ->
      let assums, ctx = List.map_until (function LocalAssum (n, ty) -> Some (n, ty) | LocalDef _ -> None) ctx in
      let assums = (n, ty) :: assums in
      LAMBDA (List.length assums, assums, Term.it_mkLambda_or_LetIn (reify_value t) (List.rev ctx), subs_id 0)
  | LocalDef _ :: _ ->
      cbv_stack_term info TOP (subs_id 0) (Term.it_mkLambda_or_LetIn (reify_value t) ctx)

and cbv_match_arg_pattern info env ctx psubst p t =
  let open Declarations in
  let t' = it_mkLambda_or_LetIn info ctx t in
  match p with
  | EHole i -> Partial_subst.add_term i t' psubst
  | EHoleIgnored -> psubst
  | ERigid (ph, es) ->
      let t, stk = destack t TOP in
      let psubst = cbv_match_rigid_arg_pattern info env ctx psubst ph t in
      let psubst, stk = cbv_apply_rule info env ctx psubst es stk in
      match stk with
      | TOP -> psubst
      | APP _| CASE _ | PROJ _ -> raise PatternFailure

and cbv_match_arg_pattern_lift info env ctx n psubst p t =
  let env = subs_liftn n env in
  cbv_match_arg_pattern info env ctx psubst p
    (cbv_stack_term info TOP env t)

and match_sort ps s subst =
  match Sorts.pattern_match ps s subst with
  | Some subst -> subst
  | None -> raise PatternFailure

and match_instance pu u psubst =
  match UVars.Instance.pattern_match pu u psubst with
  | Some subst -> subst
  | None -> raise PatternFailure


and cbv_match_rigid_arg_pattern info env ctx psubst p t =
  let open Declarations in
  match [@ocaml.warning "-4"] p, t with
  | PHInd (ind, pu), VAL(0, t') ->
    begin match kind t' with Ind (ind', u) when Environ.QInd.equal info.env ind ind' -> match_instance pu u psubst | _ -> raise PatternFailure end
  | PHConstr (constr, pu), CONSTRUCT ((constr', u), [||]) ->
    if Environ.QConstruct.equal info.env constr constr' then match_instance pu u psubst else raise PatternFailure
  | PHRel i, VAL(k, t') ->
    begin match kind t' with Rel n when Int.equal i (k + n) -> psubst | _ -> raise PatternFailure end
  | PHSort ps, VAL(0, t') ->
    begin match kind t' with Sort s -> match_sort ps s psubst | _ -> raise PatternFailure end
  | PHSymbol (c, pu), SYMBOL { cst = c', u; _ } ->
    if Environ.QConstant.equal info.env c c' then match_instance pu u psubst else raise PatternFailure
  | PHInt i, VAL(0, t') ->
    begin match kind t' with Int i' when Uint63.equal i i' -> psubst | _ -> raise PatternFailure end
  | PHFloat f, VAL(0, t') ->
    begin match kind t' with Float f' when Float64.equal f f' -> psubst | _ -> raise PatternFailure end
  | PHString s, VAL(0, t') ->
    begin match kind t' with String s' when Pstring.equal s s' -> psubst | _ -> raise PatternFailure end
  | PHLambda (ptys, pbod), LAMBDA (nlam, ntys, body, env) ->
    let np = Array.length ptys in
    if np > nlam then raise PatternFailure;
    let ntys, body =
      if np = nlam then ntys, body
      else (* np < nlam *)
        let ntys, tys' = List.chop np ntys in
        ntys, Term.compose_lam (List.rev tys') body
    in
    let ctx' = List.rev_map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys in
    let ctx' = apply_env_context env ctx' in
    let tys = Array.of_list ntys in
    let contexts_upto = Array.init np (fun i -> List.lastn i ctx' @ ctx) in
    let psubst = Array.fold_left3_i (fun i psubst ctx pty (_, ty) -> cbv_match_arg_pattern_lift info env ctx i psubst pty ty) psubst contexts_upto ptys tys in
    let psubst = cbv_match_arg_pattern_lift info env (ctx' @ ctx) np psubst pbod body in
    psubst
  | PHProd (ptys, pbod), PROD (na, ty, body, env) ->
    let ntys, _ = Term.decompose_prod body in
    let np = Array.length ptys in
    let nprod = 1 + List.length ntys in
    if np > nprod then raise PatternFailure;
    let ntys, body = Term.decompose_prod_n (np-1) body in
    let ctx' = List.map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) (ntys @ [na, ty]) in
    let ctx' = apply_env_context env ctx' in
    let tys = Array.of_list ((na, ty) :: List.rev ntys) in
    let na = Array.length tys in
    let contexts_upto = Array.init na (fun i -> List.lastn i ctx' @ ctx) in
    let psubst = Array.fold_left3_i (fun i psubst ctx pty (_, ty) -> cbv_match_arg_pattern_lift info env ctx i psubst pty ty) psubst contexts_upto ptys tys in
    let psubst = cbv_match_arg_pattern_lift info env (ctx' @ ctx) na psubst pbod body in
    psubst
  | (PHInd _ | PHConstr _ | PHRel _ | PHInt _ | PHFloat _ | PHString _ | PHSort _ | PHSymbol _ | PHLambda _ | PHProd _), _ -> raise PatternFailure


and cbv_apply_rule info env ctx psubst es stk =
  match [@ocaml.warning "-4"] es, stk with
  | [], _ -> psubst, stk
  | Declarations.PEApp pargs :: e, APP (args, s) ->
      let args = Array.of_list args in
      let np = Array.length pargs in
      let na = Array.length args in
      if np == na then
        let psubst = Array.fold_left2 (cbv_match_arg_pattern info env ctx) psubst pargs args in
        cbv_apply_rule info env ctx psubst e s
      else if np < na then (* more real arguments *)
        let usedargs, remargs = Array.chop np args in
        let psubst = Array.fold_left2 (cbv_match_arg_pattern info env ctx) psubst pargs usedargs in
        cbv_apply_rule info env ctx psubst e (APP (Array.to_list remargs, s))
      else (* more pattern arguments *)
        let usedpargs, rempargs = Array.chop na pargs in
        let psubst = Array.fold_left2 (cbv_match_arg_pattern info env ctx) psubst usedpargs args in
        cbv_apply_rule info env ctx psubst (PEApp rempargs :: e) s
  | Declarations.PECase (pind, pu, pret, pbrs) :: e, CASE (u, pms, (p, _), brs, iv, ci, env, s) ->
      if not @@ Environ.QInd.equal info.env pind ci.ci_ind then raise PatternFailure;
      let specif = Inductive.lookup_mind_specif info.env ci.ci_ind in
      let ntys_ret = Inductive.expand_arity specif (ci.ci_ind, u) pms (fst p) in
      let ntys_ret = apply_env_context env ntys_ret in
      let ntys_brs = Inductive.expand_branch_contexts specif u pms brs in
      let psubst = match_instance pu u psubst in
      let brs = Array.map2 (fun ctx' br -> List.length ctx', ctx' @ ctx, (snd br)) ntys_brs brs in
      let psubst = cbv_match_arg_pattern_lift info env (ntys_ret @ ctx) (List.length ntys_ret) psubst pret (snd p) in
      let psubst = Array.fold_left2 (fun psubst pat (n, ctx, br) -> cbv_match_arg_pattern_lift info env (apply_env_context env ctx) n psubst pat br) psubst pbrs brs in
      cbv_apply_rule info env ctx psubst e s
  | Declarations.PEProj proj :: e, PROJ (proj', r, s) ->
      if not @@ Environ.QProjection.Repr.equal info.env proj (Projection.repr proj') then raise PatternFailure;
      cbv_apply_rule info env ctx psubst e s
  | _, _ -> raise PatternFailure


and cbv_apply_rules info env u r stk =
  match r with
  | [] -> raise PatternFailure
  | { lhs_pat = (pu, elims); nvars; rhs } :: rs ->
    try
      let psubst = Partial_subst.make nvars in
      let psubst = match_instance pu u psubst in
      let psubst, stk = cbv_apply_rule info env [] psubst elims stk in
      let subst, qsubst, usubst = Partial_subst.to_arrays psubst in
      let subst = Array.fold_right subs_cons subst env in
      let usubst = UVars.Instance.of_array (qsubst, usubst) in
      let rhsu = Vars.subst_instance_constr usubst rhs in
      let rhs' = cbv_stack_term info TOP subst rhsu in
      rhs', stk
    with PatternFailure -> cbv_apply_rules info env u rs stk




(* When we are sure t will never produce a redex with its stack, we
 * normalize (even under binders) the applied terms and we build the
 * final term
 *)
let rec apply_stack info t = function
  | TOP -> t
  | APP (args,st) ->
    (* Note: should "theoretically" use a right-to-left version of map_of_list *)
      apply_stack info (mkApp(t,Array.map_of_list (cbv_norm_value info) args)) st
  | CASE (u,pms,ty,br,iv,ci,env,st) ->
    (* FIXME: Prevent this expansion by caching whether an inductive contains let-bindings *)
    let (_, (ty,r), _, _, br) = Inductive.expand_case info.env (ci, u, pms, ty, iv, mkProp, br) in
    let ty =
      let (_, mip) = Inductive.lookup_mind_specif info.env ci.ci_ind in
      Term.decompose_lambda_n_decls (mip.Declarations.mind_nrealdecls + 1) ty
    in
    let mk_br c n = Term.decompose_lambda_n_decls n c in
    let br = Array.map2 mk_br br ci.ci_cstr_ndecls in
    let aux = if info.strong then cbv_norm_term info else apply_env in
    let map_ctx (nas, c) =
      let open Context.Rel.Declaration in
      let fold decl e = match decl with
      | LocalAssum _ -> subs_lift e
      | LocalDef (_, b, _) ->
        let b = cbv_stack_term info TOP e b in
        (* The let-binding persists, so we have to shift *)
        subs_shft (1, subs_cons b e)
      in
      let env = List.fold_right fold nas env in
      let nas = Array.of_list (List.rev_map get_annot nas) in
      (nas, aux env c)
    in
      apply_stack info
        (mkCase (ci, u, Array.map (aux env) pms, (map_ctx ty,r), iv, t,
                    Array.map map_ctx br))
        st
  | PROJ (p, r, st) ->
       apply_stack info (mkProj (p, r, t)) st

(* performs the reduction on a constr, and returns a constr *)
and cbv_norm_term info env t =
  (* reduction under binders *)
  cbv_norm_value info (cbv_stack_term info TOP env t)

(* reduction of a cbv_value to a constr *)
and cbv_norm_value info = function
  | VAL (n,t) -> lift n t
  | STACK (0,v,stk) ->
      apply_stack info (cbv_norm_value info v) stk
  | STACK (n,v,stk) ->
      lift n (apply_stack info (cbv_norm_value info v) stk)
  | PROD(na,t,u,env) ->
      mkProd (na,cbv_norm_term info env t,cbv_norm_term info (subs_lift env) u)
  | LETIN (na,b,t,c,env) ->
      let aux = if info.strong then cbv_norm_term info else apply_env in
      mkLetIn (na,cbv_norm_value info b,aux env t,aux (subs_lift env) c)
  | LAMBDA (n,ctxt,b,env) ->
      let nctxt =
        List.map_i (fun i (x,ty) ->
          (x,cbv_norm_term info (subs_liftn i env) ty)) 0 ctxt in
      let aux = if info.strong then cbv_norm_term info else apply_env in
      Term.compose_lam (List.rev nctxt) (aux (subs_liftn n env) b)
  | FIX ((lij,(names,lty,bds)),env,args) ->
      let aux = if info.strong then cbv_norm_term info else apply_env in
      mkApp
        (mkFix (lij,
                (names,
                 Array.map (aux env) lty,
                 Array.map (aux (subs_liftn (Array.length lty) env)) bds)),
         Array.map (cbv_norm_value info) args)
  | COFIX ((j,(names,lty,bds)),env,args) ->
      mkApp
        (mkCoFix (j,
                  (names,Array.map (cbv_norm_term info env) lty,
                   Array.map (cbv_norm_term info
                                (subs_liftn (Array.length lty) env)) bds)),
         Array.map (cbv_norm_value info) args)
  | CONSTRUCT (c,args) ->
      mkApp(mkConstructU c, Array.map (cbv_norm_value info) args)
  | PRIMITIVE(op,c,args) ->
      mkApp(mkConstU c,Array.map (cbv_norm_value info) args)
  | ARRAY (u,t,ty) ->
    let ty = cbv_norm_value info ty in
    let t, def = Parray.to_array t in
    let def = cbv_norm_value info def in
      mkArray(u, Array.map (cbv_norm_value info) t, def, ty)
  | SYMBOL { cst; stk; _ } -> apply_stack info (mkConstU cst) stk

(* with profiling *)
let cbv_norm infos constr =
  let constr = EConstr.Unsafe.to_constr constr in
  EConstr.of_constr (cbv_norm_term infos (subs_id 0) constr)

(* constant bodies are normalized at the first expansion *)
let create_cbv_infos reds ~strong env sigma =
  { tab = KeyTable.create 91; reds; env; sigma; strong }
