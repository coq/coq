(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Bruno Barras with Benjamin Werner's account to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Call-by-value machine moved to cbv.ml, Mar 01 *)
(* Additional tools for module subtyping by Jacek Chrzaszcz, Aug 2002 *)
(* Extension with closure optimization by Bruno Barras, Aug 2003 *)
(* Support for evar reduction by Bruno Barras, Feb 2009 *)
(* Miscellaneous other improvements by Bruno Barras, 1997-2009 *)

(* This file implements a lazy reduction for the Calculus of Inductive
   Constructions *)

open Util
open Pp
open Native
open Term
open Names
open Declarations
open Environ
open Esubst

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
  beta := 0; delta := 0; zeta := 0; evar := 0; iota := 0; evar := 0;
  prune := 0

let stop() =
  msgnl (str "[Reds: beta=" ++ int !beta ++ str" delta=" ++ int !delta ++
	 str" zeta=" ++ int !zeta ++ str" evar=" ++ int !evar ++
         str" iota=" ++ int !iota ++ str" prune=" ++ int !prune ++ str"]")

let incr_cnt red cnt =
  if red then begin
    if !stats then incr cnt;
    true
  end else
    false

let with_stats c =
  if !stats then begin
    reset();
    let r = Lazy.force c in
    stop();
    r
  end else
    Lazy.force c

let all_opaque = (Idpred.empty, Cpred.empty)
let all_transparent = (Idpred.full, Cpred.full)

module type RedFlagsSig = sig
  type reds
  type red_kind
  val fBETA : red_kind
  val fDELTA : red_kind
  val fIOTA : red_kind
  val fZETA : red_kind
  val fCONST : constant -> red_kind
  val fVAR : identifier -> red_kind
  val no_red : reds
  val red_add : reds -> red_kind -> reds
  val red_sub : reds -> red_kind -> reds
  val red_add_transparent : reds -> transparent_state -> reds
  val mkflags : red_kind list -> reds
  val red_set : reds -> red_kind -> bool
end

module RedFlags = (struct

  (* [r_const=(true,cl)] means all constants but those in [cl] *)
  (* [r_const=(false,cl)] means only those in [cl] *)
  (* [r_delta=true] just mean [r_const=(true,[])] *)

  type reds = {
    r_beta : bool;
    r_delta : bool;
    r_const : transparent_state;
    r_zeta : bool;
    r_iota : bool }

  type red_kind = BETA | DELTA | IOTA | ZETA
	      | CONST of constant | VAR of identifier
  let fBETA = BETA
  let fDELTA = DELTA
  let fIOTA = IOTA
  let fZETA = ZETA
  let fCONST kn  = CONST kn
  let fVAR id  = VAR id
  let no_red = {
    r_beta = false;
    r_delta = false;
    r_const = all_opaque;
    r_zeta = false;
    r_iota = false }

  let red_add red = function
    | BETA -> { red with r_beta = true }
    | DELTA -> { red with r_delta = true; r_const = all_transparent }
    | CONST kn ->
	let (l1,l2) = red.r_const in
	{ red with r_const = l1, Cpred.add kn l2 }
    | IOTA -> { red with r_iota = true }
    | ZETA -> { red with r_zeta = true }
    | VAR id ->
	let (l1,l2) = red.r_const in
	{ red with r_const = Idpred.add id l1, l2 }

  let red_sub red = function
    | BETA -> { red with r_beta = false }
    | DELTA -> { red with r_delta = false }
    | CONST kn ->
 	let (l1,l2) = red.r_const in
	{ red with r_const = l1, Cpred.remove kn l2 }
    | IOTA -> { red with r_iota = false }
    | ZETA -> { red with r_zeta = false }
    | VAR id ->
	let (l1,l2) = red.r_const in
	{ red with r_const = Idpred.remove id l1, l2 }

  let red_add_transparent red tr =
    { red with r_const = tr }

  let mkflags = List.fold_left red_add no_red

  let red_set red = function
    | BETA -> incr_cnt red.r_beta beta
    | CONST kn ->
	let (_,l) = red.r_const in
	let c = Cpred.mem kn l in
	incr_cnt c delta
    | VAR id -> (* En attendant d'avoir des kn pour les Var *)
	let (l,_) = red.r_const in
	let c = Idpred.mem id l in
	incr_cnt c delta
    | ZETA -> incr_cnt red.r_zeta zeta
    | IOTA -> incr_cnt red.r_iota iota
    | DELTA -> (* Used for Rel/Var defined in context *)
	incr_cnt red.r_delta delta

end : RedFlagsSig)

open RedFlags

let betadeltaiota = mkflags [fBETA;fDELTA;fZETA;fIOTA]
let betadeltaiotanolet = mkflags [fBETA;fDELTA;fIOTA]
let betaiota = mkflags [fBETA;fIOTA]
let beta = mkflags [fBETA]
let betaiotazeta = mkflags [fBETA;fIOTA;fZETA]

(* Removing fZETA for finer behaviour would break many developments *)
let unfold_side_flags = [fBETA;fIOTA;fZETA]
let unfold_side_red = mkflags [fBETA;fIOTA;fZETA]
let unfold_red kn =
  let flag = match kn with
    | EvalVarRef id -> fVAR id
    | EvalConstRef kn -> fCONST kn in
  mkflags (flag::unfold_side_flags)

(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
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

type table_key = id_key

let eq_table_key = Names.eq_id_key

type 'a infos = {
  i_flags : reds;
  i_repr : 'a infos -> constr -> 'a;
  i_env : env;
  i_sigma : existential -> constr option;
  i_rels : int * (int * constr) list;
  i_vars : (identifier * constr) list;
  i_tab : (table_key, 'a constant_def) Hashtbl.t
  }

let env_info info = info.i_env

let info_flags info = info.i_flags

let ref_value_cache info ref =
  try  
    Hashtbl.find info.i_tab ref
  with Not_found ->
    let v =
      match ref with
      | RelKey n ->
	  let (s,l) = info.i_rels in 
	  (try Def (info.i_repr info (lift n (List.assoc (s-n) l)))
	  with Not_found -> Opaque None)
      | VarKey id -> 
	  (try Def (info.i_repr info (List.assoc id info.i_vars))
	  with Not_found -> Opaque None)
      | ConstKey cst -> 
	  begin match constant_value1 info.i_env cst with
	  | Def t -> Def (info.i_repr info (force t))
	  | Opaque _ -> Opaque None
	  | Primitive op -> Primitive op
	  end
    in 
    Hashtbl.add info.i_tab ref v; v

let evar_value info ev =
  info.i_sigma ev

let defined_vars flags env =
(*  if red_local_const (snd flags) then*)
    Sign.fold_named_context
      (fun (id,b,_) e ->
	 match b with
	   | None -> e
	   | Some body -> (id, body)::e)
       (named_context env) ~init:[]
(*  else []*)

let defined_rels flags env =
(*  if red_local_const (snd flags) then*)
  Sign.fold_rel_context
      (fun (id,b,t) (i,subs) ->
	 match b with
	   | None -> (i+1, subs)
	   | Some body -> (i+1, (i,body) :: subs))
      (rel_context env) ~init:(0,[])
(*  else (0,[])*)

let create mk_cl flgs env evars =
  { i_flags = flgs;
    i_repr = mk_cl;
    i_env = env;
    i_sigma = evars;
    i_rels = defined_rels flgs env;
    i_vars = defined_vars flgs env;
    i_tab = Hashtbl.create 17 }


(**********************************************************************)
(* Lazy reduction: the one used in kernel operations                  *)

(* type of shared terms. fconstr and frterm are mutually recursive.
 * Clone of the constr structure, but completely mutable, and
 * annotated with reduction state (reducible or not).
 *  - FLIFT is a delayed shift; allows sharing between 2 lifted copies
 *    of a given term.
 *  - FCLOS is a delayed substitution applied to a constr
 *  - FLOCKED is used to erase the content of a reference that must
 *    be updated. This is to allow the garbage collector to work
 *    before the term is computed.
 *)

(* Norm means the term is fully normalized and cannot create a redex
     when substituted
   Cstr means the term is in head normal form and that it can
     create a redex when substituted (i.e. constructor, fix, lambda)
   Whnf means we reached the head normal form and that it cannot
     create a redex when substituted
   Red is used for terms that might be reduced
*)
type red_state = Norm | Cstr | Whnf | Red

let neutr = function
  | (Whnf|Norm) -> Whnf
  | (Red|Cstr) -> Red

type fconstr = {
  mutable norm: red_state;
  mutable term: fterm }

and fterm =
  | FRel of int
  | FAtom of constr (* Metas and Sorts *)
  | FCast of fconstr * cast_kind * fconstr
  | FFlex of table_key
  | FInd of inductive
  | FConstruct of constructor
  | FApp of fconstr * fconstr array
  | FFix of fixpoint * fconstr subs
  | FCoFix of cofixpoint * fconstr subs
  | FCases of case_info * fconstr * fconstr * fconstr array
  | FLambda of int * (name * constr) list * constr * fconstr subs
  | FProd of name * fconstr * fconstr
  | FLetIn of name * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential * fconstr subs
  | FNativeInt of Uint31.t
  | FNativeArr of fconstr * fconstr Parray.t
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FLOCKED

let fterm_of v = v.term
let set_norm v = v.norm <- Norm
let is_val v = v.norm = Norm

let mk_atom c = {norm=Norm;term=FAtom c}

(* Could issue a warning if no is still Red, pointing out that we loose
   sharing. *)
let update v1 (no,t) =
  if !share then
    (v1.norm <- no;
     v1.term <- t;
     v1)
  else {norm=no;term=t}

(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)
type 'a next_native_args = (Native.arg_kind * 'a) list

type stack_member =
  | Zapp of fconstr array
  | Zcase of case_info * fconstr * fconstr array
  | Zfix of fconstr * stack
  | Znative of Native.op * constant * fconstr list * fconstr next_native_args
       (* operator, constr def, reduced arguments rev, next arguments *) 
  | Zshift of int
  | Zupdate of fconstr

and stack = stack_member list

let empty_stack = []
let append_stack v s =
  if Array.length v = 0 then s else
  match s with
  | Zapp l :: s -> Zapp (Array.append v l) :: s
  | _ -> Zapp v :: s

(* Collapse the shifts in the stack *)
let zshift n s =
  match (n,s) with
      (0,_) -> s
    | (_,Zshift(k)::s) -> Zshift(n+k)::s
    | _ -> Zshift(n)::s

let rec stack_args_size = function
  | Zapp v :: s -> Array.length v + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | Zupdate(_)::s -> stack_args_size s
  | _ -> 0

(* When used as an argument stack (only Zapp can appear) *)
let rec decomp_stack = function
  | Zapp v :: s ->
      (match Array.length v with
          0 -> decomp_stack s
        | 1 -> Some (v.(0), s)
        | _ ->
            Some (v.(0), (Zapp (Array.sub v 1 (Array.length v - 1)) :: s)))
  | _ -> None
let array_of_stack s =
  let rec stackrec = function
  | [] -> []
  | Zapp args :: s -> args :: (stackrec s)
  | _ -> assert false
  in Array.concat (stackrec s)
let rec stack_assign s p c = match s with
  | Zapp args :: s ->
      let q = Array.length args in
      if p >= q then
	Zapp args :: stack_assign s (p-q) c
      else
        (let nargs = Array.copy args in
         nargs.(p) <- c;
         Zapp nargs :: s)
  | _ -> s
let rec stack_tail p s =
  if p = 0 then s else
    match s with
      | Zapp args :: s ->
	  let q = Array.length args in
	  if p >= q then stack_tail (p-q) s
	  else Zapp (Array.sub args p (q-p)) :: s
      | _ -> failwith "stack_tail"
let rec stack_nth s p = match s with
  | Zapp args :: s ->
      let q = Array.length args in
      if p >= q then stack_nth s (p-q)
      else args.(p)
  | _ -> raise Not_found

(* Lifting. Preserves sharing (useful only for cell with norm=Red).
   lft_fconstr always create a new cell, while lift_fconstr avoids it
   when the lift is 0. *)
let rec lft_fconstr n ft =
  match ft.term with
    | (FInd _|FConstruct _|FFlex(ConstKey _|VarKey _)|FNativeInt _) -> ft
    | FRel i -> {norm=Norm;term=FRel(i+n)}
    | FLambda(k,tys,f,e) -> {norm=Cstr; term=FLambda(k,tys,f,subs_shft(n,e))}
    | FFix(fx,e) -> {norm=Cstr; term=FFix(fx,subs_shft(n,e))}
    | FCoFix(cfx,e) -> {norm=Cstr; term=FCoFix(cfx,subs_shft(n,e))}
    | FLIFT(k,m) -> lft_fconstr (n+k) m
    | FLOCKED -> assert false
    | _ -> {norm=ft.norm; term=FLIFT(n,ft)}
let lift_fconstr k f =
  if k=0 then f else lft_fconstr k f
let lift_fconstr_vect k v =
  if k=0 then v else Array.map (fun f -> lft_fconstr k f) v

let clos_rel e i =
  match expand_rel i e with
    | Inl(n,mt) -> lift_fconstr n mt
    | Inr(k,None) -> {norm=Norm; term= FRel k}
    | Inr(k,Some p) ->
        lift_fconstr (k-p) {norm=Red;term=FFlex(RelKey p)}

(* since the head may be reducible, we might introduce lifts of 0 *)
let compact_stack head stk =
  let rec strip_rec depth = function
    | Zshift(k)::s -> strip_rec (depth+k) s
    | Zupdate(m)::s ->
        (* Be sure to create a new cell otherwise sharing would be
           lost by the update operation *)
        let h' = lft_fconstr depth head in
        let _ = update m (h'.norm,h'.term) in
        strip_rec depth s
    | stk -> zshift depth stk in
  strip_rec 0 stk

(* Put an update mark in the stack, only if needed *)
let zupdate m s =
  if !share & m.norm = Red
  then
    let s' = compact_stack m s in
    let _ = m.term <- FLOCKED in
    Zupdate(m)::s'
  else s

(* Closure optimization: *)
let rec compact_constr (lg, subs as s) c k =
  match kind_of_term c with
      Rel i ->
        if i < k then c,s else
          (try mkRel (k + lg - list_index (i-k+1) subs), (lg,subs)
          with Not_found -> mkRel (k+lg), (lg+1, (i-k+1)::subs))
    | (Sort _|Var _|Meta _|Ind _|Const _|Construct _ | NativeInt _) -> c,s
    | Evar(ev,v) ->
        let (v',s) = compact_vect s v k in
        if v==v' then c,s else mkEvar(ev,v'),s
    | Cast(a,ck,b) ->
        let (a',s) = compact_constr s a k in
        let (b',s) = compact_constr s b k in
        if a==a' && b==b' then c,s else mkCast(a', ck, b'), s
    | App(f,v) ->
        let (f',s) = compact_constr s f k in
        let (v',s) = compact_vect s v k in
        if f==f' && v==v' then c,s else mkApp(f',v'), s
    | Lambda(n,a,b) ->
        let (a',s) = compact_constr s a k in
        let (b',s) = compact_constr s b (k+1) in
        if a==a' && b==b' then c,s else mkLambda(n,a',b'), s
    | Prod(n,a,b) ->
        let (a',s) = compact_constr s a k in
        let (b',s) = compact_constr s b (k+1) in
        if a==a' && b==b' then c,s else mkProd(n,a',b'), s
    | LetIn(n,a,ty,b) ->
        let (a',s) = compact_constr s a k in
        let (ty',s) = compact_constr s ty k in
        let (b',s) = compact_constr s b (k+1) in
        if a==a' && ty==ty' && b==b' then c,s else mkLetIn(n,a',ty',b'), s
    | Fix(fi,(na,ty,bd)) ->
        let (ty',s) = compact_vect s ty k in
        let (bd',s) = compact_vect s bd (k+Array.length ty) in
        if ty==ty' && bd==bd' then c,s else mkFix(fi,(na,ty',bd')), s
    | CoFix(i,(na,ty,bd)) ->
        let (ty',s) = compact_vect s ty k in
        let (bd',s) = compact_vect s bd (k+Array.length ty) in
        if ty==ty' && bd==bd' then c,s else mkCoFix(i,(na,ty',bd')), s
    | Case(ci,p,a,br) ->
        let (p',s) = compact_constr s p k in
        let (a',s) = compact_constr s a k in
        let (br',s) = compact_vect s br k in
        if p==p' && a==a' && br==br' then c,s else mkCase(ci,p',a',br'),s
    | NativeArr(t,p) ->
	let (t',s) = compact_constr s t k in
	let (p',s) = compact_vect s p k in
	if t == t' && p == p' then c,s else mkArray(t',p'),s

and compact_vect s v k = compact_v [] s v k (Array.length v - 1)
and compact_v acc s v k i =
  if i < 0 then
    let v' = Array.of_list acc in
    if array_for_all2 (==) v v' then v,s else v',s
  else
    let (a',s') = compact_constr s v.(i) k in
    compact_v (a'::acc) s' v k (i-1)

(* Computes the minimal environment of a closure.
   Idea: if the subs is not identity, the term will have to be
   reallocated entirely (to propagate the substitution). So,
   computing the set of free variables does not change the
   complexity. *)
let optimise_closure env c =
  if is_subs_id env then (env,c) else
    let (c',(_,s)) = compact_constr (0,[]) c 1 in
    let env' =
      Array.map (fun i -> clos_rel env i) (Array.of_list s) in
    (subs_cons (env', ESID 0),c')

let mk_lambda env t =
  let (env,t) = optimise_closure env t in
  let (rvars,t') = decompose_lam t in
  FLambda(List.length rvars, List.rev rvars, t', env)

let destFLambda clos_fun t =
  match t.term with
      FLambda(_,[(na,ty)],b,e) -> (na,clos_fun e ty,clos_fun (subs_lift e) b)
    | FLambda(n,(na,ty)::tys,b,e) ->
        (na,clos_fun e ty,{norm=Cstr;term=FLambda(n-1,tys,b,subs_lift e)})
    | _ -> assert false
	(* t must be a FLambda and binding list cannot be empty *)

(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let mk_clos e t =
  match kind_of_term t with
    | Rel i -> clos_rel e i
    | Var x -> { norm = Red; term = FFlex (VarKey x) }
    | Const c -> { norm = Red; term = FFlex (ConstKey c) }
    | Meta _ | Sort _ ->  { norm = Norm; term = FAtom t }
    | Ind kn -> { norm = Norm; term = FInd kn }
    | Construct kn -> { norm = Cstr; term = FConstruct kn }
    | NativeInt i -> {norm = Cstr; term = FNativeInt i}
    | CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _
    | NativeArr _ ->
        {norm = Red; term = FCLOS(t,e)}

let mk_clos_vect env v = Array.map (mk_clos env) v

(* Translate the head constructor of t from constr to fconstr. This
   function is parameterized by the function to apply on the direct
   subterms.
   Could be used insted of mk_clos. *)
let mk_clos_deep clos_fun env t =
  match kind_of_term t with
    | (Rel _|Ind _|Const _|Construct _|Var _|Meta _|Sort _|NativeInt _) ->
        mk_clos env t
    | Cast (a,k,b) ->
        { norm = Red;
          term = FCast (clos_fun env a, k, clos_fun env b)}
    | App (f,v) ->
        { norm = Red;
	  term = FApp (clos_fun env f, Array.map (clos_fun env) v) }
    | Case (ci,p,c,v) ->
        { norm = Red;
	  term = FCases (ci, clos_fun env p, clos_fun env c,
			 Array.map (clos_fun env) v) }
    | Fix fx ->
        { norm = Cstr; term = FFix (fx, env) }
    | CoFix cfx ->
        { norm = Cstr; term = FCoFix(cfx,env) }
    | Lambda _ ->
        { norm = Cstr; term = mk_lambda env t }
    | Prod (n,t,c)   ->
        { norm = Whnf;
	  term = FProd (n, clos_fun env t, clos_fun (subs_lift env) c) }
    | LetIn (n,b,t,c) ->
        { norm = Red;
	  term = FLetIn (n, clos_fun env b, clos_fun env t, c, env) }
    | Evar ev ->
	{ norm = Red; term = FEvar(ev,env) }
    | NativeArr(t,p) ->
	let len = Array.length p - 1 in
	{ norm = Cstr;
	  term = 
	  FNativeArr(clos_fun env t, 
		     Parray.init (Uint31.of_int len)
		       (fun i -> clos_fun env p.(i)) 
		       (clos_fun env p.(len))) 
	}

(* A better mk_clos? *)
let mk_clos2 = mk_clos_deep mk_clos

(* The inverse of mk_clos_deep: move back to constr *)
let rec to_constr constr_fun lfts v =
  match v.term with
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (RelKey p) -> mkRel (reloc_rel p lfts)
    | FFlex (VarKey x) -> mkVar x
    | FAtom c -> exliftn lfts c
    | FCast (a,k,b) ->
        mkCast (constr_fun lfts a, k, constr_fun lfts b)
    | FFlex (ConstKey op) -> mkConst op
    | FInd op -> mkInd op
    | FConstruct op -> mkConstruct op
    | FCases (ci,p,c,ve) ->
	mkCase (ci, constr_fun lfts p,
                constr_fun lfts c,
		Array.map (constr_fun lfts) ve)
    | FFix ((op,(lna,tys,bds)),e) ->
        let n = Array.length bds in
        let ftys = Array.map (mk_clos e) tys in
        let fbds = Array.map (mk_clos (subs_liftn n e)) bds in
	let lfts' = el_liftn n lfts in
	mkFix (op, (lna, Array.map (constr_fun lfts) ftys,
		         Array.map (constr_fun lfts') fbds))
    | FCoFix ((op,(lna,tys,bds)),e) ->
        let n = Array.length bds in
        let ftys = Array.map (mk_clos e) tys in
        let fbds = Array.map (mk_clos (subs_liftn n e)) bds in
	let lfts' = el_liftn (Array.length bds) lfts in
	mkCoFix (op, (lna, Array.map (constr_fun lfts) ftys,
		           Array.map (constr_fun lfts') fbds))
    | FApp (f,ve) ->
	mkApp (constr_fun lfts f,
	       Array.map (constr_fun lfts) ve)
    | FLambda _ ->
        let (na,ty,bd) = destFLambda mk_clos2 v in
	mkLambda (na, constr_fun lfts ty,
	              constr_fun (el_lift lfts) bd)
    | FProd (n,t,c)   ->
	mkProd (n, constr_fun lfts t,
	           constr_fun (el_lift lfts) c)
    | FLetIn (n,b,t,f,e) ->
        let fc = mk_clos2 (subs_lift e) f in
	mkLetIn (n, constr_fun lfts b,
	            constr_fun lfts t,
	            constr_fun (el_lift lfts) fc)
    | FEvar ((ev,args),env) ->
        mkEvar(ev,Array.map (fun a -> constr_fun lfts (mk_clos2 env a)) args)
    | FLIFT (k,a) -> to_constr constr_fun (el_shft k lfts) a
    | FCLOS (t,env) ->
        let fr = mk_clos2 env t in
        let unfv = update v (fr.norm,fr.term) in
        to_constr constr_fun lfts unfv
    | FLOCKED -> assert false (*mkVar(id_of_string"_LOCK_")*)
    | FNativeInt i -> mkInt i
    | FNativeArr(t, p) ->
	let init i = constr_fun lfts (Parray.get p (Uint31.of_int i)) in
	mkArray(constr_fun lfts t,
		Array.init (Uint31.to_int (Parray.length p) + 1) init)


(* This function defines the correspondance between constr and
   fconstr. When we find a closure whose substitution is the identity,
   then we directly return the constr to avoid possibly huge
   reallocation. *)
let term_of_fconstr =
  let rec term_of_fconstr_lift lfts v =
    match v.term with
      | FCLOS(t,env) when is_subs_id env & is_lift_id lfts -> t
      | FLambda(_,tys,f,e) when is_subs_id e & is_lift_id lfts ->
          compose_lam (List.rev tys) f
      | FFix(fx,e) when is_subs_id e & is_lift_id lfts -> mkFix fx
      | FCoFix(cfx,e) when is_subs_id e & is_lift_id lfts -> mkCoFix cfx
      | _ -> to_constr term_of_fconstr_lift lfts v in
  term_of_fconstr_lift ELID



(* fstrong applies unfreeze_fun recursively on the (freeze) term and
 * yields a term.  Assumes that the unfreeze_fun never returns a
 * FCLOS term.
let rec fstrong unfreeze_fun lfts v =
  to_constr (fstrong unfreeze_fun) lfts (unfreeze_fun v)
*)

let rec zip m stk =
  match stk with
    | [] -> m
    | Zapp args :: s -> zip {norm=neutr m.norm; term=FApp(m, args)} s
    | Zcase(ci,p,br)::s ->
        let t = FCases(ci, p, m, br) in
        zip {norm=neutr m.norm; term=t} s
    | Zfix(fx,par)::s ->
        zip fx (par @ append_stack [|m|] s)
    | Zshift(n)::s ->
        zip (lift_fconstr n m) s
    | Zupdate(rf)::s ->
        zip (update rf (m.norm,m.term)) s
    | Znative(op,kn,rargs,kargs)::s ->
	let args = List.rev_append rargs (m::List.map snd kargs) in
	let f = {norm = Red;term = FFlex (ConstKey kn)} in
                (* Check this *)
	zip {norm=Red; term = FApp (f, Array.of_list args)} s

let fapp_stack (m,stk) = zip m stk

(*********************************************************************)

(* The assertions in the functions below are granted because they are
   called only when m is a constructor, a cofix
   (strip_update_shift_app), a fix (get_nth_arg) or an abstraction
   (strip_update_shift, through get_arg). *)

(* optimised for the case where there are no shifts... *)
let strip_update_shift_app head stk =
  assert (head.norm <> Red);
  let rec strip_rec rstk h depth = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) (depth+k) s
    | (Zapp args :: s) ->
        strip_rec (Zapp args :: rstk)
          {norm=h.norm;term=FApp(h,args)} depth s
    | Zupdate(m)::s ->
        strip_rec rstk (update m (h.norm,h.term)) depth s
    | stk -> (depth,List.rev rstk, stk) in
  strip_rec [] head 0 stk


let get_nth_arg head n stk =
  assert (head.norm <> Red);
  let rec strip_rec rstk h n = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) n s
    | Zapp args::s' ->
        let q = Array.length args in
        if n >= q
        then
          strip_rec (Zapp args::rstk) {norm=h.norm;term=FApp(h,args)} (n-q) s'
        else
          let bef = Array.sub args 0 n in
          let aft = Array.sub args (n+1) (q-n-1) in
          let stk' =
            List.rev (if n = 0 then rstk else (Zapp bef :: rstk)) in
          (Some (stk', args.(n)), append_stack aft s')
    | Zupdate(m)::s ->
        strip_rec rstk (update m (h.norm,h.term)) n s
    | s -> (None, List.rev rstk @ s) in
  strip_rec [] head n stk

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let rec get_args n tys f e stk =
  match stk with
      Zupdate r :: s ->
        let _hd = update r (Cstr,FLambda(n,tys,f,e)) in
        get_args n tys f e s
    | Zshift k :: s ->
        get_args n tys f (subs_shft (k,e)) s
    | Zapp l :: s ->
        let na = Array.length l in
        if n == na then (Inl (subs_cons(l,e)),s)
        else if n < na then (* more arguments *)
          let args = Array.sub l 0 n in
          let eargs = Array.sub l n (na-n) in
          (Inl (subs_cons(args,e)), Zapp eargs :: s)
        else (* more lambdas *)
          let etys = list_skipn na tys in
          get_args (n-na) etys f (subs_cons(l,e)) s
    | _ -> (Inr {norm=Cstr;term=FLambda(n,tys,f,e)}, stk)

(* Eta expansion: add a reference to implicit surrounding lambda at end of stack *)
let rec eta_expand_stack = function
  | (Zapp _ | Zfix _ | Zcase _ | Zshift _ | Zupdate _ | Znative _ as e) :: s ->
      e :: eta_expand_stack s
  | [] ->
      [Zshift 1; Zapp [|{norm=Norm; term= FRel 1}|]]

(* Get the arguments of a native operator *)
let rec skip_native_args rargs nargs =
  match nargs with
  | (kd, a) :: nargs' ->
      if kd = Native.Kwhnf then rargs, nargs 
      else skip_native_args (a::rargs) nargs'
  | [] -> rargs, []

let get_native_args op kn stk =
  let kargs = Native.op_kind op in
  let rec get_args rnargs kargs args =
    match kargs, args with
    | kd::kargs, a::args -> get_args ((kd,a)::rnargs) kargs args
    | _, _ -> rnargs, kargs, args in
  let rec strip_rec rnargs h depth kargs = function
    | Zshift k :: s ->
	strip_rec (List.map (fun (kd,f) -> kd,lift_fconstr k f) rnargs)
	  (lift_fconstr k h) (depth+k) kargs s
    | Zapp args :: s' ->
	begin match get_args rnargs kargs (Array.to_list args) with
	| rnargs, [], [] -> 
	    (skip_native_args [] (List.rev rnargs), s')
	| rnargs, [], eargs -> 
	    (skip_native_args [] (List.rev rnargs),
	     Zapp (Array.of_list eargs) :: s')
	| rnargs, kargs, _ -> 
	    strip_rec rnargs {norm = h.norm;term=FApp(h, args)} depth kargs s'
	end
    | Zupdate(m) :: s ->
	strip_rec rnargs (update m (h.norm, h.term)) depth  kargs s
    | _ -> assert false
  in strip_rec [] {norm = Red;term = FFlex(ConstKey kn)} 0 kargs stk

let get_native_args1 op kn stk =
  match get_native_args op kn stk with
  | ((rargs, (kd,a):: nargs), stk) ->
      assert (kd = Native.Kwhnf);
      (rargs, a, nargs, stk)
  | _ -> assert false
	
let check_native_args op stk =
  let (nparams, nargs) = Native.arity op in
  let rargs = stack_args_size stk in
  (nparams + nargs) <= rargs
(*
  let rec aux n = function
    | (Zshift _ | Zupdate _) :: s -> aux n s
    | Zapp args :: s ->
	let nargs = Array.length args in
	if n <= nargs then true
	else aux (n - nargs) s
    | _ -> false in
  aux (nparams + nargs) stk *)
    

(* Iota reduction: extract the arguments to be passed to the Case
   branches *)
let rec reloc_rargs_rec depth stk =
  match stk with
      Zapp args :: s ->
        Zapp (lift_fconstr_vect depth args) :: reloc_rargs_rec depth s
    | Zshift(k)::s -> if k=depth then s else reloc_rargs_rec (depth-k) s
    | _ -> stk

let reloc_rargs depth stk =
  if depth = 0 then stk else reloc_rargs_rec depth stk

let rec drop_parameters depth n argstk =
  match argstk with
      Zapp args::s ->
        let q = Array.length args in
        if n > q then drop_parameters depth (n-q) s
        else if n = q then reloc_rargs depth s
        else
          let aft = Array.sub args n (q-n) in
          reloc_rargs depth (append_stack aft s)
    | Zshift(k)::s -> drop_parameters (depth-k) n s
    | [] -> (* we know that n < stack_args_size(argstk) (if well-typed term) *)
	if n=0 then []
	else anomaly
	  "ill-typed term: found a match on a partially applied constructor"
    | _ -> assert false
	(* strip_update_shift_app only produces Zapp and Zshift items *)

(* Iota reduction: expansion of a fixpoint.
 * Given a fixpoint and a substitution, returns the corresponding
 * fixpoint body, and the substitution in which it should be
 * evaluated: its first variables are the fixpoint bodies
 *
 * FCLOS(fix Fi {F0 := T0 .. Fn-1 := Tn-1}, S)
 *    -> (S. FCLOS(F0,S) . ... . FCLOS(Fn-1,S), Ti)
 *)
(* does not deal with FLIFT *)
let contract_fix_vect fix =
  let (thisbody, make_body, env, nfix) =
    match fix with
      | FFix (((reci,i),(_,_,bds as rdcl)),env) ->
          (bds.(i),
	   (fun j -> { norm = Cstr; term = FFix (((reci,j),rdcl),env) }),
	   env, Array.length bds)
      | FCoFix ((i,(_,_,bds as rdcl)),env) ->
          (bds.(i),
	   (fun j -> { norm = Cstr; term = FCoFix ((j,rdcl),env) }),
	   env, Array.length bds)
      | _ -> assert false
  in
  (subs_cons(Array.init nfix make_body, env), thisbody)


(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
let rec knh m stk =
  match m.term with
    | FLIFT(k,a) -> knh a (zshift k stk)
    | FCLOS(t,e) -> knht e t (zupdate m stk)
    | FLOCKED -> assert false
    | FApp(a,b) -> knh a (append_stack b (zupdate m stk))
    | FCases(ci,p,t,br) -> knh t (Zcase(ci,p,br)::zupdate m stk)
    | FFix(((ri,n),(_,_,_)),_) ->
        (match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FCast(t,_,_) -> knh t stk
(* cases where knh stops *)
    | (FFlex _|FLetIn _|FConstruct _|FEvar _|
       FCoFix _|FLambda _|FRel _|FAtom _|FInd _|FProd _|
       FNativeInt _|FNativeArr _) ->
        (m, stk)

(* The same for pure terms *)
and knht e t stk =
  match kind_of_term t with
    | App(a,b) ->
        knht e a (append_stack (mk_clos_vect e b) stk)
    | Case(ci,p,t,br) ->
        knht e t (Zcase(ci, mk_clos e p, mk_clos_vect e br)::stk)
    | Fix _ -> knh (mk_clos2 e t) stk
    | Cast(a,_,_) -> knht e a stk
    | Rel n -> knh (clos_rel e n) stk
    | (Lambda _|Prod _|Construct _|CoFix _|Ind _|
       LetIn _|Const _|Var _|Evar _|Meta _|Sort _|
       NativeInt _ | NativeArr _) ->
        (mk_clos2 e t, stk)


(************************************************************************)
(* Reduction of Native operators                                        *)

module FNativeEntries =
  struct 

    type elem = fconstr 
    type args = fconstr array
    module Parray = Parray	
	  
    let get = Array.get

    let get_int e =
      match e.term with
      | FNativeInt i -> i
      | _ -> raise Not_found

    let get_parray e =
      match e.term with
      | FNativeArr(t,p) -> (t,p)
      | _ -> raise Not_found

    let dummy = {norm = Whnf; term = FRel 0}

    let current_retro = ref Pre_env.empty_retroknowledge
    let defined_int = ref false
    let fint = ref dummy 

    let init_int retro =
      match retro.Pre_env.retro_int31 with
      | Some (cte, _) ->
	  defined_int := true;
	  fint := { norm = Whnf; term = FFlex (ConstKey cte) }
      | None -> defined_int := false

    let defined_bool = ref false
    let ftrue = ref dummy
    let ffalse = ref dummy

    let init_bool retro =
      match retro.Pre_env.retro_bool with
      | Some (ct,cf) ->
	  defined_bool := true;
	  ftrue := { norm = Whnf; term = FConstruct ct };
	  ffalse := { norm = Whnf; term = FConstruct cf }
      | None -> defined_bool :=false

    let defined_carry = ref false
    let fC0 = ref dummy
    let fC1 = ref dummy

    let init_carry retro =
      match retro.Pre_env.retro_carry with
      | Some(c0,c1) ->
	  defined_carry := true;
          fC0 := { norm = Whnf; term = FConstruct c0 };
	  fC1 := { norm = Whnf; term = FConstruct c1 } 
      | None -> defined_carry := false

    let defined_pair = ref false
    let fPair = ref dummy
	
    let init_pair retro = 
      match retro.Pre_env.retro_pair with
      | Some c ->
	  defined_pair := true;
          fPair := { norm = Whnf; term = FConstruct c }
      | None -> defined_pair := false

    let defined_cmp = ref false
    let fEq = ref dummy  
    let fLt = ref dummy
    let fGt = ref dummy

    let init_cmp retro =
      match retro.Pre_env.retro_cmp with
      | Some (cEq, cLt, cGt) ->
	  defined_cmp := true;
	  fEq := { norm = Whnf; term = FConstruct cEq };
	  fLt := { norm = Whnf; term = FConstruct cLt };
	  fGt := { norm = Whnf; term = FConstruct cGt }
      | None -> defined_cmp := false

    let defined_array = ref false

    let init_array retro =
      defined_array := retro.Pre_env.retro_array <> None

    let init env = 
      current_retro := retroknowledge env;
      init_int !current_retro;
      init_bool !current_retro;
      init_carry !current_retro;
      init_pair !current_retro;
      init_cmp !current_retro;
      init_array !current_retro

	  
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

    let mkInt env i = 
      check_int env;
      { norm = Whnf; term = FNativeInt i }

    let mkBool env b = 
      check_bool env;
      if b then !ftrue else !ffalse
       
    let mkCarry env b e =
      check_carry env;
      {norm = Whnf;
       term = FApp ((if b then !fC1 else !fC0),[|!fint;e|])}

    let mkPair env e1 e2 =
      check_pair env;
      { norm = Whnf; term = FApp(!fPair, [|!fint;!fint;e1;e2|]) }

    let mkLt env = 
      check_cmp env;
      !fLt
 
    let mkEq env = 
      check_cmp env;
      !fEq

    let mkGt env = 
      check_cmp env;
      !fGt

    let mkArray env t p =
      check_array env;
      { norm = Whnf; term = FNativeArr(t, p)}

    let mkClos id t body s =
      { norm = Whnf; 
	term = FLambda(1,[id,t],body, Esubst.CONS(s,Esubst.ESID 0)) }

  end

module FredNative = RedNative(FNativeEntries)

(* Computes a weak head normal form from the result of knh. *)
let rec knr info m stk =
  match m.term with
  | FLambda(n,tys,f,e) when red_set info.i_flags fBETA ->
      (match get_args n tys f e stk with
          Inl e', s -> knit info e' f s
        | Inr lam, s -> (lam,s))
  | FFlex(ConstKey kn) when red_set info.i_flags (fCONST kn) ->
      (match ref_value_cache info (ConstKey kn) with
      | Def v -> kni info v stk
      | Primitive op when check_native_args op stk ->
	  let rargs, a, nargs, stk = get_native_args1 op kn stk in
	  kni info a (Znative(op,kn,rargs,nargs)::stk)
      | _ -> set_norm m; (m,stk))
  | FFlex(VarKey id) when red_set info.i_flags (fVAR id) ->
      (match ref_value_cache info (VarKey id) with
      | Def v -> kni info v stk
      | _  -> (set_norm m; (m,stk)))
  | FFlex(RelKey k) when red_set info.i_flags fDELTA ->
      (match ref_value_cache info (RelKey k) with
      | Def v -> kni info v stk
      | _ -> (set_norm m; (m,stk)))
  | FConstruct(ind,c) when red_set info.i_flags fIOTA ->
      (match strip_update_shift_app m stk with
          (depth, args, Zcase(ci,_,br)::s) ->
            assert (ci.ci_npar>=0);
            let rargs = drop_parameters depth ci.ci_npar args in
            kni info br.(c-1) (rargs@s)
        | (_, cargs, Zfix(fx,par)::s) ->
            let rarg = fapp_stack(m,cargs) in
            let stk' = par @ append_stack [|rarg|] s in
            let (fxe,fxbd) = contract_fix_vect fx.term in
            knit info fxe fxbd stk'
        | (_,args,s) -> (m,args@s))
  | (FNativeInt _ | FNativeArr _) ->
      (match strip_update_shift_app m stk with
      | (_, _, Znative(op,kn,rargs,nargs)::s) ->
	  let (rargs, nargs) = skip_native_args (m::rargs) nargs in
	  begin match nargs with
	  | [] -> 
	      let args = Array.of_list (List.rev rargs) in
	      begin match FredNative.red_op info.i_env op (mkConst kn) args with
	      | Some m -> kni info m s 
	      | None -> 
		  let f = {norm = Whnf; term = FFlex (ConstKey kn)} in
		  let m = {norm = Whnf; term = FApp(f,args)} in
		  (m,s)
	      end
	  | (kd,a)::nargs -> 
	      assert (kd = Native.Kwhnf);
	      kni info a (Znative(op,kn,rargs,nargs)::s)
	  end
      | (_, _, s) -> (m, s))
  | FCoFix _ when red_set info.i_flags fIOTA ->
      (match strip_update_shift_app m stk with
          (_, args, ((Zcase _::_) as stk')) ->
            let (fxe,fxbd) = contract_fix_vect m.term in
            knit info fxe fxbd (args@stk')
        | (_,args,s) -> (m,args@s))
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knit info (subs_cons([|v|],e)) bd stk
  | FEvar(ev,env) ->
      (match evar_value info ev with
          Some c -> knit info env c stk
        | None -> (m,stk))
  | _ -> (m,stk)

(* Computes the weak head normal form of a term *)
and kni info m stk =
  let (hm,s) = knh m stk in
  knr info hm s
and knit info e t stk =
  let (ht,s) = knht e t stk in
  knr info ht s

let kh info v stk = fapp_stack(kni info v stk)

(************************************************************************)

let rec zip_term zfun m stk =
  match stk with
    | [] -> m
    | Zapp args :: s ->
        zip_term zfun (mkApp(m, Array.map zfun args)) s
    | Zcase(ci,p,br)::s ->
        let t = mkCase(ci, zfun p, m, Array.map zfun br) in
        zip_term zfun t s
    | Zfix(fx,par)::s ->
        let h = mkApp(zip_term zfun (zfun fx) par,[|m|]) in
        zip_term zfun h s
    | Zshift(n)::s ->
        zip_term zfun (lift n m) s
    | Zupdate(rf)::s ->
        zip_term zfun m s
    | Znative(_,kn,rargs, kargs)::s ->
	let kargs = List.map (fun (_,a) -> zfun a) kargs in
	let args = 
	  List.fold_left (fun args a -> zfun a ::args) (m::kargs) rargs in 
	let h = mkApp (mkConst kn, Array.of_list args) in
	zip_term zfun h s

(* Computes the strong normal form of a term.
   1- Calls kni
   2- tries to rebuild the term. If a closure still has to be computed,
      calls itself recursively. *)
let rec kl info m =
  if is_val m then (incr prune; term_of_fconstr m)
  else
    let (nm,s) = kni info m [] in
    let _ = fapp_stack(nm,s) in (* to unlock Zupdates! *)
    zip_term (kl info) (norm_head info nm) s

(* no redex: go up for atoms and already normalized terms, go down
   otherwise. *)
and norm_head info m =
  if is_val m then (incr prune; term_of_fconstr m) else
    match m.term with
      | FLambda(n,tys,f,e) ->
          let (e',rvtys) =
            List.fold_left (fun (e,ctxt) (na,ty) ->
              (subs_lift e, (na,kl info (mk_clos e ty))::ctxt))
              (e,[]) tys in
          let bd = kl info (mk_clos e' f) in
          List.fold_left (fun b (na,ty) -> mkLambda(na,ty,b)) bd rvtys
      | FLetIn(na,a,b,f,e) ->
          let c = mk_clos (subs_lift e) f in
          mkLetIn(na, kl info a, kl info b, kl info c)
      | FProd(na,dom,rng) ->
          mkProd(na, kl info dom, kl info rng)
      | FCoFix((n,(na,tys,bds)),e) ->
          let ftys = Array.map (mk_clos e) tys in
          let fbds =
            Array.map (mk_clos (subs_liftn (Array.length na) e)) bds in
          mkCoFix(n,(na, Array.map (kl info) ftys, Array.map (kl info) fbds))
      | FFix((n,(na,tys,bds)),e) ->
          let ftys = Array.map (mk_clos e) tys in
          let fbds =
            Array.map (mk_clos (subs_liftn (Array.length na) e)) bds in
          mkFix(n,(na, Array.map (kl info) ftys, Array.map (kl info) fbds))
      | FEvar((i,args),env) ->
          mkEvar(i, Array.map (fun a -> kl info (mk_clos env a)) args)
      | t -> term_of_fconstr m

(* Initialization and then normalization *)

(* weak reduction *)
let whd_val info v =
  with_stats (lazy (term_of_fconstr (kh info v [])))

(* strong reduction *)
let norm_val info v =
  with_stats (lazy (kl info v))

let inject = mk_clos (ESID 0)

let whd_stack infos m stk =
  let k = kni infos m stk in
  let _ = fapp_stack k in (* to unlock Zupdates! *)
  k

(* cache of constants: the body is computed only when needed. *)
type clos_infos = fconstr infos

let create_clos_infos ?(evars=fun _ -> None) flgs env =
  create (fun _ -> inject) flgs env evars

let unfold_reference = ref_value_cache
